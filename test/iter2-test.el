;;; -*- lexical-binding: t -*-

;;; Copyright (C) 2017 Paul Pogonyshev

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see http://www.gnu.org/licenses.


(require 'iter2)
(require 'ert)
(require 'cl-macs)


;; Evaluating iterator lambdas at runtime simplifies testing changes
;; immediately.
(cl-defmacro iter2--runtime-eval (name value &rest body)
  (declare (debug (symbolp form body))
           (indent 2))
  `(let* ((,name (eval ,(macroexp-quote value) t)))
     ,@body))

(cl-defmacro iter2--test (function &key args returned returned-expression expected end-value max-length body)
  (cl-assert (not (and returned returned-expression)))
  (let ((description (format-message "iterator %S" (if args `(apply ,function ,args) `(funcall ,function)))))
    ;; Don't create symbols for variables in a private macro: this lets
    ;; `returned-expression' have access to everything.
    `(let ((it     (apply ,function ,args))
           ,@(when returned `((to-return (cons nil ,returned))))
           value
           result
           (length 0)
           terminated-normally
           end-value)
       (condition-case error
           (catch 'too-long
             (while t
               (setq value (iter-next it ,(if returned `(pop to-return) returned-expression)))
               (when (> (setq length (1+ length)) ,(or max-length (+ (length expected) 5)))
                 (throw 'too-long nil))
               (push value result)
               ,@body))
         (iter-end-of-sequence (setq terminated-normally t
                                     end-value           (cdr error))))
       (setq result (nreverse result))
       (should (equal (progn ,(format-message "%s yielded values" description) result) ,expected))
       (when terminated-normally
         (should (equal (progn ,(format-message "%s end value" description) end-value) ,end-value)))
       nil)))

;; To make sure that converted functions don't become too inefficient
;; due to code changes, we also assert number of lambdas they result
;; in.  "Wrong" number of lambdas, of course, doesn't necessarily
;; imply that conversion produced a wrong result, but in such a case
;; it should be manually verified and either the code or the test
;; (expected number of lambdas) fixed.
(defmacro iter2--assert-num-lambdas (form expected)
  `(should (= (iter2--count-lambas ,form) ,expected)))

(defun iter2--count-lambas (form)
  (pcase (macroexpand-1 form)
    (`(function (lambda ,_arglist . ,body))
     (1+ (apply #'+ (mapcar #'iter2--count-lambas body))))
    (`(closure ,_bindings ,_arglist . ,body)
     (1+ (apply #'+ (mapcar #'iter2--count-lambas body))))
    (`(,(or 'let 'let*) ,bindings . ,body)
     (+ (apply #'+ (mapcar (lambda (binding) (iter2--count-lambas (car-safe (cdr-safe binding)))) bindings))
        (apply #'+ (mapcar #'iter2--count-lambas body))))
    (`(cond . ,conditions)
     (apply #'+ (mapcar (lambda (condition) (apply #'+ (mapcar #'iter2--count-lambas condition))) conditions)))
    (`(condition-case ,_var ,body-form . ,handlers)
     (+ (iter2--count-lambas body-form)
        (apply #'+ (mapcar (lambda (handler) (apply #'+ (mapcar #'iter2--count-lambas (cdr-safe handler)))) handlers))))
    (`(,_name . ,rest)                       ; remaining special forms can be handled like this too
     (apply #'+ (mapcar #'iter2--count-lambas rest)))
    (_ 0)))

(defmacro iter2--test-no-yields (name &rest body)
  (declare (indent defun))
  `(ert-deftest ,name ()
     (iter2--runtime-eval fn (iter2-lambda () ,@body)
       (iter2--test fn :end-value (progn ,@body)))))

(defmacro iter2--let-wrapper (bindings &rest body)
  `(let (,@bindings) ,@body))

(defmacro iter2--let-wrapper-2 (bindings &rest body)
  `(iter2--let-wrapper (,@bindings) ,@body))


(defvar iter2--test-global-var-1 nil)
(defvar iter2--test-global-var-2 nil)
(defvar iter2--test-global-var-3 nil)

(defun iter2--test-get-global-var-1 ()
  iter2--test-global-var-1)


;; No-yields tests are mostly adapted from `generator' package.  For
;; `iter2' they are less important, though, as conversion for forms
;; that yield is significantly different.

(iter2--test-no-yields iter2-no-yields-simple-1 (progn 1 2 3))
(iter2--test-no-yields iter2-no-yields-empty-progn (progn))
(iter2--test-no-yields iter2-no-yields-inline-not-progn (inline 1 2 3))
(iter2--test-no-yields iter2-no-yields-prog1-a (prog1 1 2 3))
(iter2--test-no-yields iter2-no-yields-prog1-b (prog1 1))
(iter2--test-no-yields iter2-no-yields-prog1-c (prog2 1 2 3))
(iter2--test-no-yields iter2-no-yields-quote (progn 'hello))
(iter2--test-no-yields iter2-no-yields-function (progn #'hello))

(iter2--test-no-yields iter2-no-yields-and-fail (and 1 nil 2))
(iter2--test-no-yields iter2-no-yields-and-succeed (and 1 2 3))
(iter2--test-no-yields iter2-no-yields-and-empty (and))

(iter2--test-no-yields iter2-no-yields-or-fallthrough (or nil 1 2))
(iter2--test-no-yields iter2-no-yields-or-alltrue (or 1 2 3))
(iter2--test-no-yields iter2-no-yields-or-empty (or))

(iter2--test-no-yields iter2-no-yields-let* (let* ((i 10)) i))
(iter2--test-no-yields iter2-no-yields-let*-shadow-empty (let* ((i 10)) (let (i) i)))
(iter2--test-no-yields iter2-no-yields-let (let ((i 10)) i))
(iter2--test-no-yields iter2-no-yields-let-shadow-empty (let ((i 10)) (let (i) i)))
(iter2--test-no-yields iter2-no-yields-let-novars (let nil 42))
(iter2--test-no-yields iter2-no-yields-let*-novars (let* nil 42))

(iter2--test-no-yields iter2-no-yields-let-parallel
  (let ((a 5) (b 6)) (let ((a b) (b a)) (list a b))))

(iter2--test-no-yields iter2-no-yields-let*-parallel
  (let* ((a 5) (b 6)) (let* ((a b) (b a)) (list a b))))

(iter2--test-no-yields iter2-no-yields-while-dynamic
  (setq iter2--test-global-var-1 0)
  (while (< iter2--test-global-var-1 10)
    (setf iter2--test-global-var-1 (+ iter2--test-global-var-1 1)))
  iter2--test-global-var-1)

(iter2--test-no-yields iter2-no-yields-while-lexical
  (let* ((i 0) (j 10))
    (while (< i 10)
      (setf i (+ i 1))
      (setf j (+ j (* i 10))))
    j))

(iter2--test-no-yields iter2-no-yields-while-incf
  (let* ((i 0) (j 10))
    (while (< i 10)
      (cl-incf i)
      (setf j (+ j (* i 10))))
    j))

(iter2--test-no-yields iter2-no-yields-dynbind
  (setf iter2--test-global-var-1 0)
  (let* ((iter2--test-global-var-1 5))
    (iter2--test-get-global-var-1)))

(iter2--test-no-yields iter2-no-yields-nested-application
  (+ (+ 3 5) 1))

(iter2--test-no-yields iter2-no-yields-unwind-protect
  (setf iter2--test-global-var-1 0)
  (unwind-protect
      (setf iter2--test-global-var-1 1)
    (setf iter2--test-global-var-1 2))
  iter2--test-global-var-1)

(iter2--test-no-yields iter2-no-yields-catch-unused
  (catch 'mytag 42))

(iter2--test-no-yields iter2-no-yields-catch-thrown
  (1+ (catch 'mytag
        (throw 'mytag (+ 2 2)))))

(iter2--test-no-yields iter2-no-yields-loop
  (cl-loop for x from 1 to 10 collect x))

(iter2--test-no-yields iter2-no-yields-loop-backquote
  `(a b ,(cl-loop for x from 1 to 10 collect x) -1))

(iter2--test-no-yields iter2-no-yields-if-branch-a
  (if t 'abc))

(iter2--test-no-yields iter2-no-yields-if-branch-b
  (if t 'abc 'def))

(iter2--test-no-yields iter2-no-yields-if-condition-fail
  (if nil 'abc 'def))

(iter2--test-no-yields iter2-no-yields-cond-empty
  (cond))

(iter2--test-no-yields iter2-no-yields-cond-atomi
  (cond (42)))

(iter2--test-no-yields iter2-no-yields-cond-complex
  (cond (nil 22) ((1+ 1) 42) (t 'bad)))

(iter2--test-no-yields iter2-no-yields-condition-case
  (condition-case
      condvar
      (signal 'arith-error 'test-data)
    (arith-error condvar)))

(iter2--test-no-yields iter2-no-yields-condition-case-no-error
  (condition-case
      condvar
      42
    (arith-error condvar)))


(ert-deftest iter2-progn-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (iter-yield 1) (iter-yield 2))
    (iter2--test fn :expected '(1 2))
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-prog1-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (prog1 x (iter-yield 1)))
    (iter2--test fn :args '(0) :expected '(1) :end-value 0)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-prog1-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (prog1 (iter-yield 1) (iter-yield 2)))
    (iter2--test fn                  :expected '(1 2))
    (iter2--test fn :returned '(3 4) :expected '(1 2) :end-value 3)
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-and-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (and 3 (iter-yield 1)))
    (iter2--test fn                :expected '(1))
    (iter2--test fn :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 3)))

(ert-deftest iter2-and-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (and 3 (iter-yield 1) 4))
    (iter2--test fn                :expected '(1))
    (iter2--test fn :returned '(t) :expected '(1) :end-value 4)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-and-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (and (iter-yield 1) (iter-yield 2)))
    (iter2--test fn                  :expected '(1))
    (iter2--test fn :returned '(t)   :expected '(1 2) :end-value nil)
    (iter2--test fn :returned '(t t) :expected '(1 2) :end-value t)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-or-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (or 3 (iter-yield 1)))
    (iter2--test fn :expected '() :end-value 3)
    (iter2--assert-num-lambdas fn 3)))

(ert-deftest iter2-or-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (or nil (iter-yield 1) 4))
    (iter2--test fn                :expected '(1) :end-value 4)
    (iter2--test fn :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-or-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (or (iter-yield 1) (iter-yield 2)))
    (iter2--test fn                    :expected '(1 2))
    (iter2--test fn :returned '(t)     :expected '(1)   :end-value t)
    (iter2--test fn :returned '(nil 3) :expected '(1 2) :end-value 3)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-if-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (if x (iter-yield 1) (iter-yield 2)))
    (iter2--test fn :args '(nil)                :expected '(2))
    (iter2--test fn :args '(t)                  :expected '(1))
    (iter2--test fn :args '(t)   :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 3)))

(ert-deftest iter2-if-2 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (if x (iter-yield 1) (iter-yield 2)) 3)
    (iter2--test fn :args '(nil)                :expected '(2) :end-value 3)
    (iter2--test fn :args '(t)                  :expected '(1) :end-value 3)
    (iter2--test fn :args '(t)   :returned '(t) :expected '(1) :end-value 3)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-if-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (iter-yield 1) 2 3))
    (iter2--test fn :returned '(nil) :expected '(1) :end-value 3)
    (iter2--test fn :returned '(t)   :expected '(1) :end-value 2)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-if-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (iter-yield 1) 2 3) 4)
    (iter2--test fn :returned '(nil) :expected '(1) :end-value 4)
    (iter2--test fn :returned '(t)   :expected '(1) :end-value 4)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-if-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    (iter2--test fn                  :expected '(1 3))
    (iter2--test fn :returned '(t)   :expected '(1 2))
    (iter2--test fn :returned '(t t) :expected '(1 2) :end-value t)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-while-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (while t (iter-yield t)))
    (iter2--test fn :expected '(t t t t t) :max-length 5)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-while-2 ()
  (iter2--runtime-eval fn (iter2-lambda (n) (while (iter-yield (setq n (1+ n)))))
    (iter2--test fn :args '(0)                        :expected '(1))
    (iter2--test fn :args '(0) :returned '(t t t)     :expected '(1 2 3 4))
    (iter2--test fn :args '(0) :returned-expression t :expected '(1 2 3 4 5) :max-length 5)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-while-3 ()
  (iter2--runtime-eval fn (iter2-lambda (n) (while (iter-yield (setq n (1+ n))) (iter-yield 'inside)))
    (iter2--test fn :args '(0)                            :expected '(1))
    (iter2--test fn :args '(0) :returned '(t t t)         :expected '(1 inside 2 inside 3))
    (iter2--test fn :args '(0) :returned '(t t t t)       :expected '(1 inside 2 inside 3))
    (iter2--test fn :args '(0) :returned '(t nil t nil t) :expected '(1 inside 2 inside 3 inside 4))
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-while-4 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (while x (setq x (iter-yield x))))
    (iter2--test fn :args '(nil)                                       :expected '())
    (iter2--test fn :args '(t)                                         :expected '(t))
    (iter2--test fn :args '(1)  :returned '(2 3)                       :expected '(1 2 3))
    (iter2--test fn :args '(0)  :returned-expression (1+ (or value 0)) :expected '(0 1 2 3 4) :max-length 5)
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-while-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (while (or (iter-yield 1) (iter-yield 2)) (iter-yield 3)))
    (iter2--test fn                      :expected '(1 2))
    (iter2--test fn :returned '(t)       :expected '(1 3 1 2))
    (iter2--test fn :returned '(nil t)   :expected '(1 2 3 1 2))
    (iter2--test fn :returned '(nil t t) :expected '(1 2 3 1 2))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-while-6 ()
  (iter2--runtime-eval fn (iter2-lambda () (while (> (+ (iter-yield 1) (iter-yield 2)) 0) (iter-yield 3)))
    (iter2--test fn :returned '(0 0)          :expected '(1 2))
    (iter2--test fn :returned '(1 -2)         :expected '(1 2))
    (iter2--test fn :returned '(1 1 nil 0 0)  :expected '(1 2 3 1 2))
    (iter2--test fn :returned '(-1 2 nil 0 0) :expected '(1 2 3 1 2))
    (iter2--assert-num-lambdas fn 8)))

(ert-deftest iter2-let-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (let ((x 1)) (iter-yield x)))
    (iter2--test fn :expected '(1))
    (iter2--assert-num-lambdas fn 3)))

(ert-deftest iter2-let-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (let ((x (iter-yield 1))) (iter-yield x)))
    (iter2--test fn                  :expected '(1 nil))
    (iter2--test fn :returned '(t)   :expected '(1 t))
    (iter2--test fn :returned '(t 5) :expected '(1 t) :end-value 5)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-let-3 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (let ((x (iter-yield x)) (y x) (x 0) (x (iter-yield x))) (list x y)))
    (iter2--test fn :args '(1)                  :expected '(1 1) :end-value '(nil 1))
    (iter2--test fn :args '(1) :returned '(2 3) :expected '(1 1) :end-value '(3 1))
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-let-4 ()
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let ((a (iter-yield c)) (b (iter-yield b)) (c (iter-yield a))) (list a b c)))
    (iter2--test fn :args '(1 2 3) :returned '(4 5 6) :expected '(3 2 1) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-let*-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (let* ((x 1)) (iter-yield x)))
    (iter2--test fn :expected '(1))
    (iter2--assert-num-lambdas fn 3)))

(ert-deftest iter2-let*-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (let* ((x (iter-yield 1))) (iter-yield x)))
    (iter2--test fn                  :expected '(1 nil))
    (iter2--test fn :returned '(t)   :expected '(1 t))
    (iter2--test fn :returned '(t 5) :expected '(1 t) :end-value 5)
    (iter2--assert-num-lambdas fn 4)))

(ert-deftest iter2-let*-3 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (let* ((x (iter-yield x)) (y x) (x 0) (x (iter-yield x))) (list x y)))
    (iter2--test fn :args '(1)                  :expected '(1 0) :end-value '(nil nil))
    (iter2--test fn :args '(1) :returned '(2 3) :expected '(1 0) :end-value '(3 2))
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-let*-4 ()
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let* ((a (iter-yield c)) (b (iter-yield b)) (c (iter-yield a))) (list a b c)))
    (iter2--test fn :args '(1 2 3) :returned '(4 5 6) :expected '(3 2 4) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-let-with-globals-1 ()
  (let ((iter2--test-global-var-1 0))
    (iter2--runtime-eval fn (iter2-lambda () (let ((iter2--test-global-var-1 1)) (iter-yield iter2--test-global-var-1) (iter-yield iter2--test-global-var-1)))
      (iter2--test fn :expected '(1 1)
                   :body ((should (= iter2--test-global-var-1 0))))
      (iter2--assert-num-lambdas fn 6))))

(ert-deftest iter2-let-with-globals-2 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda () (let ((iter2--test-global-var-1 (iter-yield 1))
                                                   (x (iter-yield 2))
                                                   (iter2--test-global-var-2 (iter-yield 3)))
                                               (iter-yield (list (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                                 iter2--test-global-var-1 x iter2--test-global-var-2))))
      (iter2--test fn                        :expected '(1 2 3 (nil nil nil) (nil nil nil nil))
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :returned '(1 2 3 4 5) :expected '(1 2 3 (1 2 3) (4 1 2 3)) :end-value 5
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 10))))

(ert-deftest iter2-let-with-globals-3 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda (x) (let ((iter2--test-global-var-1 x)
                                                    (x (iter-yield 1))
                                                    (iter2--test-global-var-2 x))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))))
      (iter2--test fn :args '(1)                    :expected '(1 (1 nil 1) (1 nil 1))
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :args '(1) :returned '(2 3 4) :expected '(1 (1 2 1) (1 2 1)) :end-value 4
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 7))))

(ert-deftest iter2-let*-with-globals-1 ()
  (let ((iter2--test-global-var-1 0))
    (iter2--runtime-eval fn (iter2-lambda () (let* ((iter2--test-global-var-1 1)) (iter-yield iter2--test-global-var-1) (iter-yield iter2--test-global-var-1)))
      (iter2--test fn :expected '(1 1)
                   :body ((should (= iter2--test-global-var-1 0))))
      (iter2--assert-num-lambdas fn 7))))

(ert-deftest iter2-let*-with-globals-2 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda () (let* ((iter2--test-global-var-1 (iter-yield 1))
                                                    (x (iter-yield 2))
                                                    (iter2--test-global-var-2 (iter-yield 3)))
                                               (iter-yield (list (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                                 iter2--test-global-var-1 x iter2--test-global-var-2))))
      (iter2--test fn                        :expected '(1 2 3 (nil nil nil) (nil nil nil nil))
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :returned '(1 2 3 4 5) :expected '(1 2 3 (1 2 3) (4 1 2 3)) :end-value 5
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 13))))

(ert-deftest iter2-let*-with-globals-3 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda (x) (let* ((iter2--test-global-var-1 x)
                                                     (x (iter-yield 1))
                                                     (iter2--test-global-var-2 x))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))))
      (iter2--test fn :args '(1)                    :expected '(1 (1 nil nil) (1 nil nil))
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :args '(1) :returned '(2 3 4) :expected '(1 (1 2 2) (1 2 2)) :end-value 4
                   :body ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 10))))

(ert-deftest iter2-unwind-protect-1 ()
  (iter2--runtime-eval fn (iter2-lambda (a) (or (catch 'x (unwind-protect (throw 'x (iter-yield 1)) (setq a (1+ a)))) a))
    (iter2--test fn :args '(1)                :expected '(1) :end-value 2)
    (iter2--test fn :args '(1) :returned '(0) :expected '(1) :end-value 0)
    (iter2--assert-num-lambdas fn 11)))

(ert-deftest iter2-unwind-protect-2 ()
  (iter2--runtime-eval fn (iter2-lambda (a) (+ (catch 'x (unwind-protect (or (iter-yield 1) (when (iter-yield 2) (throw 'x (iter-yield 3))) 4) (setq a (1+ a)))) a))
    (iter2--test fn :args '(1)                      :expected '(1 2)   :end-value 6)
    (iter2--test fn :args '(1) :returned '(nil t 8) :expected '(1 2 3) :end-value 10)
    (iter2--test fn :args '(1) :returned '(5)       :expected '(1)     :end-value 7)
    (iter2--assert-num-lambdas fn 14)))

(ert-deftest iter2-unwind-protect-close-1 ()
  (iter2--runtime-eval fn (iter2-lambda (done) (unwind-protect (iter-yield 1) (funcall done)))
    (let* (done
           (it (funcall fn (lambda () (setq done t)))))
      ;; Closing before `unwind-protect' is even reached.
      (should (not done))
      (iter-close it)
      (should (not done)))
    (let* (done
           (it (funcall fn (lambda () (setq done t)))))
      ;; Letting unwind-forms run normally.
      (should (not done))
      (should (equal (iter-next it) 1))
      (should (not done))
      ;; `should-error' won't catch `iter-end-of-sequence'.
      (should (equal (condition-case error (cons nil (iter-next it 3)) (iter-end-of-sequence error))
                     '(iter-end-of-sequence . 3)))
      (should done))
    (let* (done
           (it (funcall fn (lambda () (setq done t)))))
      ;; Running unwind-forms manually by closing the iterator early.
      (should (not done))
      (should (equal (iter-next it) 1))
      (should (not done))
      (iter-close it)
      (should done))
    (iter2--assert-num-lambdas fn 7)))

(ert-deftest iter2-condition-case-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case _ (error "oh") (foo (iter-yield 1) (iter-yield 2)) (error (iter-yield 3) (iter-yield 4))))
    (iter2--test fn :expected '(3 4))
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-condition-case-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case err (when (iter-yield 1) (signal (iter-yield 2) (iter-yield 3)))
                                             (file-error (iter-yield (cdr err))) (arith-error (iter-yield 4) (iter-yield 5))))
    (iter2--test fn                                  :expected '(1))
    (iter2--test fn :returned '(t file-error t 6)    :expected '(1 2 3 t)   :end-value 6)
    (iter2--test fn :returned '(t arith-error t 7 8) :expected '(1 2 3 4 5) :end-value 8)
    (iter2--assert-num-lambdas fn 9)))

(ert-deftest iter2-catch-1 ()
  (iter2--runtime-eval fn (iter2-lambda (a b) (catch 'x (throw 'x (iter-yield a)) b))
    (iter2--test fn :args '(1 2) :expected '(1))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-catch-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch 'x (iter-yield 1) (when (iter-yield 2) (throw 'x (iter-yield 3))) (iter-yield 4)))
    (iter2--test fn                      :expected '(1 2 4))
    (iter2--test fn :returned '(5 6 7)   :expected '(1 2 3) :end-value 7)
    (iter2--test fn :returned '(t nil t) :expected '(1 2 4) :end-value t)
    (iter2--assert-num-lambdas fn 9)))

(ert-deftest iter2-catch-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch (or (iter-yield 1) 'x) (catch (or (iter-yield 2) 'y) (throw (or (iter-yield 3) 'x) (iter-yield 4)) 5) 6))
    (iter2--test fn                      :expected '(1 2 3 4))
    (iter2--test fn :returned '(x y y 0) :expected '(1 2 3 4) :end-value 6)
    (iter2--test fn :returned '(y x y 0) :expected '(1 2 3 4) :end-value 0)
    (should (= (catch 'z (iter2--test fn :returned '(a b z 0) :expected '(1 2 3 4))) 0))
    (iter2--assert-num-lambdas fn 15)))

(ert-deftest iter2-save-excursion-1 ()
  (iter2--runtime-eval fn (iter2-lambda ()
                            (save-excursion
                              (while (let ((x (iter-yield nil))) (when x (insert (prin1-to-string x)) t)))
                              (buffer-substring (point-min) (point-max))))
    (with-temp-buffer
      (iter2--test fn                        :expected '(nil)             :end-value ""
                   :body ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--test fn :returned '(1)         :expected '(nil nil)         :end-value "1"
                   :body ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--test fn :returned '(1 2)       :expected '(nil nil nil)     :end-value "12"
                   :body ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--test fn :returned '(1 2 (3 4)) :expected '(nil nil nil nil) :end-value "12(3 4)"
                   :body ((set-buffer (messages-buffer)))))
    (iter2--assert-num-lambdas fn 8)))

(ert-deftest iter2-save-current-buffer-1 ()
  (iter2--runtime-eval fn (iter2-lambda ()
                            (with-temp-buffer
                              (while (let ((x (iter-yield nil))) (when x (insert (prin1-to-string x)) t)))
                              (buffer-substring (point-min) (point-max))))
    (iter2--test fn                        :expected '(nil)             :end-value "")
    (iter2--test fn :returned '(1)         :expected '(nil nil)         :end-value "1")
    (iter2--test fn :returned '(1 2)       :expected '(nil nil nil)     :end-value "12")
    (iter2--test fn :returned '(1 2 (3 4)) :expected '(nil nil nil nil) :end-value "12(3 4)")
    (iter2--assert-num-lambdas fn 12)))

(ert-deftest iter2-save-restriction-1 ()
  (iter2--runtime-eval fn (iter2-lambda ()
                            (save-restriction
                              (widen)
                              (narrow-to-region 1 1)
                              (iter-yield (cons (point-min) (point-max)))
                              (iter-yield (cons (point-min) (point-max)))))
    (with-temp-buffer
      (insert "bla bla bla")
      (iter2--test fn :expected '((1 . 1) (1 . 1)) :body ((should (> (point-max) (point-min))))))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-calls-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    (iter2--test fn                    :expected '(1 2 3) :end-value '(nil nil nil))
    (iter2--test fn :returned '(4 5 6) :expected '(1 2 3) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-calls-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (vector (iter-yield 1)) (vector (iter-yield 2)) (vector (iter-yield 3))))
    (iter2--test fn                    :expected '(1 2 3) :end-value '([nil] [nil] [nil]))
    (iter2--test fn :returned '(4 5 6) :expected '(1 2 3) :end-value '([4] [5] [6]))
    (iter2--assert-num-lambdas fn 9)))

(ert-deftest iter2-yield-from-1 ()
  (iter2--runtime-eval fn1 (iter2-lambda (&rest values) (while values (iter-yield (pop values))))
    (iter2--runtime-eval fn2 (iter2-lambda (it) (iter-yield-from it))
      (iter2--test fn1 :args '(1 2 3)                   :expected '(1 2 3))
      (iter2--test fn2 :args (list (funcall fn1 1 2 3)) :expected '(1 2 3)))))

(ert-deftest iter2-metamacro-1 ()
  ;; Test with a macro that expands to (another) macro.
  (iter2--runtime-eval fn (iter2-lambda () (iter2--let-wrapper-2 ((x 1)) (iter-yield x)))
    (iter2--test fn :expected '(1))))
