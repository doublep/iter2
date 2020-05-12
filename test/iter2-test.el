;;; -*- lexical-binding: t -*-

;;; Copyright (C) 2017-2020 Paul Pogonyshev

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
    `(let* ((fn     ,function)
            (it     (apply fn ,args))
            ,@(when returned `((to-return (cons nil ,returned))))
            value
            result
            (length 0)
            terminated-normally
            end-value)
       (condition-case error
           (progn (condition-case error
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
                    (should (equal (progn ,(format-message "%s end value" description) end-value) ,end-value))))
         (error (princ "Pretty-printed failing function:\n")
                (pp fn)
                (signal (car error) (cdr error))))
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
  (let ((dont-test-for-warnings (eq (car body) :dont-test-for-warnings)))
    (when dont-test-for-warnings
      (pop body))
    `(ert-deftest ,name ()
       (iter2--runtime-eval fn (iter2-lambda () ,@body)
         (iter2--test fn :end-value (progn ,@body))
         ,@(unless dont-test-for-warnings
             `((iter2--test-byte-compiles-with-no-warnings fn)))))))

(defmacro iter2--with-test-tracing (&rest body)
  (declare (indent 0))
  `(let* (traced-messages
          (iter2-tracing-function (lambda (format-string &rest arguments)
                                    ;; Ignore exact invoked closures.
                                    (push (replace-regexp-in-string "iter2: invoking \\((.+)\\) with value " "..." (apply #'format format-string arguments) t t 1)
                                          traced-messages))))
     ,@body))


(defmacro iter2--let-wrapper (bindings &rest body)
  `(let (,@bindings) ,@body))

(defmacro iter2--let-wrapper-2 (bindings &rest body)
  `(iter2--let-wrapper (,@bindings) ,@body))

(defmacro iter2--save-match-data-wrapper (&rest body)
  `(save-match-data ,@body))

(defun iter2--test-byte-compiles-with-no-warnings (fn)
  (let* ((advice (lambda (format &rest arguments) (signal 'byte-compilation-warning (apply #'format-message format arguments)))))
    (advice-add 'byte-compile-warn :before advice)
    (unwind-protect
        (byte-compile fn)
      (advice-remove 'byte-compile-warn advice))))


(defun iter2--test-intern-symbols (value)
  (cond ((consp value)   (cons (iter2--test-intern-symbols (car value)) (iter2--test-intern-symbols (cdr value))))
        ((symbolp value) (intern (symbol-name value)))
        (t               value)))


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
(iter2--test-no-yields iter2-no-yields-let*-shadow-empty (let* ((i 10)) (ignore i) (let (i) i)))
(iter2--test-no-yields iter2-no-yields-let (let ((i 10)) i))
(iter2--test-no-yields iter2-no-yields-let-shadow-empty (let ((i 10)) (ignore i) (let (i) i)))
(iter2--test-no-yields iter2-no-yields-let-novars (let nil 42))
(iter2--test-no-yields iter2-no-yields-let*-novars (let* nil 42))

(iter2--test-no-yields iter2-no-yields-let-parallel
  (let ((a 5) (b 6)) (let ((a b) (b a)) (list a b))))

(iter2--test-no-yields iter2-no-yields-let*-parallel
  ;; Byte-compilation warnings about unused `a' is expected here, so
  ;; do not test for no warnings.
  :dont-test-for-warnings
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

(iter2--test-no-yields iter2-no-yields-cond-atomic
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

(iter2--test-no-yields iter2-no-yields-save-excursion
  (save-excursion
    10))

(iter2--test-no-yields iter2-no-yields-save-current-buffer
  (save-current-buffer
    10))

(iter2--test-no-yields iter2-no-yields-save-restriction
  (save-restriction
    10))

(iter2--test-no-yields iter2-no-yields-save-match-data
  (save-match-data
    10))


(ert-deftest iter2-progn-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (iter-yield 1) (iter-yield 2))
    (iter2--test fn :expected '(1 2))
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-prog1-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (prog1 x (iter-yield 1)))
    (iter2--test fn :args '(0) :expected '(1) :end-value 0)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-prog1-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (prog1 (iter-yield 1) (iter-yield 2)))
    (iter2--test fn                  :expected '(1 2))
    (iter2--test fn :returned '(3 4) :expected '(1 2) :end-value 3)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-prog1-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (prog1 (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    (iter2--test fn                    :expected '(1 2 3))
    (iter2--test fn :returned '(3 4 5) :expected '(1 2 3) :end-value 3)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-prog1-4 ()
  ;; `prog1' here is actually meaningless.
  (iter2--runtime-eval fn (iter2-lambda () (prog1 (iter-yield 1) (iter-yield 2)) (iter-yield 3))
    (iter2--test fn                    :expected '(1 2 3))
    (iter2--test fn :returned '(3 4 5) :expected '(1 2 3) :end-value 5)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-prog1-5 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (prog1 (iter-yield 1) (funcall x)))
    (let* (called-back
           (callback (lambda () (setq called-back t)))
           (it       (funcall fn callback)))
      (should (not called-back))
      (should (equal (iter-next it) 1))
      (should (not called-back))
      (should (equal (condition-case error (cons nil (iter-next it 2)) (iter-end-of-sequence error))
                     '(iter-end-of-sequence . 2)))
      (should called-back))
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-and-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (and 3 (iter-yield 1)))
    (iter2--test fn                :expected '(1))
    (iter2--test fn :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-and-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (and 3 (iter-yield 1) 4))
    (iter2--test fn                :expected '(1))
    (iter2--test fn :returned '(t) :expected '(1) :end-value 4)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-and-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (and (iter-yield 1) (iter-yield 2)))
    (iter2--test fn                  :expected '(1))
    (iter2--test fn :returned '(t)   :expected '(1 2) :end-value nil)
    (iter2--test fn :returned '(t t) :expected '(1 2) :end-value t)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-and-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (and (iter-yield 1) (iter-yield 2) (iter-yield (iter-yield 3))))
    (iter2--test fn                      :expected '(1))
    (iter2--test fn :returned '(t)       :expected '(1 2)     :end-value nil)
    (iter2--test fn :returned '(t t)     :expected '(1 2 3 nil))
    (iter2--test fn :returned '(4 5 6)   :expected '(1 2 3 6))
    (iter2--test fn :returned '(4 5 6 7) :expected '(1 2 3 6) :end-value 7)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-and-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (and (iter-yield 1)))
    (iter2--test fn                :expected '(1))
    (iter2--test fn :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-or-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (or 3 (iter-yield 1)))
    (iter2--test fn :expected '() :end-value 3)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-or-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (or nil (iter-yield 1) 4))
    (iter2--test fn                :expected '(1) :end-value 4)
    (iter2--test fn :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-or-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (or (iter-yield 1) (iter-yield 2)))
    (iter2--test fn                    :expected '(1 2))
    (iter2--test fn :returned '(t)     :expected '(1)   :end-value t)
    (iter2--test fn :returned '(nil 3) :expected '(1 2) :end-value 3)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-or-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (or (iter-yield 1) (iter-yield 2) (iter-yield (iter-yield 3))))
    (iter2--test fn                            :expected '(1 2 3 nil))
    (iter2--test fn :returned '(t)             :expected '(1)         :end-value t)
    (iter2--test fn :returned '(nil 4)         :expected '(1 2)       :end-value 4)
    (iter2--test fn :returned '(nil nil 5)     :expected '(1 2 3 5))
    (iter2--test fn :returned '(nil nil nil 6) :expected '(1 2 3 nil) :end-value 6)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-or-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (or (iter-yield 1)))
    (iter2--test fn                :expected '(1))
    (iter2--test fn :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-if-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (if x (iter-yield 1) (iter-yield 2)))
    (iter2--test fn :args '(nil)                :expected '(2))
    (iter2--test fn :args '(t)                  :expected '(1))
    (iter2--test fn :args '(t)   :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-if-2 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (if x (iter-yield 1) (iter-yield 2)) 3)
    (iter2--test fn :args '(nil)                :expected '(2) :end-value 3)
    (iter2--test fn :args '(t)                  :expected '(1) :end-value 3)
    (iter2--test fn :args '(t)   :returned '(t) :expected '(1) :end-value 3)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-if-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (iter-yield 1) 2 3))
    (iter2--test fn :returned '(nil) :expected '(1) :end-value 3)
    (iter2--test fn :returned '(t)   :expected '(1) :end-value 2)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

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
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-if-6 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (eq (iter-yield 1) 2) 3))
    (iter2--test fn                  :expected '(1))
    (iter2--test fn :returned '(2)   :expected '(1) :end-value 3)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-cond-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x y) (cond ((eq x y) (iter-yield 1)) ((equal x y) (iter-yield 2)) (t (iter-yield 3))))
    (iter2--test fn :args '(nil nil)                :expected '(1))
    (iter2--test fn :args '((nil) (nil))            :expected '(2))
    (iter2--test fn :args '(nil t)                  :expected '(3))
    (iter2--test fn :args '(nil nil) :returned '(t) :expected '(1) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-cond-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (cond ((eq (iter-yield 1) (iter-yield 2)) 1) ((eq (iter-yield 3) (iter-yield 4)) 2) (t 3)))
    (iter2--test fn                      :expected '(1 2)     :end-value 1)
    (iter2--test fn :returned '(1 2)     :expected '(1 2 3 4) :end-value 2)
    (iter2--test fn :returned '(1 2 3 4) :expected '(1 2 3 4) :end-value 3)
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-cond-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (cond ((iter-yield 1) (list (iter-yield 2) 3)) ((iter-yield 4) (list (iter-yield 5) 6))))
    (iter2--test fn                      :expected '(1 4))
    (iter2--test fn :returned '(t t)     :expected '(1 2)   :end-value '(t 3))
    (iter2--test fn :returned '(nil t t) :expected '(1 4 5) :end-value '(t 6))
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-cond-4 ()
  (iter2--runtime-eval fn (iter2-lambda (a b c d) (cond (a b) (c (- (iter-yield 1))) ((iter-yield 2) (list (iter-yield 3))) ((not (iter-yield 4)) d) (t 0)))
    (iter2--test fn :args '(nil nil nil nil) :returned '(nil nil) :expected '(2 4) :end-value nil)
    (iter2--test fn :args '(nil nil nil nil) :returned '(nil t)   :expected '(2 4) :end-value 0)
    (iter2--test fn :args '(t   10  nil nil)                      :expected '()    :end-value 10)
    (iter2--test fn :args '(nil nil t   nil) :returned '(2)       :expected '(1)   :end-value -2)
    (iter2--test fn :args '(nil nil nil 5)   :returned '(t 6)     :expected '(2 3) :end-value '(6))
    (iter2--test fn :args '(nil nil nil 5)   :returned '(nil nil) :expected '(2 4) :end-value 5)
    (iter2--test fn :args '(nil nil nil 5)   :returned '(nil 6)   :expected '(2 4) :end-value 0)
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-cond-5 ()
  (iter2--runtime-eval fn (iter2-lambda (x y z) (cond ((iter-yield 1)) (x) (y 4) (z (vector (iter-yield 2)))))
    (iter2--test fn :args '(1 2 3)       :returned '(t)     :expected '(1)   :end-value t)
    (iter2--test fn :args '(1 2 3)       :returned '(nil)   :expected '(1)   :end-value 1)
    (iter2--test fn :args '(nil 2 3)     :returned '(nil)   :expected '(1)   :end-value 4)
    (iter2--test fn :args '(nil nil 3)   :returned '(nil x) :expected '(1 2) :end-value [x])
    (iter2--test fn :args '(nil nil nil) :returned '(nil)   :expected '(1)   :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-while-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (while t (iter-yield t)))
    (iter2--test fn :expected '(t t t t t) :max-length 5)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-while-2 ()
  (iter2--runtime-eval fn (iter2-lambda (n) (while (iter-yield (setq n (1+ n)))))
    (iter2--test fn :args '(0)                        :expected '(1))
    (iter2--test fn :args '(0) :returned '(t t t)     :expected '(1 2 3 4))
    (iter2--test fn :args '(0) :returned-expression t :expected '(1 2 3 4 5) :max-length 5)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-while-3 ()
  (iter2--runtime-eval fn (iter2-lambda (n) (while (iter-yield (setq n (1+ n))) (iter-yield 'inside)))
    (iter2--test fn :args '(0)                            :expected '(1))
    (iter2--test fn :args '(0) :returned '(t t t)         :expected '(1 inside 2 inside 3))
    (iter2--test fn :args '(0) :returned '(t t t t)       :expected '(1 inside 2 inside 3))
    (iter2--test fn :args '(0) :returned '(t nil t nil t) :expected '(1 inside 2 inside 3 inside 4))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-while-4 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (while x (setq x (iter-yield x))))
    (iter2--test fn :args '(nil)                                       :expected '())
    (iter2--test fn :args '(t)                                         :expected '(t))
    (iter2--test fn :args '(1)  :returned '(2 3)                       :expected '(1 2 3))
    (iter2--test fn :args '(0)  :returned-expression (1+ (or value 0)) :expected '(0 1 2 3 4) :max-length 5)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-while-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (while (or (iter-yield 1) (iter-yield 2)) (iter-yield 3)))
    (iter2--test fn                      :expected '(1 2))
    (iter2--test fn :returned '(t)       :expected '(1 3 1 2))
    (iter2--test fn :returned '(nil t)   :expected '(1 2 3 1 2))
    (iter2--test fn :returned '(nil t t) :expected '(1 2 3 1 2))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-while-6 ()
  (iter2--runtime-eval fn (iter2-lambda () (while (> (+ (iter-yield 1) (iter-yield 2)) 0) (iter-yield 3)))
    (iter2--test fn :returned '(0 0)          :expected '(1 2))
    (iter2--test fn :returned '(1 -2)         :expected '(1 2))
    (iter2--test fn :returned '(1 1 nil 0 0)  :expected '(1 2 3 1 2))
    (iter2--test fn :returned '(-1 2 nil 0 0) :expected '(1 2 3 1 2))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-let-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (let ((x 1)) (iter-yield x)))
    (iter2--test fn :expected '(1))
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-let-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (let ((x (iter-yield 1))) (iter-yield x)))
    (iter2--test fn                  :expected '(1 nil))
    (iter2--test fn :returned '(t)   :expected '(1 t))
    (iter2--test fn :returned '(t 5) :expected '(1 t) :end-value 5)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-let-3 ()
  ;; Byte-compilation warning about unused `x' is expected here, so do
  ;; not test for no warnings.
  (iter2--runtime-eval fn (iter2-lambda (x) (let ((x (iter-yield x)) (y x) (x 0) (x (iter-yield x))) (list x y)))
    (iter2--test fn :args '(1)                  :expected '(1 1) :end-value '(nil 1))
    (iter2--test fn :args '(1) :returned '(2 3) :expected '(1 1) :end-value '(3 1))
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-let-4 ()
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let ((a (iter-yield c)) (b (iter-yield b)) (c (iter-yield a))) (list a b c)))
    (iter2--test fn :args '(1 2 3) :returned '(4 5 6) :expected '(3 2 1) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-let-error-1 ()
  (should-error (eval '(iter2-lambda () (let ((x 1 2)))) t)))

(ert-deftest iter2-let*-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (let* ((x 1)) (iter-yield x)))
    (iter2--test fn :expected '(1))
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-let*-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (let* ((x (iter-yield 1))) (iter-yield x)))
    (iter2--test fn                  :expected '(1 nil))
    (iter2--test fn :returned '(t)   :expected '(1 t))
    (iter2--test fn :returned '(t 5) :expected '(1 t) :end-value 5)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-let*-3 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (let* ((x (iter-yield x)) (y x) (x 0) (x (iter-yield x))) (list x y)))
    (iter2--test fn :args '(1)                  :expected '(1 0) :end-value '(nil nil))
    (iter2--test fn :args '(1) :returned '(2 3) :expected '(1 0) :end-value '(3 2))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-let*-4 ()
  ;; Byte-compilation warnings about unused `a' is expected here, so
  ;; do not test for no warnings.
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let* ((a (iter-yield c)) (b (iter-yield b)) (c (iter-yield a))) (list a b c)))
    (iter2--test fn :args '(1 2 3) :returned '(4 5 6) :expected '(3 2 4) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-let*-5 ()
  ;; Like above, with extra unused bindings.
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let* ((a (iter-yield c)) (x) (y) (b (iter-yield b)) z (c (iter-yield a))) (list a b c)))
    (iter2--test fn :args '(1 2 3) :returned '(4 5 6) :expected '(3 2 4) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-let-with-globals-1 ()
  (let ((iter2--test-global-var-1 0))
    (iter2--runtime-eval fn (iter2-lambda () (let ((iter2--test-global-var-1 1)) (iter-yield iter2--test-global-var-1) (iter-yield iter2--test-global-var-1)))
      (iter2--test fn :expected '(1 1)
                   :body ((should (= iter2--test-global-var-1 0))))
      (iter2--assert-num-lambdas fn 6)
      (iter2--test-byte-compiles-with-no-warnings fn))))

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
      (iter2--assert-num-lambdas fn 9)
      (iter2--test-byte-compiles-with-no-warnings fn))))

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
      (iter2--assert-num-lambdas fn 7)
      (iter2--test-byte-compiles-with-no-warnings fn))))

(ert-deftest iter2-let*-with-globals-1 ()
  (let ((iter2--test-global-var-1 0))
    (iter2--runtime-eval fn (iter2-lambda () (let* ((iter2--test-global-var-1 1)) (iter-yield iter2--test-global-var-1) (iter-yield iter2--test-global-var-1)))
      (iter2--test fn :expected '(1 1)
                   :body ((should (= iter2--test-global-var-1 0))))
      (iter2--assert-num-lambdas fn 7)
      (iter2--test-byte-compiles-with-no-warnings fn))))

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
      (iter2--assert-num-lambdas fn 12)
      (iter2--test-byte-compiles-with-no-warnings fn))))

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
      (iter2--assert-num-lambdas fn 10)
      (iter2--test-byte-compiles-with-no-warnings fn))))

(ert-deftest iter2-unwind-protect-1 ()
  (iter2--runtime-eval fn (iter2-lambda (a) (or (catch 'x (unwind-protect (throw 'x (iter-yield 1)) (setq a (1+ a)))) a))
    (iter2--test fn :args '(1)                :expected '(1) :end-value 2)
    (iter2--test fn :args '(1) :returned '(0) :expected '(1) :end-value 0)
    (iter2--assert-num-lambdas fn 11)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-unwind-protect-2 ()
  (iter2--runtime-eval fn (iter2-lambda (a) (+ (catch 'x (unwind-protect (or (iter-yield 1) (when (iter-yield 2) (throw 'x (iter-yield 3))) 4) (setq a (1+ a)))) a))
    (iter2--test fn :args '(1)                      :expected '(1 2)   :end-value 6)
    (iter2--test fn :args '(1) :returned '(nil t 8) :expected '(1 2 3) :end-value 10)
    (iter2--test fn :args '(1) :returned '(5)       :expected '(1)     :end-value 7)
    (iter2--assert-num-lambdas fn 14)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-unwind-protect-3 ()
  (iter2--runtime-eval fn (iter2-lambda (x y) (unwind-protect (progn (iter-yield (funcall x)) 0) (funcall y)))
    (let (done)
      (iter2--test fn :args (list (lambda () 1) (lambda () (setq done t))) :expected '(1) :end-value 0)
      (should done))
    (let (done)
      (catch 'eek
        (iter2--test fn :args (list (lambda () (throw 'eek nil)) (lambda () (setq done t)))))
      (should done))
    (iter2--assert-num-lambdas fn 8)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-unwind-protect-4 ()
  ;; `unwind-protect' here does nothing and can be ignored.
  (iter2--runtime-eval fn (iter2-lambda (a) (or (catch 'x (unwind-protect (throw 'x (iter-yield 1)))) a))
    (iter2--test fn :args '(1)                :expected '(1) :end-value 1)
    (iter2--test fn :args '(1) :returned '(0) :expected '(1) :end-value 0)
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

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
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-unwind-protect-close-2 ()
  ;; Same with nested `unwind-protect' forms.
  (iter2--runtime-eval fn (iter2-lambda (done)
                            (unwind-protect (progn (iter-yield 0)
                                                   (unwind-protect (iter-yield 1) (funcall done 1))
                                                   (iter-yield 2))
                              (funcall done 2)))
    (let* (done
           (it (funcall fn (lambda (n) (push n done)))))
      ;; Closing before `unwind-protect' forms are even reached.
      (should (equal done nil))
      (iter-close it)
      (should (equal done nil)))
    (let* (done
           (it (funcall fn (lambda (n) (push n done)))))
      ;; Letting everything run normally.
      (should (equal done nil))
      (should (equal (iter-next it) 0))
      (should (equal done nil))
      (should (equal (iter-next it) 1))
      (should (equal done nil))
      (should (equal (iter-next it) 2))
      (should (equal done '(1)))
      (should (equal (condition-case error (cons nil (iter-next it 3)) (iter-end-of-sequence error))
                     '(iter-end-of-sequence . 3)))
      (should (equal done '(2 1))))
    (let* (done
           (it (funcall fn (lambda (n) (push n done)))))
      ;; Stopping early, before second `unwind-protect' is reached...
      (should (equal done nil))
      (should (equal (iter-next it) 0))
      (should (equal done nil))
      (iter-close it)
      (should (equal done '(2))))
    (let* (done
           (it (funcall fn (lambda (n) (push n done)))))
      ;; Stopping early, when second `unwind-protect' is already reached...
      (should (equal done nil))
      (should (equal (iter-next it) 0))
      (should (equal done nil))
      (should (equal (iter-next it) 1))
      (should (equal done nil))
      (iter-close it)
      (should (equal done '(2 1))))
    (let* (done
           (it (funcall fn (lambda (n) (push n done)))))
      ;; Like above, just a bit later...
      (should (equal done nil))
      (should (equal (iter-next it) 0))
      (should (equal done nil))
      (should (equal (iter-next it) 1))
      (should (equal done nil))
      (should (equal (iter-next it) 2))
      (should (equal done '(1)))
      (iter-close it)
      (should (equal done '(2 1))))
    (iter2--assert-num-lambdas fn 13)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-condition-case-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case _ (error "oh") (foo (iter-yield 1) (iter-yield 2)) (error (iter-yield 3) (iter-yield 4))))
    (iter2--test fn :expected '(3 4))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-condition-case-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case err (when (iter-yield 1) (signal (iter-yield 2) (iter-yield 3)))
                                             (file-error (iter-yield (cdr err))) (arith-error (iter-yield 4) (iter-yield 5))))
    (iter2--test fn                                  :expected '(1))
    (iter2--test fn :returned '(t file-error t 6)    :expected '(1 2 3 t)   :end-value 6)
    (iter2--test fn :returned '(t arith-error t 7 8) :expected '(1 2 3 4 5) :end-value 8)
    (iter2--assert-num-lambdas fn 9)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-condition-case-3 ()
  ;; Test `condition-case' that has no handlers.
  (iter2--runtime-eval fn (iter2-lambda (x) (iter-yield (condition-case nil x)))
    (iter2--test fn :args '(nil) :returned '(nil) :expected '(nil))
    (iter2--test fn :args '(1)   :returned '(2)   :expected '(1) :end-value 2)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-condition-case-error-1 ()
  (should-error (eval '(iter2-lambda () (condition-case nil (foo) error)) t)))

(ert-deftest iter2-catch-1 ()
  (iter2--runtime-eval fn (iter2-lambda (a b) (catch 'x (throw 'x (iter-yield a)) b))
    (iter2--test fn :args '(1 2)                :expected '(1))
    (iter2--test fn :args '(1 2) :returned '(3) :expected '(1) :end-value 3)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-catch-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch 'x (iter-yield 1) (when (iter-yield 2) (throw 'x (iter-yield 3))) (iter-yield 4)))
    (iter2--test fn                      :expected '(1 2 4))
    (iter2--test fn :returned '(5 6 7)   :expected '(1 2 3) :end-value 7)
    (iter2--test fn :returned '(t nil t) :expected '(1 2 4) :end-value t)
    (iter2--assert-num-lambdas fn 9)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-catch-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch (or (iter-yield 1) 'x) (catch (or (iter-yield 2) 'y) (throw (or (iter-yield 3) 'x) (iter-yield 4)) 5) 6))
    (iter2--test fn                      :expected '(1 2 3 4))
    (iter2--test fn :returned '(x y y 0) :expected '(1 2 3 4) :end-value 6)
    (iter2--test fn :returned '(y x y 0) :expected '(1 2 3 4) :end-value 0)
    (should (= (catch 'z (iter2--test fn :returned '(a b z 0) :expected '(1 2 3 4))) 0))
    (iter2--assert-num-lambdas fn 15)
    (iter2--test-byte-compiles-with-no-warnings fn)))

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
    (iter2--assert-num-lambdas fn 8)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-save-current-buffer-1 ()
  (iter2--runtime-eval fn (iter2-lambda ()
                            (with-temp-buffer
                              (while (let ((x (iter-yield nil))) (when x (insert (prin1-to-string x)) t)))
                              (buffer-substring (point-min) (point-max))))
    (iter2--test fn                        :expected '(nil)             :end-value "")
    (iter2--test fn :returned '(1)         :expected '(nil nil)         :end-value "1")
    (iter2--test fn :returned '(1 2)       :expected '(nil nil nil)     :end-value "12")
    (iter2--test fn :returned '(1 2 (3 4)) :expected '(nil nil nil nil) :end-value "12(3 4)")
    (iter2--assert-num-lambdas fn 12)
    (iter2--test-byte-compiles-with-no-warnings fn)))

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
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-save-match-data-1 ()
  (iter2--runtime-eval fn (iter2-lambda (string regexp) (save-match-data (string-match regexp string) (iter-yield (match-string 0 string)) (iter-yield (match-string 1 string))))
    (let ((string "iter2 is cool"))
      (string-match "cool" string)
      (iter2--test fn :args '("foo bar" "b\\(a\\)r") :expected '("bar" "a")
                   :body ((should (equal (match-string 0 string) "cool")))))))

(ert-deftest iter2-save-match-data-2 ()
  (iter2--runtime-eval fn (iter2-lambda (string regexp) (iter2--save-match-data-wrapper (string-match regexp string) (iter-yield (match-string 0 string)) (iter-yield (match-string 1 string))))
    (let ((string "iter2 is cool"))
      (string-match "cool" string)
      (iter2--test fn :args '("foo bar" "b\\(a\\)r") :expected '("bar" "a")
                   :body ((should (equal (match-string 0 string) "cool")))))))

(ert-deftest iter2-calls-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    (iter2--test fn                    :expected '(1 2 3) :end-value '(nil nil nil))
    (iter2--test fn :returned '(4 5 6) :expected '(1 2 3) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-calls-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (vector (iter-yield 1)) (vector (iter-yield 2)) (vector (iter-yield 3))))
    (iter2--test fn                    :expected '(1 2 3) :end-value '([nil] [nil] [nil]))
    (iter2--test fn :returned '(4 5 6) :expected '(1 2 3) :end-value '([4] [5] [6]))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

;; Written against a real bug caused by a typo in `iter2--stack-head-reversing-form'.
(ert-deftest iter2-calls-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (iter-yield 1) (iter-yield 2) (iter-yield 3) (iter-yield 4)))
    (iter2--test fn                      :expected '(1 2 3 4) :end-value '(nil nil nil nil))
    (iter2--test fn :returned '(5 6 7 8) :expected '(1 2 3 4) :end-value '(5 6 7 8))
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-calls-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (> (+ (iter-yield 1) (iter-yield 2)) 0))
    (iter2--test fn :returned '(1 1) :expected '(1 2) :end-value t)
    (iter2--test fn :returned '(0 0) :expected '(1 2) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-calls-5 ()
  ;; Enough arguments to trigger a call to `iter2--reverse-stack-head-n'.
  (iter2--runtime-eval fn (iter2-lambda () (+ (iter-yield 1) (iter-yield 2) (iter-yield 3) (iter-yield 4) (iter-yield 5)))
    (iter2--test fn :returned '( 1  2  3  4  5) :expected '(1 2 3 4 5) :end-value 15)
    (iter2--test fn :returned '(+1 -2 +3 -4 +5) :expected '(1 2 3 4 5) :end-value  3)
    (iter2--assert-num-lambdas fn 8)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-nested-yields-1 ()
  (iter2--runtime-eval fn (iter2-lambda (&optional x) (iter-yield (iter-yield x)))
    (iter2--test fn                             :expected '(nil nil))
    (iter2--test fn :args '(1)                  :expected '(1 nil))
    (iter2--test fn :args '(2) :returned '(3 4) :expected '(2 3) :end-value 4)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-yield-from-1 ()
  (iter2--runtime-eval fn1 (iter2-lambda (&rest values_) (while values_ (iter-yield (pop values_))))
    (iter2--runtime-eval fn2 (iter2-lambda (it) (iter-yield-from it))
      (iter2--test fn1 :args '(1 2 3)                   :expected '(1 2 3))
      (iter2--test fn2 :args (list (funcall fn1 1 2 3)) :expected '(1 2 3))
      (iter2--assert-num-lambdas fn1 4)
      (iter2--assert-num-lambdas fn2 11)
      (iter2--test-byte-compiles-with-no-warnings fn1)
      (iter2--test-byte-compiles-with-no-warnings fn2))))

(ert-deftest iter2-illegal-yield-1 ()
  (should-error (eval '(iter2-lambda () (iter-yield)) t)))

(ert-deftest iter2-illegal-yield-2 ()
  (should-error (eval '(iter2-lambda () (iter-yield 1 2 3)) t)))

(ert-deftest iter2-illegal-yield-3 ()
  (should-error (eval '(iter2-lambda () (unwind-protect (foo) (iter-yield 1))) t)))

(ert-deftest iter2-metamacro-1 ()
  ;; Test with a macro that expands to (another) macro.
  (iter2--runtime-eval fn (iter2-lambda () (iter2--let-wrapper-2 ((x 1)) (iter-yield x)))
    (iter2--test fn :expected '(1))
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-with-no-warnings-1 ()
  (let* ((variable (make-symbol "variable"))
         (fn       (eval `(iter2-lambda () (with-no-warnings (set ',variable (iter-yield 1)))) t)))
    (iter2--test fn                :expected '(1))
    (iter2--test fn :returned '(2) :expected '(1) :end-value 2)
    (iter2--assert-num-lambdas fn 4)
    (makunbound variable)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-with-no-warnings-2 ()
  (let* ((variable (make-symbol "variable"))
         (fn       (eval `(iter2-lambda () (with-no-warnings (set ',variable (iter-yield 1))) 10) t)))
    (iter2--test fn                :expected '(1) :end-value 10)
    (should (equal (symbol-value variable) nil))
    (iter2--test fn :returned '(2) :expected '(1) :end-value 10)
    (should (equal (symbol-value variable) 2))
    (iter2--assert-num-lambdas fn 5)
    (makunbound variable)
    (iter2--test-byte-compiles-with-no-warnings fn)))


(ert-deftest iter2-defun-1 ()
  (iter2--runtime-eval fn (iter2-defun iter2--test-defun-1 () (iter-yield 1) (iter-yield 2))
    (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4)
    (should (equal (iter2--test-intern-symbols (symbol-function fn))
                   (iter2--test-intern-symbols (iter2--runtime-eval fn (iter2-lambda () (iter-yield 1) (iter-yield 2)) fn))))))

(ert-deftest iter2-defun-2 ()
  (iter2--with-test-tracing
    (iter2--runtime-eval fn (iter2-tracing-defun iter2--test-defun-1 () (iter-yield 1) (iter-yield 2))
      (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4)
      (should (equal (iter2--test-intern-symbols (symbol-function fn))
                     (iter2--test-intern-symbols (iter2--runtime-eval fn (iter2-tracing-lambda () (iter-yield 1) (iter-yield 2)) fn)))))))


(ert-deftest iter2-tracing-1 ()
  (iter2--with-test-tracing
    (iter2--runtime-eval fn (iter2-tracing-lambda () (iter-yield 1) (iter-yield 2))
      (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4)
      (should (equal (reverse traced-messages)
                     '("iter2: invoking ... with value nil" "    iter2: yielding 1"
                       "iter2: invoking ... with value 3"   "    iter2: yielding 2"))))))

(ert-deftest iter2-tracing-2 ()
  (iter2--with-test-tracing
    (iter2--runtime-eval fn (iter2-lambda () (iter-yield 1) (iter-yield 2))
      (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4)
      (should (null traced-messages)))))

(ert-deftest iter2-tracing-3 ()
  (iter2--with-test-tracing
    (let ((iter2-generate-tracing-functions t))
      (iter2--runtime-eval fn (iter2-lambda () (iter-yield 1) (iter-yield 2))
        (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4)
        (should (equal (reverse traced-messages)
                       '("iter2: invoking ... with value nil" "    iter2: yielding 1"
                         "iter2: invoking ... with value 3"   "    iter2: yielding 2")))))))


(ert-deftest iter2-nested-lambda-detection-1 ()
  ;; It seems that passing an alist to `eval' is not enough, because
  ;; apparently macros are expanded before that takes effect.
  (let ((iter2-detect-nested-lambda-yields t))
    (should-error (eval '(iter2-lambda (x) (mapc (lambda (v) (iter-yield v)) x)) t)))
  ;; With detection off it should be converted just fine, but fail at
  ;; runtime.
  (let* ((iter2-detect-nested-lambda-yields nil)
         (fn (eval '(iter2-lambda (x) (mapc (lambda (v) (iter-yield v)) x)) t)))
    (should-error (iter-next (funcall fn '(1 2 3))))))


(ert-deftest iter2-requires-lexical-binding-1 ()
  (should-error (eval '(iter2-lambda () (iter-yield 1) (iter-yield 2)) nil)))
