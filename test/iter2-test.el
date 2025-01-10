;;; -*- lexical-binding: t -*-

;;; Copyright (C) 2017-2025 Paul Pogonyshev

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


;; Evaluating iterator lambdas at runtime simplifies testing changes immediately.
(defmacro iter2--runtime-eval (name value &rest body)
  (declare (debug (symbolp form body))
           (indent 2))
  (let (catching)
    (while (keywordp (car body))
      (pcase-exhaustive (pop body)
        (:catching (setf catching (pop body)))))
    `(let ((,name (eval ,(macroexp-quote value) t))
           ;; Optionally bind a _catching_ variant of the lambda: it catches all user errors and returns
           ;; string "user error" in such cases.  Used to test that nonlocal exits from `iter2-next' don't get
           ;; lost.
           ,@(when catching (pcase-exhaustive value
                              (`(iter2-lambda ,arglist . ,body)
                               `((,catching (eval '(iter2-lambda ,arglist (condition-case nil ,(macroexp-progn body) (user-error "user error"))) t)))))))
       ,@body)))

(defmacro iter2--pretty-print-if-failing (function &rest body)
  (declare (debug (sexp body))
           (indent 1))
  (let (extra)
    (while (keywordp (car body))
      (pcase-exhaustive (pop body)
        (:extra (setf extra (pop body)))))
    (let ((error (make-symbol "$error")))
      `(condition-case ,error
           (progn ,@body)
         (error (princ "Pretty-printed failing function:\n")
                (pp ,function)
                ,extra
                (signal (car ,error) (cdr ,error)))))))

(cl-defmacro iter2--do-test (function next-type &key args expected returned returned-expression end-value end-signal max-length after-yield when-done)
  (let ((description (format-message "iterator %S" (if args `(apply ,function ,args) `(funcall ,function)))))
    ;; Don't create symbols for variables in a private macro: this lets
    ;; `returned-expression' have access to everything.
    `(let* ((fn        ,function)
            (args      ,args)
            (it        (apply fn args))
            (expected  ,expected)
            (returned  ,returned)
            (to-return (cons nil returned))
            value
            result
            terminated-normally
            end-value
            end-signal)
       (iter2--pretty-print-if-failing fn
         :extra (progn (princ "\n")
                       ,@(when args
                           `((princ (format "Arguments: %S\n" ,args))))
                       (princ (format "Expected:  %S\n" expected))
                       (princ (format "Returned:  %S\n" returned))
                       ,@(when returned-expression
                           `((princ (format "    then:  %S\n" ,(macroexp-quote returned-expression)))))
                       (princ (format "Yielded:   %S\n\n" result)))
         (condition-case error
             (catch 'too-long
               (while t
                 (setq value ,(pcase-exhaustive next-type
                                (`iter-next  `(iter-next it (if to-return (eval (pop to-return) t) ,returned-expression)))
                                (`iter2-next `(let ((expression (if to-return (pop to-return) ,(macroexp-quote returned-expression))))
                                                (eval `(iter2-next it ,expression) `((it . ,it) (value . ,value) (result . ,result)))))))
                 (push value result)
                 (when (= (length result) (or ,max-length (+ (length expected) 5)))
                   (throw 'too-long nil))
                 ,@after-yield)
               ,@when-done)
           (iter-end-of-sequence (setq terminated-normally t
                                       end-value           (cdr error)))
           ;; Using `error' rather than t, since the latter is supported only on Emacs 27 and up.  For tests
           ;; we don't really need completeness ("catch everything" semantics), so this is fine.
           (error                (setq end-signal          error)))
         (setq result (nreverse result))
         (should (equal (progn ,(format-message "%s yielded values" description) result) expected))
         (if terminated-normally
             (should (equal (progn ,(format-message "%s end value" description) end-value)  ,end-value))
           (should (equal (progn ,(format-message "%s exit signal" description) end-signal) ,end-signal))))
       nil)))

(cl-defmacro iter2--test (function &key args expected returned returned-expression end-value end-signal max-length
                                   after-yield when-done no-std-next catching)
  "Test given FUNCTION.
Key parameter meaning:

  ARGS        -- passed to the FUNCTION call itself;
  EXPECTED    -- list of values that must be yielded by the iterator;
  RETURNED    -- list of expressions to calculate values for each
                 successive call to `iter2-next'; they can use variable
                 `value' that holds the last yielded value;
  RETURNED-EXPRESSION -- instead of a list, you can specify one
                 expression to be evaluated as many times as needed;
                 can also be specified together with the list, in which
                 case expression is used after the list is exhausted;
  END-VALUE   -- the end value that must be returned by the iterator
                 when it signals `iter-end-of-sequence';
  END-SIGNAL  -- expect that the iterator exits with given signal
                 rather than normally;
  MAX-LENGTH  -- stop checking after this many yields (for unbounded
                 iterators);
  AFTER-YIELD -- forms to evaluate _each time_ the iterator yields;
  WHEN-DONE   -- forms to evaluate once the iterator is exhausted;
  NO-STD-NEXT -- don't try using `iter2-next'."
  `(progn
     ,@(unless no-std-next
         `((iter2--do-test ,function iter-next :args ,args :expected ,expected :returned ,returned :returned-expression ,returned-expression
                           :end-value ,end-value :end-signal ,end-signal :max-length ,max-length :after-yield ,after-yield :when-done ,when-done)))
     (iter2--do-test ,function iter2-next :args ,args :expected ,expected :returned ,returned :returned-expression ,returned-expression
                     :end-value ,end-value :end-signal ,end-signal :max-length ,max-length :after-yield ,after-yield :when-done ,when-done)
     ;; See `iter2--runtime-eval'.  If there is a "catching variant", automatically create tests that instead
     ;; of returning next value (for each possible position) signal a user error or a generic error.  The
     ;; former must get caught and result in end-value being "user error"; the latter gets propagated out as
     ;; end-signal.
     ,@(when catching
         (cl-assert (and expected (eq (car expected) 'quote)))
         (cl-assert (or (null returned) (eq (car returned) 'quote)))
         (let ((expected (cadr expected))
               (returned (cadr returned))
               signalling-tests)
           (dotimes (k (length (cdr expected)))
             (let ((expected (butlast expected (1+ k)))
                   (returned (copy-sequence returned)))
               (while (>= (length returned) (length expected))
                 (setf returned (butlast returned)))
               (push `(iter2--do-test ,catching iter2-next :args ,args :expected ',expected
                                      :returned ,(macroexp-quote returned) :returned-expression (if (= (length result) ,(length expected)) (user-error "stop") ,returned-expression)
                                      :end-value "user error" :after-yield ,after-yield :when-done ,when-done)
                     signalling-tests)
               (push `(iter2--do-test ,catching iter2-next :args ,args :expected ',expected
                                      :returned ,(macroexp-quote returned) :returned-expression (if (= (length result) ,(length expected)) (error "stop") ,returned-expression)
                                      :end-signal '(error "stop") :after-yield ,after-yield :when-done ,when-done)
                     signalling-tests)))
           signalling-tests))))

;; To make sure that converted functions don't become too inefficient
;; due to code changes, we also assert number of lambdas they result
;; in.  "Wrong" number of lambdas, of course, doesn't necessarily
;; imply that conversion produced a wrong result, but in such a case
;; it should be manually verified and either the code or the test
;; (expected number of lambdas) fixed.
(defmacro iter2--assert-num-lambdas (form expected)
  `(let ((fn ,form))
     (iter2--pretty-print-if-failing fn
       (should (= (iter2--count-lambas fn) ,expected)))))

;; These are new in Emacs 30.
(declare-function closurep (x))
(declare-function make-interpreted-closure (&rest _))
(defun iter2--test-closurep (x)
  (and (fboundp 'closurep) (closurep x)))

(defun iter2--count-lambas (form)
  (pcase (macroexpand-1 form)
    ((pred iter2--test-closurep)
     ;; FIXME: Is it fine just accessing stuff with `aref' like this?
     (1+ (apply #'+ (mapcar #'iter2--count-lambas (aref form 1)))))
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
  ;; On Emacs 29 snapshots warnings are shown even when not byte-compiling now.  Annoying,
  ;; but at least doesn't break the tests.
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
                                    (push (let ((string (apply #'format format-string arguments)))
                                            ;; Ignore exact invoked closures.  They used to be printed as "(...)" before, but became "#[...]" in Emacs 30.
                                            (setf string (replace-regexp-in-string (rx bos "iter2: invoking " (group (| (seq "(" (1+ any) ")") (seq "#[" (1+ any) "]"))) " with value ")
                                                                                   (lambda (string)
                                                                                     ;; Ignore exact invoked closures.
                                                                                     (pcase (ignore-errors (car (read-from-string (match-string 1 string))))
                                                                                       ((pred iter2--test-closurep) "...")
                                                                                       (`(closure . ,_)             "...")
                                                                                       (_                           (match-string 1 string))))
                                                                                   string t t 1))
                                            (setf string (replace-regexp-in-string (rx " ... with value " (group (1+ any)) eos)
                                                                                   (lambda (string)
                                                                                     ;; Extract passed values from closures if possible.  Invoking random closures is not safe
                                                                                     ;; (they are not necessarily reentrable), but for testing it is good enough.
                                                                                     (condition-case nil
                                                                                         (prin1-to-string (funcall (car (read-from-string (match-string 1 string)))))
                                                                                       (t (match-string 1 string))))
                                                                                   string t t 1))
                                            string)
                                          traced-messages))))
     ,@body))


(defmacro iter2--let-wrapper (bindings &rest body)
  `(let (,@bindings) ,@body))

(defmacro iter2--let-wrapper-2 (bindings &rest body)
  `(iter2--let-wrapper (,@bindings) ,@body))

(defmacro iter2--save-match-data-wrapper (&rest body)
  `(save-match-data ,@body))

(defun iter2--test-byte-compiles-with-no-warnings (&rest functions)
  (let* ((advice (lambda (format &rest arguments) (signal 'byte-compilation-warning (apply #'format-message format arguments)))))
    (advice-add 'byte-compile-warn :before advice)
    (unwind-protect
        (dolist (fn functions)
          (byte-compile fn))
      (advice-remove 'byte-compile-warn advice))))


(defun iter2--test-intern-symbols (value)
  (cond ((consp value)                (cons (iter2--test-intern-symbols (car value)) (iter2--test-intern-symbols (cdr value))))
        ;; FIXME: Is it fine just accessing stuff with `aref' like this?
        ((iter2--test-closurep value) (make-interpreted-closure (aref value 0) (iter2--test-intern-symbols (aref value 1)) (aref value 2)))
        ((symbolp value)              (intern (symbol-name value)))
        (t                            value)))


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

(iter2--test-no-yields iter2-no-yields-let (let ((i 10)) i))
(iter2--test-no-yields iter2-no-yields-let-novars (let nil 42))
(iter2--test-no-yields iter2-no-yields-let*-novars (let* nil 42))

(iter2--test-no-yields iter2-no-yields-let*-shadow-empty
  ;; Emacs 28 (?) started issuing a warning about uninitialized variable here, I'd say
  ;; rightly so.  So, don't byte-compilate anymore.
  :dont-test-for-warnings
  (let* ((i 10)) (ignore i) (let (i) i)))

(iter2--test-no-yields iter2-no-yields-let-shadow-empty
  :dont-test-for-warnings
  (let ((i 10)) (ignore i) (let (i) i)))

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
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2))
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-progn-2 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (progn (progn (dolist (e x) (iter-yield e)))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-progn-3 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (progn (progn (dolist (e x) (iter-yield e)) 'done)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value 'done)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-prog1-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (prog1 x (iter-yield 1)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1) :end-value 0)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-prog1-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (prog1 (iter-yield 1) (iter-yield 2)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2))
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(3 4) :end-value 3)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-prog1-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (prog1 (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3))
    (iter2--test fn :catching catching-fn :expected '(1 2 3) :returned '(4 5 6) :end-value 4)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-prog1-4 ()
  ;; `prog1' here is actually meaningless.
  (iter2--runtime-eval fn (iter2-lambda () (prog1 (iter-yield 1) (iter-yield 2)) (iter-yield 3))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3))
    (iter2--test fn :catching catching-fn :expected '(1 2 3) :returned '(4 5 6) :end-value 6)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-prog1-5 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (prog1 (iter-yield 1) (funcall x)))
    :catching catching-fn
    (let* (called-back
           (callback (lambda () (setq called-back t)))
           (it       (funcall fn callback)))
      (should (not called-back))
      (should (equal (iter-next it) 1))
      (should (not called-back))
      (should (equal (condition-case error (cons nil (iter-next it 2)) (iter-end-of-sequence error))
                     '(iter-end-of-sequence . 2)))
      (should called-back))
    (let* (called-back
           (callback (lambda () (setq called-back t)))
           (it       (funcall catching-fn callback)))
      (should (not called-back))
      (should (equal (iter2-next it) 1))
      (should (not called-back))
      ;; The user error must get caught inside `catching-fn', but this results in callback never being invoked.
      (should (equal (condition-case error (cons nil (iter2-next it (user-error "stop"))) (iter-end-of-sequence error))
                     '(iter-end-of-sequence . "user error")))
      (should (not called-back)))
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-prog1-6 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (prog1 (dolist (e x) (iter-yield e))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-and-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (and 3 (iter-yield 1)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(t) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-and-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (and 3 (iter-yield 1) 4))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(t) :end-value 4)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-and-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (and (iter-yield 1) (iter-yield 2)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(t)   :end-value nil)
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(t t) :end-value t)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-and-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (and (iter-yield 1) (iter-yield 2) (iter-yield (iter-yield 3))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1 2)       :returned '(t)       :end-value nil)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 nil) :returned '(t t))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 6)   :returned '(4 5 6))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 6)   :returned '(4 5 6 7) :end-value 7)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-and-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (and (iter-yield 1)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(t) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-and-6 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (and (dolist (e x) (iter-yield e))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-or-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (or 3 (iter-yield 1)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '() :end-value 3)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-or-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (or nil (iter-yield 1) 4))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1)                :end-value 4)
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(t) :end-value t)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-or-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (or (iter-yield 1) (iter-yield 2)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2))
    (iter2--test fn :catching catching-fn :expected '(1)   :returned '(t)     :end-value t)
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(nil 3) :end-value 3)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-or-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (or (iter-yield 1) (iter-yield 2) (iter-yield (iter-yield 3))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3 nil))
    (iter2--test fn :catching catching-fn :expected '(1)         :returned '(t)             :end-value t)
    (iter2--test fn :catching catching-fn :expected '(1 2)       :returned '(nil 4)         :end-value 4)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 5)   :returned '(nil nil 5))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 nil) :returned '(nil nil nil 6) :end-value 6)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-or-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (or (iter-yield 1)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(t) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-or-6 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (or (dolist (e x) (iter-yield e))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-if-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (if x (iter-yield 1) (iter-yield 2)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(nil) :expected '(2))
    (iter2--test fn :catching catching-fn :args '(t)   :expected '(1))
    (iter2--test fn :catching catching-fn :args '(t)   :expected '(1) :returned '(t) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-if-2 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (if x (iter-yield 1) (iter-yield 2)) 3)
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(nil) :expected '(2)                :end-value 3)
    (iter2--test fn :catching catching-fn :args '(t)   :expected '(1)                :end-value 3)
    (iter2--test fn :catching catching-fn :args '(t)   :expected '(1) :returned '(t) :end-value 3)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-if-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (iter-yield 1) 2 3))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(nil) :end-value 3)
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(t)   :end-value 2)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-if-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (iter-yield 1) 2 3) 4)
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(nil) :end-value 4)
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(t)   :end-value 4)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-if-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 3))
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(t))
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(t t) :end-value t)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-if-6 ()
  (iter2--runtime-eval fn (iter2-lambda () (if (eq (iter-yield 1) 2) 3))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1) :returned '(2) :end-value 3)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-cond-1 ()
  (iter2--runtime-eval fn (iter2-lambda (x y) (cond ((eq x y) (iter-yield 1)) ((equal x y) (iter-yield 2)) (t (iter-yield 3))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(nil nil)     :expected '(1))
    (iter2--test fn :catching catching-fn :args '((nil) (nil)) :expected '(2))
    (iter2--test fn :catching catching-fn :args '(nil t)       :expected '(3))
    (iter2--test fn :catching catching-fn :args '(nil nil)     :expected '(1) :returned '(t) :end-value t)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-cond-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (cond ((eq (iter-yield 1) (iter-yield 2)) 1) ((eq (iter-yield 3) (iter-yield 4)) 2) (t 3)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2)                          :end-value 1)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4) :returned '(1 2)     :end-value 2)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4) :returned '(1 2 3 4) :end-value 3)
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-cond-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (cond ((iter-yield 1) (list (iter-yield 2) 3)) ((iter-yield 4) (list (iter-yield 5) 6))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 4))
    (iter2--test fn :catching catching-fn :expected '(1 2)   :returned '(t t)     :end-value '(t 3))
    (iter2--test fn :catching catching-fn :expected '(1 4 5) :returned '(nil t t) :end-value '(t 6))
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-cond-4 ()
  (iter2--runtime-eval fn (iter2-lambda (a b c d) (cond (a b) (c (- (iter-yield 1))) ((iter-yield 2) (list (iter-yield 3))) ((not (iter-yield 4)) d) (t 0)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(nil nil nil nil) :expected '(2 4) :returned '(nil nil) :end-value nil)
    (iter2--test fn :catching catching-fn :args '(nil nil nil nil) :expected '(2 4) :returned '(nil t)   :end-value 0)
    (iter2--test fn :catching catching-fn :args '(t   10  nil nil) :expected '()                         :end-value 10)
    (iter2--test fn :catching catching-fn :args '(nil nil t   nil) :expected '(1)   :returned '(2)       :end-value -2)
    (iter2--test fn :catching catching-fn :args '(nil nil nil 5)   :expected '(2 3) :returned '(t 6)     :end-value '(6))
    (iter2--test fn :catching catching-fn :args '(nil nil nil 5)   :expected '(2 4) :returned '(nil nil) :end-value 5)
    (iter2--test fn :catching catching-fn :args '(nil nil nil 5)   :expected '(2 4) :returned '(nil 6)   :end-value 0)
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-cond-5 ()
  (iter2--runtime-eval fn (iter2-lambda (x y z) (cond ((iter-yield 1)) (x) (y 4) (z (vector (iter-yield 2)))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1 2 3)       :expected '(1)   :returned '(t)      :end-value t)
    (iter2--test fn :catching catching-fn :args '(1 2 3)       :expected '(1)   :returned '(nil)    :end-value 1)
    (iter2--test fn :catching catching-fn :args '(nil 2 3)     :expected '(1)   :returned '(nil)    :end-value 4)
    (iter2--test fn :catching catching-fn :args '(nil nil 3)   :expected '(1 2) :returned '(nil 'x) :end-value [x])
    (iter2--test fn :catching catching-fn :args '(nil nil nil) :expected '(1)   :returned '(nil)    :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-cond-6 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (cond ((dolist (e x) (iter-yield e)))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-while-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (while t (iter-yield t)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(t t t t t) :max-length 5)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-while-2 ()
  (iter2--runtime-eval fn (iter2-lambda (n) (while (iter-yield (setq n (1+ n)))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1))
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1 2 3 4)   :returned '(t t t))
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1 2 3 4 5) :returned-expression t :max-length 5)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-while-3 ()
  (iter2--runtime-eval fn (iter2-lambda (n) (while (iter-yield (setq n (1+ n))) (iter-yield 'inside)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1))
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1 inside 2 inside 3)          :returned '(t t t))
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1 inside 2 inside 3)          :returned '(t t t t))
    (iter2--test fn :catching catching-fn :args '(0) :expected '(1 inside 2 inside 3 inside 4) :returned '(t nil t nil t))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-while-4 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (while x (setq x (iter-yield x))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(nil) :expected '())
    (iter2--test fn :catching catching-fn :args '(t)   :expected '(t))
    (iter2--test fn :catching catching-fn :args '(1)   :expected '(1 2 3)     :returned '(2 3))
    (iter2--test fn :catching catching-fn :args '(0)   :expected '(0 1 2 3 4) :returned-expression (1+ value) :max-length 5)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-while-5 ()
  (iter2--runtime-eval fn (iter2-lambda () (while (or (iter-yield 1) (iter-yield 2)) (iter-yield 3)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2))
    (iter2--test fn :catching catching-fn :expected '(1 3 1 2)   :returned '(t))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 1 2) :returned '(nil t))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 1 2) :returned '(nil t t))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-while-6 ()
  (iter2--runtime-eval fn (iter2-lambda () (while (> (+ (iter-yield 1) (iter-yield 2)) 0) (iter-yield 3)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2)       :returned '(0 0))
    (iter2--test fn :catching catching-fn :expected '(1 2)       :returned '(1 -2))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 1 2) :returned '(1 1 nil 0 0))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 1 2) :returned '(-1 2 nil 0 0))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-while-7 ()
  (iter2--runtime-eval fn (iter2-lambda (x)
                            ;; Yielding elements of an array.
                            (let ((n (length x))
                                  (k 0))
                              (when (> n 0)
                                (while (progn (iter-yield (aref x k))
                                              (/= (setf k (1+ k)) n))))))
    :catching catching-fn
    (iter2--test fn                       :args '([]))
    (iter2--test fn :catching catching-fn :args '([a])   :expected '(a))
    (iter2--test fn :catching catching-fn :args '([a b]) :expected '(a b))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (let ((x 1)) (iter-yield x)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (let ((x (iter-yield 1))) (iter-yield x)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 nil))
    (iter2--test fn :catching catching-fn :expected '(1 t) :returned '(t))
    (iter2--test fn :catching catching-fn :expected '(1 t) :returned '(t 5) :end-value 5)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let-3 ()
  ;; Byte-compilation warning about unused `x' is expected here, so do
  ;; not test for no warnings.
  (iter2--runtime-eval fn (iter2-lambda (x) (let ((x (iter-yield x)) (y x) (x 0) (x (iter-yield x))) (list x y)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1 1)                  :end-value '(nil 1))
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1 1) :returned '(2 3) :end-value '(3 1))
    (iter2--assert-num-lambdas fn 5)))

(ert-deftest iter2-let-4 ()
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let ((a (iter-yield c)) (b (iter-yield b)) (c (iter-yield a))) (list a b c)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1 2 3) :expected '(3 2 1) :returned '(4 5 6) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let-5 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (let () (dolist (e x) (iter-yield e))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let-error-1 ()
  (should-error (eval '(iter2-lambda () (let ((x 1 2)))) t)))

(ert-deftest iter2-let*-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (let* ((x 1)) (iter-yield x)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let*-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (let* ((x (iter-yield 1))) (iter-yield x)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 nil))
    (iter2--test fn :catching catching-fn :expected '(1 t)   :returned '(t))
    (iter2--test fn :catching catching-fn :expected '(1 t)   :returned '(t 5) :end-value 5)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let*-3 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (let* ((x (iter-yield x)) (y x) (x 0) (x (iter-yield x))) (list x y)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1 0)                   :end-value '(nil nil))
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1 0) :returned '(2 3) :end-value '(3 2))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-let*-4 ()
  ;; Byte-compilation warnings about unused `a' is expected here, so
  ;; do not test for no warnings.
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let* ((a (iter-yield c)) (b (iter-yield b)) (c (iter-yield a))) (list a b c)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1 2 3) :expected '(3 2 4) :returned '(4 5 6) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-let*-5 ()
  ;; Like above, with extra unused bindings.
  (iter2--runtime-eval fn (iter2-lambda (a b c) (let* ((a (iter-yield c)) (x) (y) (b (iter-yield b)) z (c (iter-yield a))) (list a b c)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1 2 3) :expected '(3 2 4) :returned '(4 5 6) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)))

(ert-deftest iter2-let-with-globals-1 ()
  (let ((iter2--test-global-var-1 0))
    (iter2--runtime-eval fn (iter2-lambda () (let ((iter2--test-global-var-1 1)) (iter-yield iter2--test-global-var-1) (iter-yield iter2--test-global-var-1)))
      :catching catching-fn
      (iter2--test fn :catching catching-fn :expected '(1 1)
                   :after-yield ((should (= iter2--test-global-var-1 0))))
      (iter2--assert-num-lambdas fn 6)
      (iter2--test-byte-compiles-with-no-warnings fn catching-fn))))

(ert-deftest iter2-let-with-globals-2 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda () (let ((iter2--test-global-var-1 (iter-yield 1))
                                                   (x (iter-yield 2))
                                                   (iter2--test-global-var-2 (iter-yield 3)))
                                               (iter-yield (list (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                                 iter2--test-global-var-1 x iter2--test-global-var-2))))
      :catching catching-fn
      (iter2--test fn :catching catching-fn :expected '(1 2 3 (nil nil nil) (nil nil nil nil))
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :catching catching-fn :expected '(1 2 3 (1 2 3) (4 1 2 3))               :returned '(1 2 3 4 5) :end-value 5
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 9)
      (iter2--test-byte-compiles-with-no-warnings fn catching-fn))))

(ert-deftest iter2-let-with-globals-3 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda (x) (let ((iter2--test-global-var-1 x)
                                                    (x (iter-yield 1))
                                                    (iter2--test-global-var-2 x))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))))
      :catching catching-fn
      (iter2--test fn :catching catching-fn :args '(1) :expected '(1 (1 nil 1) (1 nil 1))
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :catching catching-fn :args '(1) :expected '(1 (1 2 1) (1 2 1)) :returned '(2 3 4) :end-value 4
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 7)
      (iter2--test-byte-compiles-with-no-warnings fn catching-fn))))

(ert-deftest iter2-let*-with-globals-1 ()
  (let ((iter2--test-global-var-1 0))
    (iter2--runtime-eval fn (iter2-lambda () (let* ((iter2--test-global-var-1 1)) (iter-yield iter2--test-global-var-1) (iter-yield iter2--test-global-var-1)))
      :catching catching-fn
      (iter2--test fn :catching catching-fn :expected '(1 1)
                   :after-yield ((should (= iter2--test-global-var-1 0))))
      (iter2--assert-num-lambdas fn 7)
      (iter2--test-byte-compiles-with-no-warnings fn catching-fn))))

(ert-deftest iter2-let*-with-globals-2 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda () (let* ((iter2--test-global-var-1 (iter-yield 1))
                                                    (x (iter-yield 2))
                                                    (iter2--test-global-var-2 (iter-yield 3)))
                                               (iter-yield (list (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                                 iter2--test-global-var-1 x iter2--test-global-var-2))))
      :catching catching-fn
      (iter2--test fn :catching catching-fn :expected '(1 2 3 (nil nil nil) (nil nil nil nil))
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :catching catching-fn :expected '(1 2 3 (1 2 3) (4 1 2 3))               :returned '(1 2 3 4 5) :end-value 5
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 12)
      (iter2--test-byte-compiles-with-no-warnings fn catching-fn))))

(ert-deftest iter2-let*-with-globals-3 ()
  (let ((iter2--test-global-var-1 0)
        (iter2--test-global-var-2 0))
    (iter2--runtime-eval fn (iter2-lambda (x) (let* ((iter2--test-global-var-1 x)
                                                     (x (iter-yield 1))
                                                     (iter2--test-global-var-2 x))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))
                                                (iter-yield (list iter2--test-global-var-1 x iter2--test-global-var-2))))
      :catching catching-fn
      (iter2--test fn :catching catching-fn :args '(1) :expected '(1 (1 nil nil) (1 nil nil))
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--test fn :catching catching-fn :args '(1) :expected '(1 (1 2 2) (1 2 2))        :returned '(2 3 4) :end-value 4
                   :after-yield ((should (equal iter2--test-global-var-1 0)) (should (equal iter2--test-global-var-2 0))))
      (iter2--assert-num-lambdas fn 10)
      (iter2--test-byte-compiles-with-no-warnings fn catching-fn))))

(ert-deftest iter2-unwind-protect-1 ()
  (iter2--runtime-eval fn (iter2-lambda (a) (or (catch 'x (unwind-protect (throw 'x (iter-yield 1)) (setq a (1+ a)))) a))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1)                :end-value 2)
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1) :returned '(0) :end-value 0)
    (iter2--assert-num-lambdas fn 11)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-unwind-protect-2 ()
  (iter2--runtime-eval fn (iter2-lambda (a) (+ (catch 'x (unwind-protect (or (iter-yield 1) (when (iter-yield 2) (throw 'x (iter-yield 3))) 4) (setq a (1+ a)))) a))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1 2)                        :end-value 6)
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1 2 3) :returned '(nil t 8) :end-value 10)
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1)     :returned '(5)       :end-value 7)
    (iter2--assert-num-lambdas fn 14)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-unwind-protect-3 ()
  (iter2--runtime-eval fn (iter2-lambda (x y) (unwind-protect (progn (iter-yield (funcall x)) 0) (funcall y)))
    :catching catching-fn
    (let (done)
      (iter2--test fn :catching catching-fn :args (list (lambda () 1) (lambda () (setq done t))) :expected '(1) :end-value 0)
      (should done))
    (let (done)
      (catch 'eek
        (iter2--test fn :args (list (lambda () (throw 'eek nil)) (lambda () (setq done t)))))
      (should done))
    (iter2--assert-num-lambdas fn 8)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-unwind-protect-4 ()
  ;; `unwind-protect' here does nothing and can be ignored.
  (iter2--runtime-eval fn (iter2-lambda (a) (or (catch 'x (unwind-protect (throw 'x (iter-yield 1)))) a))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1)                :end-value 1)
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1) :returned '(0) :end-value 0)
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-unwind-protect-5 ()
  (iter2--runtime-eval fn (iter2-lambda (x) (unwind-protect (dolist (e x) (iter-yield e))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '((1 2 3)) :expected '(1 2 3) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

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
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(3 4))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-condition-case-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case err (when (iter-yield 1) (signal (iter-yield 2) (iter-yield 3)))
                                             (file-error (iter-yield (cdr err))) (arith-error (iter-yield 4) (iter-yield 5))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 t)   :returned '(t 'file-error t 6)    :end-value 6)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4 5) :returned '(t 'arith-error t 7 8) :end-value 8)
    (iter2--assert-num-lambdas fn 9)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-condition-case-3 ()
  ;; Similar to `iter2-condition-case-2', but with `condition-case' body repeated twice.
  (iter2--runtime-eval fn (iter2-lambda () (condition-case err (progn (when (iter-yield 1) (signal (iter-yield 2) (iter-yield 3)))
                                                                      (when (iter-yield 4) (signal (iter-yield 5) (iter-yield 6))))
                                             (file-error (iter-yield (cdr err))) (arith-error (iter-yield 7) (iter-yield 8))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 4))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 t)     :returned '(t 'file-error t 9)          :end-value 9)
    (iter2--test fn :catching catching-fn :expected '(1 4 5 6 t)   :returned '(nil t 'file-error t 9)      :end-value 9)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 7 8)   :returned '(t 'arith-error t 10 11)     :end-value 11)
    (iter2--test fn :catching catching-fn :expected '(1 4 5 6 7 8) :returned '(nil t 'arith-error t 10 11) :end-value 11)
    (iter2--assert-num-lambdas fn 13)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-condition-case-4 ()
  ;; Test `condition-case' that has no handlers.
  (iter2--runtime-eval fn (iter2-lambda (x) (iter-yield (condition-case nil x)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(nil) :expected '(nil) :returned '(nil))
    (iter2--test fn :catching catching-fn :args '(1)   :expected '(1)   :returned '(2)   :end-value 2)
    (iter2--assert-num-lambdas fn 3)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-condition-case-error-1 ()
  (should-error (eval '(iter2-lambda () (condition-case nil (foo) error)) t)))

(ert-deftest iter2-signalling-iter-yield-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case error (iter-yield 10) (user-error (cadr error))))
    (iter2--test fn                :expected '(10) :returned '("ok")               :end-value  "ok")
    (iter2--test fn :no-std-next t :expected '(10) :returned '((user-error "meh")) :end-value  "meh")
    (iter2--test fn :no-std-next t :expected '(10) :returned '((error "meh"))      :end-signal '(error "meh"))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-signalling-iter-yield-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case error (format "proceeding: %s" (iter-yield 10)) (user-error (format "user error (%s)" (cadr error)))))
    (iter2--test fn                :expected '(10) :returned '("ok")               :end-value  "proceeding: ok")
    (iter2--test fn :no-std-next t :expected '(10) :returned '((user-error "meh")) :end-value  "user error (meh)")
    (iter2--test fn :no-std-next t :expected '(10) :returned '((error "meh"))      :end-signal '(error "meh"))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-signalling-iter-yield-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (condition-case error (progn (iter-yield 1) (iter-yield 2) (iter-yield 3)) (user-error (cadr error))))
    (iter2--test fn                :expected '(1 2 3))
    (iter2--test fn :no-std-next t :expected '(1)     :returned '((user-error "stop"))         :end-value "stop")
    (iter2--test fn :no-std-next t :expected '(1)     :returned '((error "stop"))              :end-signal '(error "stop"))
    (iter2--test fn :no-std-next t :expected '(1 2)   :returned '(nil (user-error "stop"))     :end-value "stop")
    (iter2--test fn :no-std-next t :expected '(1 2)   :returned '(nil (error "stop"))          :end-signal '(error "stop"))
    (iter2--test fn :no-std-next t :expected '(1 2 3) :returned '(nil nil (user-error "stop")) :end-value "stop")
    (iter2--test fn :no-std-next t :expected '(1 2 3) :returned '(nil nil (error "stop"))      :end-signal '(error "stop"))
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-catch-1 ()
  (iter2--runtime-eval fn (iter2-lambda (a b) (catch 'x (throw 'x (iter-yield a)) b))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :args '(1 2) :expected '(1))
    (iter2--test fn :catching catching-fn :args '(1 2) :expected '(1) :returned '(3) :end-value 3)
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-catch-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch 'x (iter-yield 1) (when (iter-yield 2) (throw 'x (iter-yield 3))) (iter-yield 4)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 4))
    (iter2--test fn :catching catching-fn :expected '(1 2 3) :returned '(5 6 7)   :end-value 7)
    (iter2--test fn :catching catching-fn :expected '(1 2 4) :returned '(t nil t) :end-value t)
    (iter2--assert-num-lambdas fn 9)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-catch-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch (or (iter-yield 1) 'x) (catch (or (iter-yield 2) 'y) (throw (or (iter-yield 3) 'x) (iter-yield 4)) 5) 6))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4) :returned '('x 'y 'y 0) :end-value 6)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4) :returned '('y 'x 'y 0) :end-value 0)
    (should (= (catch 'z (iter2--test fn :returned '('a 'b 'z 0) :expected '(1 2 3 4))) 0))
    (iter2--assert-num-lambdas fn 15)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-throwing-iter-yield-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch 'done (iter-yield 10)))
    (iter2--test fn                :expected '(10) :returned '("ok")             :end-value  "ok")
    (iter2--test fn :no-std-next t :expected '(10) :returned '((throw 'done 20)) :end-value  20)
    (iter2--test fn :no-std-next t :expected '(10) :returned '((throw 'wut nil)) :end-signal '(no-catch wut nil))
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-throwing-iter-yield-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch 'done (format "proceeding: %s" (iter-yield 10))))
    (iter2--test fn                :expected '(10) :returned '("ok")             :end-value  "proceeding: ok")
    (iter2--test fn :no-std-next t :expected '(10) :returned '((throw 'done 20)) :end-value  20)
    (iter2--test fn :no-std-next t :expected '(10) :returned '((throw 'wut nil)) :end-signal '(no-catch wut nil))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-throwing-iter-yield-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (catch 'done (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    (iter2--test fn                :expected '(1 2 3))
    (iter2--test fn :no-std-next t :expected '(1)     :returned '((throw 'done 10))         :end-value 10)
    (iter2--test fn :no-std-next t :expected '(1)     :returned '((throw 'wut nil))         :end-signal '(no-catch wut nil))
    (iter2--test fn :no-std-next t :expected '(1 2)   :returned '(nil (throw 'done 11))     :end-value 11)
    (iter2--test fn :no-std-next t :expected '(1 2)   :returned '(nil (throw 'wut nil))     :end-signal '(no-catch wut nil))
    (iter2--test fn :no-std-next t :expected '(1 2 3) :returned '(nil nil (throw 'done 12)) :end-value 12)
    (iter2--test fn :no-std-next t :expected '(1 2 3) :returned '(nil nil (throw 'wut nil)) :end-signal '(no-catch wut nil))
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-save-excursion-1 ()
  (iter2--runtime-eval fn (iter2-lambda ()
                            (save-excursion
                              (while (let ((x (iter-yield nil))) (when x (insert (prin1-to-string x)) t)))
                              (buffer-substring (point-min) (point-max))))
    (with-temp-buffer
      (iter2--do-test fn iter-next  :expected '(nil)                                     :end-value ""
                      :after-yield ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--do-test fn iter2-next :expected '(nil)                                     :end-value ""
                      :after-yield ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--do-test fn iter-next  :expected '(nil nil)         :returned '(1)          :end-value "1"
                      :after-yield ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--do-test fn iter2-next :expected '(nil nil)         :returned '(1)          :end-value "1"
                      :after-yield ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--do-test fn iter-next  :expected '(nil nil nil)     :returned '(1 2)        :end-value "12"
                      :after-yield ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--do-test fn iter2-next :expected '(nil nil nil)     :returned '(1 2)        :end-value "12"
                      :after-yield ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--do-test fn iter-next  :expected '(nil nil nil nil) :returned '(1 2 '(3 4)) :end-value "12(3 4)"
                      :after-yield ((set-buffer (messages-buffer)))))
    (with-temp-buffer
      (iter2--do-test fn iter2-next :expected '(nil nil nil nil) :returned '(1 2 '(3 4)) :end-value "12(3 4)"
                      :after-yield ((set-buffer (messages-buffer)))))
    (iter2--assert-num-lambdas fn 9)
    (iter2--test-byte-compiles-with-no-warnings fn)))

(ert-deftest iter2-save-current-buffer-1 ()
  (iter2--runtime-eval fn (iter2-lambda ()
                            (with-temp-buffer
                              (while (let ((x (iter-yield nil))) (when x (insert (prin1-to-string x)) t)))
                              (buffer-substring (point-min) (point-max))))
    :catching catching-fn
    (iter2--test fn                         :expected '(nil)             :end-value "")
    (iter2--test fn :returned '(1)          :expected '(nil nil)         :end-value "1")
    (iter2--test fn :returned '(1 2)        :expected '(nil nil nil)     :end-value "12")
    (iter2--test fn :returned '(1 2 '(3 4)) :expected '(nil nil nil nil) :end-value "12(3 4)")
    (iter2--assert-num-lambdas fn 13)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-save-restriction-1 ()
  (iter2--runtime-eval fn (iter2-lambda ()
                            (save-restriction
                              (widen)
                              (narrow-to-region 1 1)
                              (iter-yield (cons (point-min) (point-max)))
                              (iter-yield (cons (point-min) (point-max)))))
    :catching catching-fn
    (with-temp-buffer
      (insert "bla bla bla")
      (iter2--test fn :catching catching-fn :expected '((1 . 1) (1 . 1)) :after-yield ((should (> (point-max) (point-min))))))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-save-match-data-1 ()
  (iter2--runtime-eval fn (iter2-lambda (string regexp) (save-match-data (string-match regexp string) (iter-yield (match-string 0 string)) (iter-yield (match-string 1 string))))
    :catching catching-fn
    (let ((string "iter2 is cool"))
      (string-match "cool" string)
      (iter2--test fn :catching catching-fn :args '("foo bar" "b\\(a\\)r") :expected '("bar" "a")
                   :after-yield ((should (equal (match-string 0 string) "cool")))))))

(ert-deftest iter2-save-match-data-2 ()
  (iter2--runtime-eval fn (iter2-lambda (string regexp) (iter2--save-match-data-wrapper (string-match regexp string) (iter-yield (match-string 0 string)) (iter-yield (match-string 1 string))))
    :catching catching-fn
    (let ((string "iter2 is cool"))
      (string-match "cool" string)
      (iter2--test fn :catching catching-fn :args '("foo bar" "b\\(a\\)r") :expected '("bar" "a")
                   :after-yield ((should (equal (match-string 0 string) "cool")))))))

(ert-deftest iter2-calls-1 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (iter-yield 1) (iter-yield 2) (iter-yield 3)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3)                    :end-value '(nil nil nil))
    (iter2--test fn :catching catching-fn :expected '(1 2 3) :returned '(4 5 6) :end-value '(4 5 6))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-calls-2 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (vector (iter-yield 1)) (vector (iter-yield 2)) (vector (iter-yield 3))))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3)                    :end-value '([nil] [nil] [nil]))
    (iter2--test fn :catching catching-fn :expected '(1 2 3) :returned '(4 5 6) :end-value '([4] [5] [6]))
    (iter2--assert-num-lambdas fn 6)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

;; Written against a real bug caused by a typo in `iter2--stack-head-reversing-form'.
(ert-deftest iter2-calls-3 ()
  (iter2--runtime-eval fn (iter2-lambda () (list (iter-yield 1) (iter-yield 2) (iter-yield 3) (iter-yield 4)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4)                      :end-value '(nil nil nil nil))
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4) :returned '(5 6 7 8) :end-value '(5 6 7 8))
    (iter2--assert-num-lambdas fn 7)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-calls-4 ()
  (iter2--runtime-eval fn (iter2-lambda () (> (+ (iter-yield 1) (iter-yield 2)) 0))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(1 1) :end-value t)
    (iter2--test fn :catching catching-fn :expected '(1 2) :returned '(0 0) :end-value nil)
    (iter2--assert-num-lambdas fn 5)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-calls-5 ()
  ;; Enough arguments to trigger a call to `iter2--reverse-stack-head-n'.
  (iter2--runtime-eval fn (iter2-lambda () (+ (iter-yield 1) (iter-yield 2) (iter-yield 3) (iter-yield 4) (iter-yield 5)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4 5) :returned '( 1  2  3  4  5) :end-value 15)
    (iter2--test fn :catching catching-fn :expected '(1 2 3 4 5) :returned '(+1 -2 +3 -4 +5) :end-value  3)
    (iter2--assert-num-lambdas fn 8)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

(ert-deftest iter2-nested-yields-1 ()
  (iter2--runtime-eval fn (iter2-lambda (&optional x) (iter-yield (iter-yield x)))
    :catching catching-fn
    (iter2--test fn :catching catching-fn            :expected '(nil nil))
    (iter2--test fn :catching catching-fn :args '(1) :expected '(1 nil))
    (iter2--test fn :catching catching-fn :args '(2) :expected '(2 3) :returned '(3 4) :end-value 4)
    (iter2--assert-num-lambdas fn 4)
    (iter2--test-byte-compiles-with-no-warnings fn catching-fn)))

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
      (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4
                   :when-done ((should (equal (reverse traced-messages)
                                              '("iter2: invoking ... with value nil" "    iter2: yielding 1"
                                                "iter2: invoking ... with value 3"   "    iter2: yielding 2"
                                                "iter2: invoking ... with value 4"))))))))

(ert-deftest iter2-tracing-2 ()
  (iter2--with-test-tracing
    (iter2--runtime-eval fn (iter2-lambda () (iter-yield 1) (iter-yield 2))
      (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4
                   :when-done ((should (null traced-messages)))))))

(ert-deftest iter2-tracing-3 ()
  (iter2--with-test-tracing
    (let ((iter2-generate-tracing-functions t))
      (iter2--runtime-eval fn (iter2-lambda () (iter-yield 1) (iter-yield 2))
        (iter2--test fn :expected '(1 2) :returned '(3 4) :end-value 4
                     :when-done ((should (equal (reverse traced-messages)
                                                '("iter2: invoking ... with value nil" "    iter2: yielding 1"
                                                  "iter2: invoking ... with value 3"   "    iter2: yielding 2"
                                                  "iter2: invoking ... with value 4")))))))))


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


(declare-function iter2--test-using-special-variable nil)

(ert-deftest iter2-byte-compiled-special-variables-1 ()
  (let ((k     0)
        (file (make-temp-file "iter2-" nil ".el"))
        special-variable-name)
    (while (fboundp (setf special-variable-name (intern (format "iter2--test-special-variable-%d" k))))
      (setf k (1+ k)))
    (with-temp-file file
      (insert (format ";;; -*- lexical-binding: t -*-
(require 'iter2)
(defvar iter2--test-global-var-1)
(defvar %s nil)
(defun iter2--test-get-special-variable ()
  %s)
(iter2-defun iter2--test-rebinding-special-variable (x)
  (let ((%s x))
    (iter-yield (iter2--test-get-special-variable))
    (iter-yield (iter2--test-get-special-variable))))
(defun iter2--test-using-special-variable (x)
  (iter-do (v (iter2--test-rebinding-special-variable x))
    (push v iter2--test-global-var-1)))
" special-variable-name special-variable-name special-variable-name)))
    (byte-compile-file file)
    (load (format "%s.elc" (file-name-sans-extension file)) nil t))
  (let ((iter2--test-global-var-1 nil))
    (should (byte-code-function-p (symbol-function 'iter2--test-rebinding-special-variable)))
    (iter2--test-using-special-variable t)
    (should (equal iter2--test-global-var-1 '(t t)))))
