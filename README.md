[![License: GPL 3](https://img.shields.io/badge/license-GPL_3-green.svg)](http://www.gnu.org/licenses/gpl-3.0.txt)
[![Build Status](https://secure.travis-ci.org/doublep/iter2.png)](http://travis-ci.org/doublep/iter2)
[![MELPA Stable](http://stable.melpa.org/packages/iter2-badge.svg)](http://stable.melpa.org/#/logview)
[![Coverage Status](https://coveralls.io/repos/github/doublep/iter2/badge.svg)](https://coveralls.io/github/doublep/iter2)


# iter2

`iter2` is a fully compatible reimplementation of built-in `generator`
package.  It provides `iter2-defun` and `iter2-lambda` forms that can
be used in place of `iter-defun` and `iter-lambda`.  All other
functions and macros (e.g. `iter-yield`, `iter-next`) are
intentionally not duplicated: just use the ones from the original
package.

Advantages:

* Support for `save-excursion` and similar special forms and also
  macro `save-match-data` (see [detailed description below](#save-x)).

* Generator functions can be debugged with Edebug.

* Much faster conversion of complex generator functions.

* Generally faster resulting functions.

* Considerably smaller generated code, especially for complex
  functions.

* More readable resulting functions and backtraces.

* Built-in tracing support for generated iterator functions.

Disadvantages:

* Because `iter2` conversion is heavily optimized, it is not as
  generic as in original `generator` package and is, therefore, more
  prone to bugs.


## Installation

`iter2` is available from MELPA (I recommend using the
[stable](http://stable.melpa.org/#/iter2) version).  Assuming your
`package-archives` lists MELPA, just type

    M-x package-install RET iter2 RET

to install it.

Alternatively, installing `iter2` from source is not difficult either.
First, clone the source code:

    $ cd SOME-PATH
    $ git clone https://github.com/doublep/iter2.git

Now, from Emacs execute:

    M-x package-install-file RET SOME-PATH/iter2

### Running regression tests

This is only possible if you have the full source code, e.g. cloned it
from Git as described above.  Just execute `./run-tests.sh` from the
`iter2` directory.  All tests must pass, there can be no “expected
failures”.


## Usage

### In place of `generator`

Just replace all `iter-defun` with `iter2-defun` and `iter-lambda`
with `iter2-lambda`.  And, of course, add

    (require 'iter2)

somewhere at the top of your file.  You are done, no other changes are
needed.

### From scratch

Please refer to [description in Wikipedia][1] for reasons to use
generator functions in general.

To declare a generator function, use `iter2-defun` or `iter2-lambda`.
Inside the function you can yield control with `iter-yield`.  For
example:

    (iter2-defun unbounded-counter (start)
      (while t
        (iter-yield start)
        (setq start (1+ start))))

Yielding can happen anywhere inside generator function with one
exception: you cannot yield from cleanup forms inside `(unwind-protect
BODY CLEANUP...)`.  It is also possible to yield values produced by
another generator with `iter-yield-from` macro.

To create an iterator object, call generator function as a usual
function.  Once you have an iterator object, retrieve values from it
using `iter-next`:

    (let ((it (unbounded-counter 1)))
      (dotimes (_ 5)
        (print (iter-next it))))

You should always call `iter-close` on iterator object once you no
longer need it.  Otherwise, cleanup forms in `unwind-protect` in the
generator may not run.  Iterators produced by our `unbounded-counter`
do not really need closing, since `unwind-protect` is never used in
that function, but if you write anything that works with arbitrary
generators, keep that in mind.

If generator function terminates, `iter-next` will signal condition
`iter-end-of-sequence` with evaluated value.  For example, this form:

    (let ((it (funcall (iter2-lambda ()
                         (iter-yield 1)
                         2))))
      (iter-next it)
      (iter-next it))

will signal `(iter-end-of-sequence . 2)`.  You can use
`condition-case` to handle this condition.  In simple cases, you can
use `iter-do` macro, which parallels `dolist` and always run its
iterator till the end:

    (iter-do (x (funcall (iter2-lambda ()
                           (iter-yield 'a)
                           (iter-yield 'b))))
      (print x))

Optional second parameter of `iter-next` is the value that is returned
by `iter-yield` inside generator function.  To illustrate:

    (iter2-defun parrot (value)
      (while t
        (setq value (iter-yield value))))

    (let ((it (parrot 1)))
      (print (iter-next it))  ; first time it is not used
      (print (iter-next it 'hello))
      (print (iter-next it (list 1 2 3)))
      (print (iter-next it)))


## Tips and tricks

* Since `iter2` is fully compatible with `generator`, they can be used
  interchangeably or even together, and will produce identical end
  results, save for any bugs.  Therefore, if you suspect a bug in
  `iter2`, try replacing `iter2-defun` with `iter-defun` in your
  generator definition.  Remember, though, that `generator` package
  also has bugs, e.g. [with lambda parameter names matching already
  bound variable names][2].

* Generator functions can only yield “on their own”, it is not allowed
  to have a called function yield control on their behalf.  For
  example, this is illegal:

      (iter2-defun clever-but-illegal (&rest args)
        (mapc (lambda (x) (iter-yield x)) args))

  The package provides a guard against such mistakes.  It is not on by
  default, but you can activate it by customizing
  `iter2-detect-nested-lambda-yields`.  It can come in very handy,
  since oftentimes nested lambdas are generated by macros (e.g. by
  `dash.el`) without you even being aware of that.

  Remember that calling `iter-yield` by its name is also illegal.
  I.e. like this:

      (iter2-defun clever-but-illegal-2 (&rest args)
        (mapc #'iter-yield args))

  Unfortunately, the guard will not detect such things and they will
  fail only at runtime.  Just remember, never ever call `iter-yield`
  by name, always use `(iter-yield ...)` form.

### Current buffer, point etc.<a id="save-x"></a>

In general, generator functions must be aware that when `iter-yield`
gives control back, invoking function can do anything it wants,
including switching to other buffers, moving point, matching regular
expressions and so on.  When generator function resumes, its local
variables (and dynamic ones it rebound) get their values restored, but
not other global state.

However, you can use special forms `save-excursion`,
`save-current-buffer`, `save-restriction` and macro `save-match-data`
to “separate” generator function buffer and match data state from its
caller’s state.  This is probably easier to illustrate with an
example:

    (iter2-defun uses-own-buffer ()
      (with-temp-buffer
        (insert "foo")
        (iter-yield 1)
        (insert " bar")
        (buffer-substring (point-min) (point-max))))

    (print (iter-do (_ (uses-own-buffer))
             (insert "just a test")))

This example doesn’t do anything remotely useful, of course, but it
shows how generator function and its caller can write each to its own
buffer: `with-temp-buffer` internally uses `save-current-buffer`.


[1]: https://en.wikipedia.org/wiki/Generator_(computer_programming)
[2]: https://debbugs.gnu.org/cgi/bugreport.cgi?bug=26073
