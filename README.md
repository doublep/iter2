[![License: GPL 3](https://img.shields.io/badge/license-GPL_3-green.svg)](http://www.gnu.org/licenses/gpl-3.0.txt)
[![Build Status](https://secure.travis-ci.org/doublep/iter2.png)](http://travis-ci.org/doublep/iter2)
[![GitHub release](https://img.shields.io/github/release/doublep/iter2.svg?maxAge=86400)](https://github.com/doublep/iter2/releases)


# iter2

`iter2` is a fully compatible reimplementation of built-in `generator`
package.  It provides `iter2-defun` and `iter2-lambda` forms that can
be used instead of `iter-defun` and `iter-lambda`.  All other
functions and macros (e.g. `iter-yield`, `iter-next`) are
intentionally not duplicated: just use the ones from the original
package.

Advantages:

* *Much* faster conversion of complicated generator functions.

* Generally faster resulting functions, though this can vary.

* Considerably smaller generated code, especially for complicated
  functions.

* A bit more readable resulting functions.  There is also a built-in
  tracing support.

Disadvantages:

* Because `iter2` conversion is heavily optimized, it is not as
  generic as in original `generator` package and is, therefore, more
  prone to bugs.


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

*TO BE WRITTEN*


## Tips and tricks

* Since `iter2` is fully compatible with `generator`, they can be used
  interchangeably or even together, and will produce identical end
  results, save for any bugs.  Therefore, if you suspect a bug in
  `iter2`, try replacing `iter2-defun` with `iter-defun` in your
  generator definition.  Remember, though, that `generator` package
  also has bugs, e.g. [with variable rebindings][2].


[1]: https://en.wikipedia.org/wiki/Generator_(computer_programming)
[2]: https://debbugs.gnu.org/cgi/bugreport.cgi?bug=26073
