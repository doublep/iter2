#! /usr/bin/env bash

set -e

if [ -z "$EMACS" ] ; then
    EMACS=emacs
fi

if [ -z "$ERT_SELECTOR" ] ; then
    ERT_SELECTOR=t
fi

if [ "$ITER2_DEBUG" != "t" ] ; then
    ITER2_DEBUG=nil
fi

$EMACS -batch                                                           \
       --eval "(message \"Using Emacs %s\" (emacs-version))"            \
       -l iter2.el                                                      \
       -l test/iter2-test.el                                            \
       --execute "(let ((ert-quiet t))                                  \
                    (iter2--debug-converter $ITER2_DEBUG)               \
                    (ert-run-tests-batch-and-exit (quote ${ERT_SELECTOR})))"

$EMACS -Q --batch                                                       \
       --eval "(setq byte-compile-error-on-warn t)"                     \
       --eval "(batch-byte-compile)" iter2.el
