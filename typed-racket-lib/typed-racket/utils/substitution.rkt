#lang racket/base

(require racket/lazy-require)

(lazy-require
 ("../typecheck/tc-subst.rkt" (subst-type)))

(provide subst-type)