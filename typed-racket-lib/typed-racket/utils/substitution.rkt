#lang racket/base

(require racket/lazy-require)

(lazy-require
 ("../typecheck/tc-subst.rkt" (subst-type subst-result)))

(provide subst-type subst-result)