#lang typed/racket

;; Issue #229: Typed units with signatures from submodules previously
;; caused a "free-id-table-ref: contract violation" internal error.
;; Now type checks correctly.

(module a typed/racket
  (provide foo^)

  (define-signature foo^
    ([some-class% : ClassTop])))

(require 'a)

(define-unit foo@
  (import)
  (export foo^)

  (define some-class%
    (class object%
      (super-new))))
