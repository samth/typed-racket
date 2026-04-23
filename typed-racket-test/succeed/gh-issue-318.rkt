#lang typed/racket

;; Issue #318: Regression test - previously caused internal error when overriding
;; a method that returns multiple values including 'this'.
;; This was fixed in an earlier version of Typed Racket.

(define atree%
  (class object%
    (super-new)
    (define/public (m)
      (values #f this))))

(define state%
  (class atree%
    (super-new)
    (define/override (m)
      (values #f this))))
