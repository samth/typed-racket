#;
(exn-pred #rx"row type variable used in invalid position")
#lang typed/racket

;; Issue #1146: Row type variables should only appear in (Class #:row-var ...),
;; not directly as types like (-> r r). Previously this caused internal errors;
;; now it produces a proper type error.

(: hi (All (r #:row)
           (-> r r)))
(define (hi a)
  a)
