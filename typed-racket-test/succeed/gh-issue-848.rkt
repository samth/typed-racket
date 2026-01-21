#lang typed/racket/base

;; Issue #848: Regression test - previously caused car: contract violation
;; with recursive case-> types during contract generation.
;; Fixed by adding null checks in compute-defs in static-contracts/instantiate.rkt

(provide
 new-T
 consume-T)

(define-type T
  (case->
   ['a -> Any]
   ['b -> (-> T)]))

(: new-T : -> T)
(define (new-T) (new-T))

(: consume-T : T -> Nothing)
(define (consume-T t) (consume-T t))
