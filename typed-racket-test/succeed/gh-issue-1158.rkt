#lang typed/racket/base

;; Issue #1158: Regression test - previously caused car: contract violation
;; during contract generation with recursive MListof.
;; Fixed by adding null checks in compute-defs in static-contracts/instantiate.rkt

(provide func-1 func-2)

(define-type MNulls (MListof MNulls))

(: func-1 [-> MNulls Any]) (define (func-1 ns) 1)
(: func-2 [-> MNulls Any]) (define (func-2 ns) 2)

(displayln (func-1 '()))
(displayln (func-2 '()))
