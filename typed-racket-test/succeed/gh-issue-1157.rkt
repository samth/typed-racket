#lang typed/racket

;; Issue #1157: Regression test - previously caused "define/match: no matching clause"
;; internal error when type checking case-> functions with keyword arguments.
;; Fixed by adding defensive patterns to add-unconditional-prop, add-unconditional-prop-all-args,
;; reduce-tc-results/subsumption, check-below, and type-table->tooltips.

(provide func)

(: func (case-> [-> #:bool True One]
                [-> #:bool False Zero]))
(define (func #:bool b)
  (cond [(eq? #t b) 1]
        [(eq? #f b) 0]))

;; Just defining and exporting the function validates that the type checker doesn't crash.
