#lang typed/racket

;; Issue #378: cast in dead code previously caused an internal error
;; "contract-def-property: thunk called too early". Now works correctly.

(define result
  (cond [#false (cast 1 Integer)]
        [else 2]))

(unless (= result 2)
  (error "expected 2"))
