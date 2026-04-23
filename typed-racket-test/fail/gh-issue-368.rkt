#;
(exn-pred #rx"broke its own contract")
#lang typed/racket

;; Issue #368: cast with wrong type previously threw an internal error
;; "procedure-arity: contract violation" instead of a proper contract failure.

(cast 3 (-> Integer Integer))
