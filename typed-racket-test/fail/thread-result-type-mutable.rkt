#;
(exn-pred #rx"thread")
#lang typed/racket

;; Untyped code can wait for any thread's results, so a typed thread may
;; not keep a mutable result.
(thread (λ () (box 5)) #:keep 'results)
