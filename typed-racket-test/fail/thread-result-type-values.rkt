#;
(exn-pred #rx"thread")
#lang typed/racket

;; A typed thread may keep only a single result.
(thread (λ () (values 1 2)) #:keep 'results)
