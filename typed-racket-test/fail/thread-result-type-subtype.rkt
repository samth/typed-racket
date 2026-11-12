#;
(exn-pred #rx"'results")
#lang typed/racket

;; A thread that keeps a result does not produce `(void)`.
(ann (thread (λ () 5) #:keep 'results) (Threadof Void))
