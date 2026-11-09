#;
(exn-pred #rx"'results")
#lang typed/racket

;; A thread that keeps a result is not a `Thread`, whose `thread-wait`
;; produces `(void)`.
(ann (thread (λ () 5) #:keep 'results) Thread)
