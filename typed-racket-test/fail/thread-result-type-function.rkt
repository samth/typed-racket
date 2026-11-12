#;
(exn-pred #rx"thread")
#lang typed/racket

;; Untyped code can wait for any thread's results, so a typed thread may
;; not keep a function.
(thread (λ () add1) #:keep 'results)
