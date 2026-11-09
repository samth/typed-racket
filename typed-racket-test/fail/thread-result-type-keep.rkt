#;
(exn-pred #rx"Expected result: Integer")
#lang typed/racket

;; A thread that keeps its results may also end abnormally, in which
;; case `thread-wait` calls the default failure thunk, `void`.
(: t (Threadof Integer))
(define t (thread (λ () 5) #:keep 'results))
(ann (thread-wait t) Integer)
