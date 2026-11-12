#;
(exn-pred #rx"thread")
#lang typed/racket

;; A `#:keep` argument that might be `'results` also requires an
;; immutable first-order result.
(define (start [keep : (U #f 'results)])
  (thread (λ () (box 5)) #:keep keep))
