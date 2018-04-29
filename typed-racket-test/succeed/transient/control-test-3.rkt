#lang racket/load

;; TODO 2021-09-13 should succeed, but fails because default-continuation-prompt-tag
;;  is always wrapped in a contract

(module untyped racket
  (provide call-f)

  (define (call-f f)
    (call-with-continuation-prompt
     (λ () (f 0))
     (default-continuation-prompt-tag)
     ;; this application should fail due to the any wrapping
     ;; for the TR function that's aborted here
     (λ (x) (x "string")))))

(module typed typed/racket/shallow
  (require/typed 'untyped
                 [call-f ((Integer -> Integer) -> Integer)])

  (call-f
   (λ: ([x : Integer])
     ;; this abort should wrap with an Any wrapper
     (abort-current-continuation
      (default-continuation-prompt-tag)
      (λ (x) x)))))

(require 'typed)
