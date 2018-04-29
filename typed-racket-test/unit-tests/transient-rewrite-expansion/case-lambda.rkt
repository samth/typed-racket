#lang typed/racket/shallow/base

;; Check that things are defended
;; - transient-assert x symbol? in f0
;; - transient-assert 2x that y and z are Nothing

(: f0 (case-> (-> Symbol Symbol)))
(define f0
  (case-lambda
    [(x) x]))

(f0 'x)
((case-lambda [(x) x]) 'x)
((case-lambda [(x) x] [(y z) z]) 'x)
