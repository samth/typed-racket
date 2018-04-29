#lang typed/racket/shallow/base

;; LD submodules in LD code

(module t typed/racket/shallow/base
  (: f (-> Real (-> Real Real) Real))
  (define (f r g)
    (g (g r)))
  (provide f))
(require 't)

(: h (-> Real Real))
(define (h n)
  (* n n))

(f 3 h)
