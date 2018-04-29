#lang racket/load

(require typed/racket/shallow)

(define-predicate p? (All (A) (Listof A)))

(let ()
  (: x (U (Listof Integer) Integer)) (define x '(1 2 3))
  (if (p? x) (car x) 0))
