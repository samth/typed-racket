#lang typed/racket/shallow/base

;; For combinators don't need a codomain check,
;;  or a domain check on the `for-loop` functions
;;
;; Expand, look for:
;; - no "transient-assert" around the final result
;; - no domain "transient-assert" for any functions
;; - no transient-assert around unsafe-cdr

(void?
  (for ((x (in-list '(A B C))))
    x))

(list?
  (for/list : (Listof Symbol) ((x '(A B C)))
    x))

(list?
  (for/fold
            ((acc : (Listof Symbol) '()))
            ((x (in-list '(A B C))))
    (cons x acc)))

