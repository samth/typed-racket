#lang typed/racket/base/shallow

;; List? should expand to a check for `(and/c list? len=2)`
;; Vector? should expand to a check for `vector?`
;;
;; search for `List?` and `Vector?`, looking for a define-values

(define-type Big-T (List (Listof Integer) (List Symbol Integer Integer)))
(define-predicate List? Big-T)

(define-predicate Vector? (Vectorof Big-T))

(: g (-> Any (U #f Big-T)))
(define (g y)
  (if (List? y)
    y
    #f))

(void
  (Vector? 4))
