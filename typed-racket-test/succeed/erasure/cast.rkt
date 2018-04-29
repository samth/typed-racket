#lang typed/racket/optional

(define-predicate p? (All (A) (Listof A)))
(require/typed racket/base
  [object-name (-> (U (Listof Real) Regexp)
                   (U String Bytes Symbol))])
(object-name #rx"a regexp")
(object-name (cast '(A B C) (Listof Real)))

