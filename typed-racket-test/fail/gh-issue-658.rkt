#;
(exn-pred #rx"cannot apply a non-polymorphic type")
#lang typed/racket

;; Issue #658: Invalid *-> type previously caused an internal error
;; "erroneous syntax was not a syntax object". Fixed to give a proper
;; type error about applying a non-polymorphic type.

(struct Node [{reachable : Edge}])
(struct Edge [{to : Symbol} {cost : Positive-Integer}])

(define-type Graph [Immutable-HashTable Symbol Node])

(: make-graph (Node *-> Graph))
(define (make-graph . lo-node)
  (make-immutable-hash))
