#lang racket

;; Issue #858: Previously caused "recursive-contract: contract violation"
;; with recursive types. Fixed by null checks in compute-defs.

(module a typed/racket
  (define-type T (Rec T (-> (U T String))))
  (provide f)
  (: f (-> T T))
  (define (f x) x))

(require 'a)
(f (lambda () ""))
