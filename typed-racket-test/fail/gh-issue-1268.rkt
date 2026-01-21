#;
(exn-pred #rx"Inference for polymorphic keyword functions not supported")
#lang typed/racket

;; Issue #1268: hash-union with #:combine previously caused an internal
;; match-define error. Fixed to give a proper type error about polymorphic
;; keyword function inference.

(require racket/hash)

(hash-union (make-hash) (make-hash) #:combine (lambda (a b) a))
