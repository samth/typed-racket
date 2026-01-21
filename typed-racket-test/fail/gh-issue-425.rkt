#;
(exn-pred #rx"cannot apply a non-polymorphic type")
#lang typed/racket

;; Issue #425: Regression test - previously caused internal error
;; "Base type L+ not in predefined-type-table" when using recursive
;; type definitions with intersection types incorrectly.

(define-type (L+ T REST) (Pairof T (∩ (L+ T Any) REST)))
