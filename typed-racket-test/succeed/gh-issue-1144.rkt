#lang typed/racket

;; Issue #1144: Referencing certain identifiers like exn:srclocs? previously
;; caused an internal "syntax-property: contract violation" error.
;; Now properly returns the procedure.

(ann exn:srclocs? (-> Any Boolean))
(ann rename-transformer? (-> Any Boolean))
(ann set!-transformer? (-> Any Boolean))
