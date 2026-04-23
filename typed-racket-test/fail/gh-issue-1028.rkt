#;
(exn-pred #rx"expected single value, got multiple")
#lang typed/racket

;; Issue #1028: Incorrect with-handlers usage previously caused an internal
;; typechecker error "get-range-result: should not happen". Fixed to give
;; a proper type error about expecting single value.

(with-handlers ([exn:fail? (values #f #f)]) (values #t #t))
