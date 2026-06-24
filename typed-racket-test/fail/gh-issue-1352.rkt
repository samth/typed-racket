#;
(exn-pred #rx"struct property has no predicate")
#lang typed/racket

;; Issue #1352: syntax-property: contract violation with Has-Struct-Property
;; Bug in type-contract.rkt has-struct-property->sc function

(require/typed racket/stream
  [prop:stream (Struct-Property Any)]
  [stream->list (-> (Has-Struct-Property prop:stream) (List Any))])
