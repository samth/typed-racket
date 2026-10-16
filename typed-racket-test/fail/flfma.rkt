#;
(exn-pred #rx"expected: Flonum")
#lang typed/racket/base
(require racket/flonum)
(flfma 1 2.0 3.0)
