#;
(exn-pred #rx"Threadof")
#lang typed/racket

;; The results of a thread from untyped code cannot be checked.
(require/typed racket/base [current-thread (-> (Threadof Integer))])
