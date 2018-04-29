#;
(exn-pred exn:fail:contract? #rx"car")

#lang typed/racket/optional/base

(require/typed racket/base
  (cdr (All (A) A)))

(let ((v : (Pairof String String)
       (inst cdr (Pairof String String))))
  (car v))

