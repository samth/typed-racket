#;
(exn-pred exn:fail:contract? #rx"transient-assert" )

#lang typed/racket/base/shallow

(require typed/rackunit)

(check-not-exn
  (lambda ()
    (cast (lambda () 3) (-> String))))

((cast (lambda () 3) (-> String)))

