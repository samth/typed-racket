#lang typed/racket/optional/base

(require typed/rackunit)

(check-not-exn
  (lambda ()
    (cast (lambda () 3) (-> String))))

(check-not-exn
  (lambda ()
    ((cast (lambda () 3) (-> String)))))

