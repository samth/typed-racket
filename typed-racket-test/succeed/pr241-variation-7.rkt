#lang racket/base

;; Continuation Mark Sets are unsafe

(module u racket/base
  (define (trustme? x)
    (define v
      (if (pair? x)
        (continuation-mark-set-first (car x) (cdr x))
        (continuation-mark-set-first (current-continuation-marks) x)))
    (set-box! v (void))
    #t)
  (provide trustme?))

(module t typed/racket/base
  (require/typed (submod ".." u)
    [#:opaque T trustme?])

  (: secret-key (Continuation-Mark-Keyof (Boxof Integer)))
  (define secret-key (make-continuation-mark-key))
  (: secret-val (Boxof Integer))
  (define secret-val (box 2))

  (with-handlers ([exn:fail:contract? (lambda (x) (void))])
    (define marks
      (with-continuation-mark secret-key secret-val
        (current-continuation-marks)))
    (trustme? (cons marks secret-key))
    (error 'pr241 "Continuation-Mark-Set allowed as Any"))

  (with-handlers ([exn:fail:contract? (lambda (x) (void))])
    (with-continuation-mark secret-key secret-val
      (trustme? secret-key))
    (error 'pr241 "Continuation-Mark-Key allowed as Any")))

(require 't)
