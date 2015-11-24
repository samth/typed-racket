#lang racket/base

;; Namespace anchors should not be passed as 'Any'
;; Neither should variable references

(module u racket/base
  (define (trustme? x)
    (define ns
      (cond
       [(namespace-anchor? x)
        (namespace-anchor->namespace x)]
       [(variable-reference? x)
        (variable-reference->namespace x)]
       [else (error 'pr241 "Unexpected argument in unit test")]))
    (eval '(set-box! secret-box (void)) ns)
    #t)
  (provide trustme?))

(module t typed/racket/base
  (require/typed (submod ".." u)
    [#:opaque T trustme?])
  (: secret-box (Boxof Integer))
  (define secret-box (box 2))

  (define-namespace-anchor nsa)
  (with-handlers ([exn:fail:contract? (lambda (x) (void))])
    (trustme? nsa)
    (error 'pr241 "Allowed namespace anchor as Any"))

  (define vr (#%variable-reference secret-box))
  (with-handlers ([exn:fail:contract? (lambda (x) (void))])
    (trustme? vr)
    (error 'pr241 "Allowed variable-reference as Any")))

(require 't)
