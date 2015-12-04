#lang racket/base

;; continuation-prompt-tag is unsafe!

(module u racket/base
  (require racket/control)
  (define (foo? x)
    (error 'pr241 "Continuation Prompt Tag allowed as 'Any'")
    (abort/cc x -1))
  (provide foo?))

(module t typed/racket/base
  (require/typed (submod ".." u)
    (#:opaque F foo?))

  (: tag (Prompt-Tagof Any (-> String Any)))
  (define tag (make-continuation-prompt-tag))

  (: handler (-> String Any))
  (define (handler str)
    (displayln (string-append "Something bad happened : " str))
    #f)

  (with-handlers ([exn:fail:contract? (lambda (e) (void))])
    (call-with-continuation-prompt
      (lambda () (foo? tag))
      tag handler))
)

(require 't)
