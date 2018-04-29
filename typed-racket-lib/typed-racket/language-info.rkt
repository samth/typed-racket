#lang racket/base
(require typed-racket/typed-reader)
(provide get-info configure)

(define ((get-info arg) key default)
  (case key
    [(configure-runtime) `(#(typed-racket/language-info configure ',arg))]
    [else default]))

(define (configure options)
  (namespace-require 'racket/base)
  (define te-mode
    (cond
      [(memq 'deep options) 'guarded]
      [(memq 'shallow options) 'transient]
      [(memq 'optional options) 'erasure]
      [else 'guarded]))
  (eval `(begin
           (require (for-syntax typed-racket/utils/tc-utils racket/base))
           (begin-for-syntax
             (set-box! type-enforcement-mode ',te-mode)
             (set-box! typed-context? '#t)))
        (current-namespace))
  (current-readtable (readtable)))
