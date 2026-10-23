#lang racket/base

(require (for-syntax racket/base syntax/parse/pre
                     "../private/parse-classes.rkt"
                     "../utils/disappeared-use.rkt"
                     "../utils/utils.rkt"
                     (only-in "../utils/tc-utils.rkt" tc-error/stx))
         (submod "../typecheck/internal-forms.rkt" forms)
         (prefix-in t: "base-types-extra.rkt"))

(provide :)

(begin-for-syntax
 (define (err stx str . sub)
   (apply raise-syntax-error '|type declaration| str stx sub))

 ;; Wrap the `:-helper` use with a `define-values`. This is like
 ;; what `internal` does, but the work is spread out among two
 ;; macros to delay the unbound identifier check. When expanding
 ;; directly in an internal-definition body, the `:-helper` use is
 ;; instead lifted to the start of the body's expressions (like
 ;; `internal/lift`), so that the declaration does not prevent
 ;; splitting the body's definitions into `let-values` forms.
 (define (wrap stx top-level? . args)
   (cond
     [(and (not top-level?) (syntax-transforming-with-body-lifts?))
      (syntax-local-lift-body-expression
       (quasisyntax/loc stx (:-helper #,stx #f #t #,@args)))
      (syntax/loc stx (begin))]
     [else
      (quasisyntax/loc stx
        (define-values () (:-helper #,stx #,top-level? #f #,@args)))])))

(define-syntax (: stx)
  (define ctx (syntax-local-context))
  (define top-level? (eq? 'top-level ctx))
  ;; make it possible to add another colon after the id for clarity
  ;; and in that case, a `->' on the RHS does not need to be
  ;; explicitly parenthesized
  (syntax-parse stx #:literals (: t:->)
    [_
     #:when (eq? 'expression ctx)
     (err stx "must be used in a definition context")]
    [(: id (~and kw :) . more:omit-parens)
     (add-disappeared-use (syntax-local-introduce #'kw))
     (wrap stx top-level? #'id #'more.type)]
    [(: e ...)
     (apply wrap stx top-level? (syntax->list #'(e ...)))]))

(define-syntax (:-helper stx)
  (syntax-parse stx
    [(_ orig-stx top-level? lifted? i ty)
     #:fail-unless (identifier? #'i) (err #'orig-stx "expected identifier" #'i)
     (unless (or (syntax-e #'top-level?)
                 (identifier-binding #'i))
       (tc-error/stx #'i
                     "Declaration for `~a' provided, but `~a' has no definition"
                     (syntax-e #'i)
                     (syntax-e #'i)))
     (syntax-property (if (syntax-e #'lifted?)
                          ;; lifted to the start of a body's expressions
                          (syntax/loc stx (quote-syntax (:-internal i ty) #:local))
                          ;; right-hand side of `(define-values () ....)`
                          (syntax/loc stx (begin (quote-syntax (:-internal i ty) #:local)
                                                 (#%plain-app values))))
                      'disappeared-use (syntax-local-introduce #'i))]
    [(_ orig-stx _ _ i x ...)
     #:fail-unless (identifier? #'i) (err #'orig-stx "expected identifier" #'i)
     (case (syntax-length #'(x ...))
       [(0)  (err #'orig-stx "missing type after identifier")]
       [else (err #'orig-stx "too many types after identifier")])]))

