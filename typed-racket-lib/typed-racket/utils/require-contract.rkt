#lang racket/base

;; This module provides helper macros for `require/typed`

(require racket/contract/region racket/contract/base
         syntax/location 
         (for-syntax racket/base racket/syntax
                     "../private/syntax-properties.rkt"
                     syntax/parse))

(provide require/contract define-ignored rename-without-provide)


(define-syntax (define-ignored stx)
  (syntax-case stx ()
    [(_ name expr)
     (syntax-case (local-expand/capture-lifts #'expr
                                              'expression
                                              null #;(list #'define-values))
       (begin define-values)
       [(begin (define-values (n) e) ... e*)
        #`(begin (define-values (n) e) ...
                 (define name #,(syntax-property #'e*
                                                 'inferred-name
                                                 (syntax-e #'name))))]
       [(begin e)
        #`(define name #,(syntax-property #'e
                                          'inferred-name
                                          (syntax-e #'name)))])]))
(require (for-syntax racket/pretty))
(define-syntax (really-ignore stx)
  (syntax-case stx ()
    [(_ e)
     (syntax-case (local-expand #'e (syntax-local-context) null) ()
       [(begin e ...)
        (pretty-print (syntax-e #'(e ...)))
         #`(begin #,@(map ignore (syntax-e #'(e ...))))])]))

;; Define a rename-transformer that's set up to avoid being provided
;; by all-defined-out or related forms.
(define-syntax (rename-without-provide stx)
  (syntax-parse stx
    [(_ nm:id hidden:id)
     #'(define-syntax nm
         (make-rename-transformer
          (syntax-property (syntax-property (quote-syntax hidden)
                                            'not-free-identifier=? #t)
                           'not-provide-all-defined #t)))]))

;; Requires an identifier from an untyped module into a typed module
;; nm is the import
;; hidden is an id that will end up being the actual definition
;; nm will be bound to a rename transformer so that it is not provided
;; with all-defined-out
(define-syntax (require/contract stx)
  (define-syntax-class renameable
    (pattern nm:id
             #:with orig-nm #'nm
             #:with orig-nm-r ((make-syntax-introducer) #'nm))
    (pattern (orig-nm:id nm:id)
             #:with orig-nm-r ((make-syntax-introducer) #'nm)))

  (syntax-parse stx
    [(require/contract nm:renameable cnt lib)
     (define/with-syntax fresh (generate-temporary))
      #`(begin
         #;
         (module submodule-name racket/base
           (require
             (submod typed-racket/private/type-contract predicates)
             typed-racket/utils/utils
             (for-syntax typed-racket/utils/utils)
             typed-racket/utils/any-wrap typed-racket/utils/struct-type-c
             typed-racket/utils/opaque-object
             typed-racket/utils/evt-contract
             typed-racket/utils/sealing-contract
             typed-racket/utils/promise-not-name-contract
             racket/sequence
             racket/contract/parametric)
           (require (only-in lib [nm.orig-nm nm.orig-nm-r]))
           (provide (contract-out [rename #,(get-alternate #'nm.orig-nm-r) hidden cnt])))
         ;(require (only-in 'submodule-name hidden))
         
         (require (only-in lib [nm.orig-nm nm.orig-nm-r]))
         (rename-without-provide nm.nm hidden)

         (define-module-boundary-contract fresh
           #,(get-alternate #'nm.orig-nm-r)
           cnt
           #:pos-source '(interface for #,(syntax->datum #'nm.nm))
           #:srcloc (quote-srcloc nm.nm)
           #:hidden-id #,(ignore #'hidden) #,(ignore #'hidden-extra))
         #;
         (define-ignored hidden
           (contract cnt
                     #,(get-alternate #'nm.orig-nm-r)
                     '(interface for #,(syntax->datum #'nm.nm))
                     (current-contract-region)
                     (quote nm.nm)
                     (quote-srcloc nm.nm))))]))

;; identifier -> identifier
;; get the alternate field of the renaming, if it exists
(define-for-syntax (get-alternate id)
  (define-values (v new-id) (syntax-local-value/immediate id (λ _ (values #f #f))))
  (cond [(rename-transformer? v)
         (get-alternate (rename-transformer-target v))]
        [else id]))
