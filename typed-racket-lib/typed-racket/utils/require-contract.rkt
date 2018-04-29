#lang racket/base

;; This module provides helper macros for `require/typed`

(require racket/contract/region racket/contract/base
         "transient-contract.rkt"
         syntax/location
         racket/syntax
         (for-syntax racket/base
                     syntax/parse
                     (only-in "tc-utils.rkt" current-type-enforcement-mode)))

(provide require/contract require/contract-transient require/contract-erasure define-ignored rename-without-provide)

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


;; Define a rename-transformer that's set up to avoid being provided
;; by all-defined-out or related forms.
(define-syntax (rename-without-provide stx)
  (syntax-parse stx
    [(_ nm:id hidden:id orig:id)
     #'(define-syntax nm
         (make-rename-transformer
          (syntax-property
           (syntax-property
            (syntax-property (quote-syntax hidden)
                             'not-free-identifier=? #t)
            'original-name
            (quote-syntax orig))
           'not-provide-all-defined #t)))]))

(begin-for-syntax
  (define-syntax-class renameable
    (pattern nm:id
             #:with orig-nm #'nm
             #:with orig-nm-r ((make-syntax-introducer) #'nm))
    (pattern (orig-nm:id nm:id)
             #:with orig-nm-r ((make-syntax-introducer) #'nm))))

;; Requires an identifier from an untyped module into a typed module
;; nm is the import
;; hidden is an id that will end up being the actual definition
;; nm will be bound to a rename transformer so that it is not provided
;; with all-defined-out
(define-syntax (require/contract stx)
  ;; define-syntax-class renameable
  (syntax-parse stx
    [(require/contract nm:renameable hidden:id cnt lib orig-ty-str)
     #`(begin (require (only-in lib [nm.orig-nm nm.orig-nm-r]))
              (rename-without-provide nm.nm hidden nm.orig-nm-r)

              (define-ignored hidden
                (contract cnt
                          #,(get-alternate #'nm.orig-nm-r)
                          '(interface for #,(syntax->datum #'nm.nm))
                          (current-contract-region)
                          (quote nm.nm)
                          (quote-srcloc nm.nm))))]))

;; TODO combine ^
(define-syntax (require/contract-transient stx)
  (syntax-parse stx
    [(_ nm:renameable hidden:id cnt lib orig-ty-str)
     #`(begin (require (only-in lib [nm.orig-nm nm.orig-nm-r]))
              (rename-without-provide nm.nm hidden nm.orig-nm-r)
              (define-ignored hidden
                (#%plain-app transient-assert #,(get-alternate #'nm.orig-nm-r) cnt 'orig-ty-str (quote-srcloc nm.nm))))]))

;; TODO combine ^^
(define-syntax (require/contract-erasure stx)
  (syntax-parse stx
    [(_ nm:renameable hidden:id cnt lib orig-ty-str)
     #`(begin (require (only-in lib [nm.orig-nm nm.orig-nm-r]))
              (rename-without-provide nm.nm hidden nm.orig-nm-r)
              (define-ignored hidden #,(get-alternate #'nm.orig-nm-r)))]))

;; identifier -> identifier
;; get the alternate field of the renaming, if it exists
(define-for-syntax (get-alternate id)
  (define-values (v new-id) (syntax-local-value/immediate id (λ _ (values #f #f))))
  (cond [(rename-transformer? v)
         (get-alternate (rename-transformer-target v))]
        [else id]))
