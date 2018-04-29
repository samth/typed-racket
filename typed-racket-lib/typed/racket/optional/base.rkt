#lang racket/base

(require
  (only-in racket/require subtract-in)
  (for-syntax racket/base)
  (subtract-in
    (except-in typed/racket/base
               #%module-begin #%top-interaction with-type with-type-shallow)
    (submod typed-racket/base-env/prims-contract forms))
  (only-in (submod typed-racket/base-env/prims-contract forms-optional)
           (require-typed-signature-erasure require-typed-signature)
           (require/opaque-type-erasure require/opaque-type)
           (require-typed-struct-legacy-erasure require-typed-struct-legacy)
           (require-typed-struct-erasure require-typed-struct)
           (require/typed-legacy-erasure require/typed-legacy)
           (require/typed-erasure require/typed)
           (require/typed/provide-erasure require/typed/provide)
           (require-typed-struct/provide-erasure require-typed-struct/provide)
           (cast-erasure cast)
           (make-predicate-erasure make-predicate)
           (define-predicate-erasure define-predicate))
  (only-in typed/racket/base
           [#%module-begin --#%module-begin]
           [#%top-interaction --#%top-interaction]))

(provide
  (all-from-out typed/racket/base)
  (all-from-out (submod typed-racket/base-env/prims-contract forms-optional))
  with-type
  (rename-out [-#%module-begin #%module-begin] [-#%top-interaction #%top-interaction]))

(define-syntax (-#%module-begin stx)
  (quasisyntax/loc stx (--#%module-begin #:optional . #,(cdr (syntax-e stx)))))

(define-syntax (-#%top-interaction stx)
  (quasisyntax/loc stx (--#%top-interaction #:optional . #,(cdr (syntax-e stx)))))

(define-syntax (with-type stx)
  (quasisyntax/loc stx (with-type-optional . #,(cdr (syntax-e stx)))))

