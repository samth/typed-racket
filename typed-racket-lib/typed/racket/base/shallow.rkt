#lang racket/base

(require
  (only-in racket/require subtract-in)
  (for-syntax racket/base)
  typed-racket/utils/transient-contract ;; needed for eval, see test in succeed/transient/scribble-example.rkt
  (subtract-in
    (except-in typed/racket/base
               #%module-begin #%top-interaction with-type with-type-optional)
    (submod typed-racket/base-env/prims-contract forms))
  (only-in (submod typed-racket/base-env/prims-contract forms-shallow)
           (require-typed-signature-transient require-typed-signature)
           (require/opaque-type-transient require/opaque-type)
           (require-typed-struct-legacy-transient require-typed-struct-legacy)
           (require-typed-struct-transient require-typed-struct)
           (require/typed-legacy-transient require/typed-legacy)
           (require/typed-transient require/typed)
           (require/typed/provide-transient require/typed/provide)
           (require-typed-struct/provide-transient require-typed-struct/provide)
           (cast-transient cast)
           (make-predicate-transient make-predicate)
           (define-predicate-transient define-predicate))
  (only-in typed/racket/base
           [#%module-begin --#%module-begin]
           [#%top-interaction --#%top-interaction]))

(provide
  (all-from-out typed/racket/base)
  (all-from-out (submod typed-racket/base-env/prims-contract forms-shallow))
  with-type
  (rename-out [-#%module-begin #%module-begin] [-#%top-interaction #%top-interaction]))

(define-syntax (-#%module-begin stx)
  (quasisyntax/loc stx (--#%module-begin #:shallow . #,(cdr (syntax-e stx)))))

(define-syntax (-#%top-interaction stx)
  (quasisyntax/loc stx (--#%top-interaction #:shallow . #,(cdr (syntax-e stx)))))

(define-syntax (with-type stx)
  (quasisyntax/loc stx (with-type-shallow . #,(cdr (syntax-e stx)))))

