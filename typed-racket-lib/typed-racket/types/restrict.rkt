#lang racket/base

(require (except-in "../utils/utils.rkt" infer)
         (utils tc-utils)
         (rep type-rep rep-utils)
         (types abbrev base-abbrev union subtype remove-intersect resolve refine)
         racket/match racket/lazy-require
         (rename-in racket/contract [-> c:->] [->* c:->*] [one-of/c c:one-of/c])
         racket/set)

(provide restrict restrict/notify)

(lazy-require
 ["../infer/infer.rkt" (infer)])

(define/cond-contract (restrict old-ty new-ty)
  (c:-> Type? Type? Type?)
  (define/cond-contract (dummy-notify old-t new-t lope)
    (c:-> Type/c Type/c (or/c #f (listof PathElem?)) Type/c)
    new-t)
  (restrict/notify old-ty new-ty #f dummy-notify))

;; restrict old-ty to be a subtype of new-ty
;; track the path we're traversed to get here
;; notify when an update could have produced
;; an interesting result (Refinement, integer type
;; with bounds associated, etc)
(define/cond-contract (restrict/notify old-ty new-ty path-stack notify)
  (c:-> Type?
      Type?
      (or/c #f (listof PathElem?))
      (c:-> Type/c Type/c (or/c #f (listof PathElem?)) Type/c)
      Type?)
  ;; build-type: build a type while propogating bottom
  (define/cond-contract (build-type constructor . args)
    (c:->* (procedure?) () #:rest (cons/c Type/c (listof Type/c))
           Type/c)
    (if (memf Bottom? args) -Bottom (apply constructor args)))
  ;; resolved is a set tracking previously seen restrict cases
  ;; (i.e. pairs of t1 t2) to prevent infinite unfolding.
  ;; subtyping performs a similar check for the same
  ;; reason
  (define/cond-contract (restrict* old-ty new-ty resolved path-stack)
    (c:-> Type/c Type/c set? (or/c #f (listof PathElem?))
          Type/c)
    (define (push pe)
      (and path-stack (cons pe path-stack)))
    (match* (old-ty new-ty)
      ;; already a subtype
      [(_ _)
       #:when (subtype old-ty new-ty) 
       old-ty]
      
      ;; polymorphic restrict
      [(_ (Poly: vars t))
       #:when (infer vars null (list old-ty) (list t) #f)
       old-ty]
      
      ;; structural recursion on types
      [((Pair: a1 d1) (Pair: a2 d2))
       (define a (restrict* a1 a2 resolved (push -car)))
       (define d (restrict* d1 d2 resolved (push -cdr)))
       (when (not (Type? a))
         (error 'restrict* "WTF NOT A TYPE 1!!! ~a" a))
       (when (not (Type? d))
         (error 'restrict* "WTF NOT A TYPE 2!!! ~a" a))
       (build-type -pair a d)]
      ;; FIXME: support structural updating for structs when structs are updated to
      ;; contain not only *if* they are polymorphic, but *which* fields are too  
      ;;[((Struct: _ _ _ _ _ _)
      ;; (Struct: _ _ _ _ _ _))]
      [((Syntax: t1*) (Syntax: t2*))
       (build-type -Syntax (restrict* t1* t2* resolved (push -syntax-e)))]
      [((Promise: t1*) (Promise: t2*))
       (build-type -Promise (restrict* t1* t2* resolved (push -force)))]
      
      ;; unions
      [((Union: t1s) _)
       (notify old-ty (apply Un (map (λ (t1*) (restrict* t1* new-ty resolved #f)) t1s)) path-stack)]
      [(_ (Union: t2s))
       (notify old-ty (apply Un (map (λ (t2*) (restrict* old-ty t2* resolved #f)) t2s)) path-stack)]
      
      ;; resolve resolvable types if we haven't already done so
      [((? needs-resolving?) _)
       #:when (not (set-member? resolved (cons old-ty new-ty)))
       (restrict* (resolve old-ty) new-ty (set-add resolved (cons old-ty new-ty)) path-stack)]
      [(_ (? needs-resolving?))
       #:when (not (set-member? resolved (cons old-ty new-ty)))
       (restrict* old-ty (resolve new-ty) (set-add resolved (cons old-ty new-ty)) path-stack)]
      
      ;; we don't actually want this - want something that's a part of t1
      [(_ _)
       #:when (subtype new-ty old-ty)
       (notify old-ty new-ty path-stack)]

      [((Refine-unsafe: rt rp) _)
       (notify old-ty (unsafe-make-Refine* (restrict* rt new-ty resolved path-stack) rp) path-stack)]
      
      [(_ (Refine-unsafe: rt rp))
       (unsafe-make-Refine* (restrict* old-ty rt resolved path-stack) rp)]
      
      ;; there's no overlap, so the restriction is empty
      [(_ _) #:when (not (overlap old-ty new-ty)) 
             (Un)]
      
      ;; t2 and t1 have a complex relationship, so we punt
      [(_ _)
       (notify old-ty new-ty path-stack)]))
  
  (restrict* old-ty new-ty (set) path-stack))
