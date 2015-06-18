#lang racket/base

(require "../utils/utils.rkt"
         racket/match racket/set
         (contract-req)
         (rep object-rep type-rep filter-rep rep-utils)
         (utils tc-utils)
         (typecheck renamer)
         (types subtype resolve union remove-intersect numeric-tower)
         (except-in (types utils abbrev kw-types) -> ->* one-of/c))

(provide/cond-contract
 [id-ty+path->obj-ty (Type/c (listof PathElem?) . -> . Type/c)]
 [try/obj-ty+path->ty ((Type/c (listof PathElem?) #:fail-type Type/c)
                              . ->* . Type/c)]
 [try/obj-ty+rev-path->ty ((Type/c (listof PathElem?) (listof PathElem?) #:fail-type fail-type)
                                  . ->* . Type/c)])

(define empty-resolved-set (set))

;; returns the result of following a path into a type
;; (Listof PathElem) Type -> Type
;; Ex. '(CarPE) (Pair α β) (-acc-path (list -len))-> α
;; resolved is the set of resolved types so far at a particular
;; path - it ensures we are making progress, that we do not
;; continue unfolding types infinitely while not progressing.
;; It is intentionally reset each time we decrease the
;; paths size on a recursive call, and maintained/extended
;; when the path does not decrease on a recursive call.
(define (id-ty+path->obj-ty t path)
  (id-ty+rev-path->obj-ty t (reverse path) empty-resolved-set))

(define (id-ty+rev-path->obj-ty t reversed-path resolved)
  (define-values (path-elem rst)
    (match reversed-path
      [(cons h t) (values h t)]
      [_ (values #f #f)]))
  (match t
    ;; empty path
    [_ #:when (not path-elem)
       t]
    
    ;; pair ops
    [(Pair: a _) #:when (CarPE? path-elem)
                 (id-ty+rev-path->obj-ty a rst resolved)]
    [(Pair: _ d) #:when (CdrPE? path-elem)
                 (id-ty+rev-path->obj-ty d rst resolved)]
    
    ;; syntax ops
    [(Syntax: t) #:when (SyntaxPE? path-elem)
                 (id-ty+rev-path->obj-ty t rst resolved)]
    
    ;; promise op
    [(Promise: t) #:when (ForcePE? path-elem)
                  (id-ty+rev-path->obj-ty t rst resolved)]
    
    ;; struct ops
    [(Struct: nm par flds proc poly pred)
     #:when (and (StructPE? path-elem)
                 (match path-elem
                   [(StructPE: (? (λ (s) (subtype t s)) s) _) #t]
                   [_ #f]))
     (match-let* ([(StructPE: _ idx) path-elem]
                  [(fld: ft _ _) (list-ref flds idx)])
       (id-ty+rev-path->obj-ty ft rst resolved))]
    
    [(Union: ts)
     (apply Un (map (λ (t) (id-ty+rev-path->obj-ty t reversed-path resolved)) ts))]
    
    ;; paths into polymorphic types
    [(Poly: _ body-t) (id-ty+rev-path->obj-ty body-t reversed-path resolved)]
    [(PolyDots: _ body-t) (id-ty+rev-path->obj-ty body-t reversed-path resolved)]
    [(PolyRow: _ _ body-t) (id-ty+rev-path->obj-ty body-t reversed-path resolved)]
    
    ;; for private fields in classes
    [(Function: (list (arr: doms (Values: (list (Result: rng _ _))) _ _ _ _)))
     #:when (FieldPE? path-elem)
     (id-ty+rev-path->obj-ty rng rst resolved)]
    
    ;; types which need resolving
    [(? needs-resolving?)
     #:when (not (set-member? resolved (cons reversed-path t)))
     (id-ty+rev-path->obj-ty (resolve-once t) reversed-path (set-add resolved (cons reversed-path t)))]
    
    ;; length ops
    [vt #:when (and (LengthPE? path-elem)
                    (overlap vt -VectorTop))
        -Nat]
    
    ;; type/path mismatch =(
    [_ Err]))


;; try/obj-ty+path->ty
;; takes a path and a type and builds up the type from 'unwrapping'
;; the path. Ex: (car cdr) String --> (Pairof (Pairof Any String) Any)
;; WARNING - this is best effort, but currently cannot rebuild *any* type
;; from a path (FIXME make it work for any type/path combo?)
;; NOTE: path is reversed (so we're not continually matching on the last
;; element of a list) -- i.e. for caddr we would expect reversed-path
;; to equal '(cdr cdr car)
(define (try/obj-ty+path->ty t path #:fail-type fail-type)
  (try/obj-ty+rev-path->ty t (reverse path) #:fail-type fail-type))

(define (try/obj-ty+rev-path->ty t reversed-path #:fail-type fail-type)
  (define-values (hd rst)
    (match reversed-path
      [(cons h t) (values h t)]
      [_ (values #f #f)]))
  
  (match hd
    ;; empty path
    [#f t]
    
    ;; pair ops
    [(CarPE:)
     (define a (try/obj-ty+rev-path->ty t rst #:fail-type fail-type))
     (-pair a Univ)]
    [(CdrPE:)
     (define d (try/obj-ty+rev-path->ty t rst #:fail-type fail-type))
     (-pair Univ d)]
    
    ;; syntax ops
    [(SyntaxPE:)
     (-Syntax (try/obj-ty+rev-path->ty t rst #:fail-type fail-type))]
    
    ;; promise op
    [(ForcePE:)
     (-Promise (try/obj-ty+rev-path->ty t rst #:fail-type fail-type))]
    
    ;; struct ops
    #;[(StructPE: (? (λ (s) (subtype t s)) s) idx)
       ;TODO(amk) punt for now! support later?
       (int-error "nope - not supported! Hey, who uncommented this!?")]
    
    ;; default to specified fail-type (since this function supports claims about negative types
    ;; (at least it does right now...)
    [_ fail-type]))

