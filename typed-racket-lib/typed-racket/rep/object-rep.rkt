#lang racket/base

;; Representation of "objects" --- these describe the
;; part of an environment that an expression accesses
;;
;; See "Logical Types for Untyped Languages" pg.3

(require "rep-utils.rkt" 
         "free-variance.rkt" 
         "../utils/utils.rkt"
         "fme.rkt"
         (except-in racket/contract one-of/c)
         racket/match racket/dict racket/list racket/function
         racket/lazy-require racket/set
         (contract-req)
         (for-syntax racket/base)
         (utils tc-utils))

(lazy-require
 ["../types/abbrev.rkt" (-id-path)]
 ["filter-rep.rkt" (hash-name name-ref/c)])

(provide object-equal?
         LExp?
         LExp-path-map
         LExp-paths
         LExp-add1
         LExp-simple?
         LExp-has-path?
         LExp->sexp
         -lexp
         constant-LExp?
         non-empty-obj?
         immutable-path-set?
         empty-path-set
         (rename-out [LExp:* LExp:]
                     [LExp: LExp-raw:]
                     [LExp-terms* LExp-terms])
         -obj+
         -obj*)

(def-pathelem CarPE () [#:fold-rhs #:base])
(def-pathelem CdrPE () [#:fold-rhs #:base])
(def-pathelem SyntaxPE () [#:fold-rhs #:base])
(def-pathelem ForcePE () [#:fold-rhs #:base])
;; t is always a Name (can't put that into the contract b/c of circularity)
(def-pathelem StructPE ([t Type?] [idx natural-number/c])
  [#:frees (λ (f) (f t))]
  [#:fold-rhs (*StructPE (type-rec-id t) idx)])
;; TODO(amk) add type so length can access lists
(def-pathelem LengthPE () [#:fold-rhs #:base])
(def-pathelem FieldPE () [#:fold-rhs #:base])

(def-object Empty () [#:fold-rhs #:base])
(define -empty-obj (*Empty))
(def-object Path ([p (listof PathElem?)] [v name-ref/c])
  [#:intern (list (map Rep-seq p) (hash-name v))]
  [#:frees (λ (f) (combine-frees (map f p)))]
  [#:fold-rhs (*Path (map pathelem-rec-id p) v)])


;; represents no info about the object of this expression
;; should only be used for parsing type annotations and expected types
(def-object NoObject () [#:fold-rhs #:base])

(define/cond-contract (object-equal? o1 o2)
  (Object? Object? . -> . boolean?)
  (= (Obj-seq o1) (Obj-seq o2)))

(define-custom-set-types path-set
  object-equal?
  Obj-seq)
(define empty-path-set (make-immutable-path-set))

#;(define (intern-lexp exp)
  (match exp
    [(lexp: const terms)
     (cons const (sort (hash->list terms) < #:key car))]
    [_ (int-err "cannot intern invalid LExp (given bad lexp?) ~a" exp)]))
;; *****************************************************************************
;; Linear Expressions and related operations

(def-object LExp ([paths immutable-path-set?] 
                  [exp lexp?])
  #:no-provide
  [#:intern exp]
  [#:frees (λ (f) (combine-frees (set-map paths f)))]
  [#:fold-rhs ;; warning - this returns Empty if any subterm is converted to Empty
   (internal-lexp-path-map object-rec-id paths exp)])

;; LExp-path-map
;; applies f to each Path p in the terms
;; + if, for any  p, (f p) returns Empty for any p, Empty is returned
;; + for any p where (f p) returns a LExp, it is multiplied by the
;;    original coefficient of p and added to the LExp
;; + for p's where (f p) = some Path, we just swap p and (f p) basically
(define/cond-contract (LExp-path-map f lexp)
  (-> (-> Path? Object?) LExp? 
      (or/c LExp? Empty?))
  (match lexp
    [(LExp: ps exp) (internal-lexp-path-map f ps exp)]
    [_ (int-err "invalid LExp for LExp-path-map: ~a" lexp)]))

;; internal workhorse for LExp-path-map (details described there)
(define/cond-contract (internal-lexp-path-map f paths exp)
  (-> (-> Path? Object?) immutable-path-set? lexp?
      (or/c LExp? Empty?))
  (match exp
   [(lexp: const terms)
    (define-values (const* terms* ps*)
      (for/fold ([const const]
                 [terms terms]
                 [ps* empty-path-set])
                ([p (in-set paths)])
        (define p* (f p))
        (define p-key (Obj-seq p))
        (define p*-key (Obj-seq p*))
        (cond
          [(not const) (values const terms ps*)]
          ;; no change, continue
          [(eq? p-key p*-key)
           (values const terms (set-add ps* p))]
          ;; empty, this linear expression is kaputt
          [(Empty? p*) (values #f p* #f)]
          ;; a new path -- remove the old, put in the new
          ;; w/ the same coeff
          [(Path? p*)
           (values const
                   (terms-remove
                    (terms-set terms p*-key (terms-ref terms p-key 0))
                    p-key)
                   (set-add ps* p*))]
          ;; a linear expression -- scale it by
          ;; the old path's coeff and add it
          [(LExp? p*)
           (match-define (LExp: p*-ps (lexp: p*-const p*-terms)) p*)
           (define old-p-coeff (terms-ref terms p-key 0))
           (values (+ const (* old-p-coeff p*-const))
                   (terms-plus (terms-remove terms p-key)
                               (terms-scale p*-terms old-p-coeff))
                   (set-union ps* p*-ps))]
          [else
           (int-err "internal-lexp-path-map: invalid obj after fold fun ~a" p*)])))
    (if const*
        (*LExp ps* (lexp const* terms*))
        ;; if const* is #f then terms was mapped to empty
        -empty-obj)]
    [_ (int-err "internal-lexp-path-map: invalid lexp ~a" exp)]))


;; constructor for LExps
;; shares implementation details heavily with
;; list->lexp in rep/fme.rkt
(define/cond-contract (-lexp . raw-terms)
  (->* () () #:rest (listof (or/c exact-integer?
                                  name-ref/c
                                  Path?
                                  (list/c exact-integer? Path?))) 
       LExp?)
  (let loop ([const 0]
             [terms (hasheq)]
             [paths empty-path-set]
             [xs raw-terms])
    (match xs
      [(list) (*LExp paths (lexp const terms))]
      [(cons term rst)
       (match term
         [(list (? exact-integer? coeff) (? Path? p))
          (define p-key (Obj-seq p))
          (loop const 
                (terms-set terms p-key (+ coeff (terms-ref terms p-key 0)))
                (set-add paths p)
                rst)]
         [(? exact-integer? new-const)
          (loop (+ new-const const)
                terms
                paths
                rst)]
         [(? Path? p)
          (define p-key (Obj-seq p))
          (loop const 
                (terms-set terms p-key (add1 (terms-ref terms p-key 0)))
                (set-add paths p)
                rst)]
         [(? name-ref/c var)
          (define p (-id-path var))
          (loop const 
                (terms-set terms (Obj-seq p) (add1 (terms-ref terms (Obj-seq p) 0)))
                (set-add paths p)
                rst)]
         [_ (int-err "invalid term in -lexp args ~a" term)])]
      [_ (int-err "-lexp invalid list of arguments for -lexp ~a" xs)])))

(define/cond-contract (LExp-const l)
  (-> LExp? exact-integer?)
  (match l
    [(LExp: _ (lexp: const _))
     const]
    [_ (int-err "invalid LExp-const argument: ~a" l)]))

;; returns the terms from this LExp as cons pairs
;; of the form  (cons Variable Coefficient)
;; (e.g. (LExp-terms (3x + 4y + z + 42)) 
;;   produces '((x . 3) (y . 4) (z . 1)))
(define/cond-contract (LExp-terms* l)
  (-> LExp? (listof (cons/c Path? exact-integer?)))
  (match l
    [(LExp: ps exp)
     (let ([terms (lexp-terms exp)])
       (for/list ([p (in-set ps)])
         (cons p (terms-ref terms (Obj-seq p) 0))))]
    [_ (int-err "invalid LExp-terms* argument: ~a" l)]))


;; LExp-add1
(define/cond-contract (LExp-add1 l)
  (-> LExp? LExp?)
  (match l
    [(LExp: ps exp)
     (*LExp ps (lexp-add1 exp))]
    [_ (int-err "invalid LExp-add1 argument: ~a" l)]))

;; constant-LExp?
;; returns #f if this LExp contains non-zero variables
;; else returns the constant value of the LExp
(define/cond-contract (constant-LExp? l)
  (-> LExp? (or/c #f exact-integer?))
  (match l
    [(LExp: _ (lexp: c terms))
     (if (hash-empty? terms)
         c
         #f)]
    [_ (int-err "invalid constant-LExp? argument: ~a" l)]))


(define-match-expander LExp:*
  (lambda (stx)
    (syntax-case stx ()
      [(_ c ps/cs) 
       #'(? LExp? (app (λ (l) (list (LExp-const l)
                                    (LExp-terms* l))) 
                       (list c ps/cs)))])))

; lexp-simple?
; IF the lexp (exp) contains only 1 variable and its coefficient
; is 1 and furthermore (= 0 (lexp-const exp)) then that variable
; THEN that variable is returned
; ELSE it returns #f
(define/cond-contract (LExp-simple? l)
  (-> LExp? (or/c #f Path?))
  (match l
    [(LExp: ps (lexp: const terms))
     (and
      ;; ps is length 1? (i.e. only 1 variable)
      (= 1 (set-count ps))
      ;; constant is 0?
      (zero? const)
      (let ([p (set-first ps)])
        ;; coefficient is 1?
        (and (= 1 (terms-ref terms (Obj-seq p) 0))
             ;; okay, then return p
             p)))]
    [_ (int-err "invalid constant-LExp? argument: ~a" l)]))

(define/cond-contract (LExp-has-path? l p)
  (-> LExp? Path? boolean?)
  (set-member? (LExp-paths l) p))

(define (LExp->sexp l Path->sexp)
  (match l
    [(LExp: ps (lexp: c terms))
     (cond
       [(hash-empty? terms) c]
       [else
        (define terms*
          (let ([terms (for/list ([p (in-set ps)])
                         (define coeff (terms-ref terms (Obj-seq p) 0))
                         (if (= 1 coeff)
                             (Path->sexp p)
                             `(* ,coeff ,(Path->sexp p))))])
            (if (zero? c) terms (cons c terms))))
        (cond
          [(null? terms*) 0] ;; not possible?
          [(null? (cdr terms*)) (car terms*)] ;; just one term, no '+'
          [else (cons '+ terms*)])])] ;; else do an sexp with '+' at front
    [_ (int-err "invalid LExp in LExp->sexp ~a" l)]))


;;******************************************************************************
;; Mathematical operations for Objects (potentially producing LExps)
(define/cond-contract (-obj* . objs)
  (->* () () #:rest (listof Object?) (or/c Object? #f))
  (match objs
    [(list) #f]
    [(list o) o]
    [(list o1 o2) (multiply-Objects o1 o2)]
    [(list o1 o2 o3 os ...)
     (apply -obj* (cons (multiply-Objects o1 o2) (cons o3 os)))]))


(define/cond-contract (multiply-Objects o1 o2)
  (-> Object? Object? Object?)
  (define ((scale-obj o) c)
    (match o
      [(? Path?)
       (-lexp (list c o))]
      [(LExp: ps (lexp: const terms))
       ;; scaling doesn't modify which paths are in the LExp! =)
       ;; just constants & coefficients
       (*LExp ps (lexp (* c const) (terms-scale terms c)))]
      [_ (int-err "invalid obj to multiply ~a" o)]))
  (cond
    ;; any Empty object --> Empty
    [(or (Empty? o1) (Empty? o2))
     -empty-obj]
    [(and (LExp? o1) (constant-LExp? o1))
     => (scale-obj o2)]
    [(and (LExp? o2) (constant-LExp? o2))
     => (scale-obj o1)]
    [else
     -empty-obj]))


(define/cond-contract (-obj+ objs)
  (-> (listof Object?) (or/c Object? #f))
  (match objs
    [(list) #f]
    [(list o) o]
    [(list o1 o2) (add-Objects o1 o2)]
    [(list o1 o2 o3 os ...)
     (-obj+ (cons (add-Objects o1 o2) (cons o3 os)))]))

(define (add-Objects o1 o2)
  (define (sorted-path-insert ps p)
    (match ps
      [(list) (cons p ps)]
      [(cons x xs)
       (cond
         [(obj<? p x)
          (cons p ps)]
         [(object-equal? p x)
          ps]
         [else
          (cons x (sorted-path-insert p xs))])]))

  (define (add-path-to-lexp p l)
    (match l
      [(LExp: ps (lexp: const terms))
       (*LExp (set-add ps p)
              (lexp const
                    (terms-set terms
                               (Obj-seq p)
                               (terms-ref terms (Obj-seq p) 0))))]
      [_ (int-err "add-path-to-lexp: invalid lexp ~a" l)]))
  
  (match* (o1 o2)
    [(_ _) #:when (or (Empty? o1) (Empty? o2))
           -empty-obj]
    [((? Path?) (? Path?))
     (-lexp (list 1 o1) (list 1 o2))]
    [((? LExp? l) (? Path? p))
     (add-path-to-lexp p l)]
    [((? Path? p) (? LExp? l))
     (add-path-to-lexp p l)]
    [((LExp: ps1 (lexp: c1 terms1)) (LExp: ps2 (lexp: c2 terms2)))
     (*LExp (set-union ps1 ps2)
            (lexp (+ c1 c2)
                  (terms-plus terms1 terms2)))]
    [(_ _) (int-err "add-Objects: unknown object case for add-Objects (~a ~a)" o1 o2)]))


(define (non-empty-obj? o)
  (or (Path? o) (LExp? o)))
