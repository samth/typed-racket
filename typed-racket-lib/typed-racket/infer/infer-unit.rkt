#lang racket/unit

;; This is the main file that defines local type inference in TR
;;
;; The algorithm is based on
;;   "Local Type Inference" by Pierce and Turner
;;   ACM TOPLAS, Vol. 22, No. 1, January 2000.
;;

(require "../utils/utils.rkt"
         (except-in
          (combine-in
           (utils tc-utils substitution)
           (rep free-variance type-rep filter-rep object-rep rep-utils)
           (types utils abbrev numeric-tower union subtype resolve
                  substitute generalize prefab)
           (logic proves)
           (env index-env tvar-env lexical-env))
          make-env -> ->* one-of/c)
         "constraint-structs.rkt"
         "signatures.rkt" "fail.rkt"
         "promote-demote.rkt"
         racket/match racket/function
         mzlib/etc
         (contract-req)
         (for-syntax
           racket/base
           syntax/parse)
         unstable/sequence unstable/list unstable/hash
         racket/list)

(import dmap^ constraints^)
(export infer^)

;; For more data definitions, see "constraint-structs.rkt"
;;
;; A Seen is a set represented by a list of Pair<Seq, Seq>
(define (empty-set) '())

(define current-seen (make-parameter (empty-set)))

;; Type Type -> Pair<Seq, Seq>
;; construct a pair for the set of seen type pairs
(define (seen-before s t)
  (cons (Type-seq s) (Type-seq t)))

;; Context, contains which type variables and indices to infer and which cannot be mentioned in
;; constraints.
(define-struct/cond-contract context
  ([bounds (listof symbol?)]
   [vars (listof symbol?)]
   [indices (listof symbol?)]) #:transparent)

(define (context-add-vars ctx vars)
  (match ctx
    [(context V X Y)
     (context V (append vars X) Y)]))

(define (context-add-var ctx var)
  (match ctx
    [(context V X Y)
     (context V (cons var X) Y)]))

(define (context-add ctx #:bounds [bounds empty] #:vars [vars empty] #:indices [indices empty])
  (match ctx
    [(context V X Y)
     (context (append bounds V) (append vars X) (append indices Y))]))

(define (inferable-index? ctx bound)
  (match ctx
    [(context _ _ Y)
     (memq bound Y)]))

(define ((inferable-var? ctx) var)
  (match ctx
    [(context _ X _)
     (memq var X)]))

(define (empty-cset/context ctx)
  (match ctx
    [(context _ X Y)
     (empty-cset X Y)]))




;; Type Type Seen -> Seen
;; Add the type pair to the set of seen type pairs
(define/cond-contract (remember s t A)
  ((or/c AnyValues? Values/c ValuesDots?) (or/c AnyValues? Values/c ValuesDots?)
   (listof (cons/c exact-nonnegative-integer?
                   exact-nonnegative-integer?))
   . -> .
   (listof (cons/c exact-nonnegative-integer?
                   exact-nonnegative-integer?)))
 (cons (seen-before s t) A))

;; Type Type -> Boolean
;; Check if a given type pair have been seen before
(define/cond-contract (seen? s t cs)
  ((or/c AnyValues? Values/c ValuesDots?) (or/c AnyValues? Values/c ValuesDots?)
   (listof (cons/c exact-nonnegative-integer?
                   exact-nonnegative-integer?))
   . -> . any/c)
 (member (seen-before s t) cs))

;; (CMap DMap -> Pair<CMap, DMap>) CSet -> CSet
;; Map a function over a constraint set
(define (map/cset f cset)
  (% make-cset (for/list/fail ([(cmap dmap) (in-pairs (cset-maps cset))])
                 (f cmap dmap))))

;; Symbol DCon -> DMap
;; Construct a dmap containing only a single mapping
(define (singleton-dmap dbound dcon)
  (make-dmap (make-immutable-hash (list (cons dbound dcon)))))

;; Hash<K, V> Listof<K> -> Hash<K, V>
;; Remove all provided keys from the hash table
(define (hash-remove* hash keys)
  (for/fold ([h hash]) ([k (in-list keys)]) (hash-remove h k)))

(define (mover cset dbound vars f)
  (map/cset
   (lambda (cmap dmap)
     (when (hash-has-key? (dmap-map dmap) dbound)
       (int-err "Tried to move vars to dbound that already exists"))
     (% cons
        (hash-remove* cmap (cons dbound vars))
        (dmap-meet
         (singleton-dmap
          dbound
          (f cmap))
         dmap)))
   cset))

;; dbound : index variable
;; vars : listof[type variable] - temporary variables
;; cset : the constraints being manipulated
;; takes the constraints on vars and creates a dmap entry constraining dbound to be |vars|
;; with the constraints that cset places on vars
(define/cond-contract (move-vars-to-dmap cset dbound vars)
  (cset? symbol? (listof symbol?) . -> . cset?)
  (mover cset dbound vars
         (λ (cmap)
           (make-dcon (for/list ([v (in-list vars)])
                        (hash-ref cmap v
                                  (λ () (int-err "No constraint for new var ~a" v))))
                      #f))))

;; cset : the constraints being manipulated
;; var : index variable being inferred
;; dbound : constraining index variable
;;
(define/cond-contract (move-dotted-rest-to-dmap cset var dbound)
  (cset? symbol? symbol? . -> . cset?)
  (mover cset var null
         (λ (cmap)
           (make-dcon-dotted
            null
            (hash-ref cmap var
                      (λ () (int-err "No constraint for bound ~a" var)))
            dbound))))

;; cset : the constraints being manipulated
;; vars : the variables that are the prefix of the dbound
;; dbound : index variable
(define/cond-contract (move-vars+rest-to-dmap cset vars dbound #:exact [exact? #f])
  ((cset? (listof symbol?) symbol?) (#:exact boolean?) . ->* . cset?)
  (mover cset dbound vars
         (λ (cmap)
           ((if exact? make-dcon-exact make-dcon)
            (for/list ([v (in-list vars)])
              (hash-ref cmap v no-constraint))
            (hash-ref cmap dbound (λ () (int-err "No constraint for bound ~a" dbound)))))))

;; Represents a sequence of types. types are the fixed prefix, and end is the remaining types
;; This is a unification of all of the dotted types that exist ListDots, ->..., and ValuesDots.
;; This allows for one implementation of the cgen algorithm for dotted types to be shared across all
;; of them.
(struct seq (types end) #:transparent)
(struct null-end () #:transparent)
(struct uniform-end (type) #:transparent)
(struct dotted-end (type bound) #:transparent)

(define (Values->seq v)
  (match v
    [(Values: ts) (seq ts (null-end))]
    [(ValuesDots: ts dty dbound) (seq ts (dotted-end (-result dty) dbound))]
    [_ #f]))


(define (List->end v)
  (match v
    [(== -Null type-equal?) (null-end)]
    [(Listof: t) (uniform-end t)]
    [(ListDots: t dbound) (dotted-end t dbound)]
    [_ #f]))

(define (List->seq v)
  (match v
    [(List: ts #:tail (app List->end end)) (and end (seq ts end))]))


(define-match-expander ValuesSeq:
  (lambda (stx)
    (syntax-parse stx
      [(_ seq) #'(app Values->seq (? values seq))])))

(define-match-expander ListSeq:
  (lambda (stx)
    (syntax-parse stx
      [(_ seq) #'(app List->seq (? values seq))])))


;; generate-dbound-prefix: Symbol Type/c Natural Symbol -> (Values (Listof Symbol) (Listof Type/c))
;; Substitutes n fresh new variables, replaces dotted occurences of v in t with the variables (and
;; maybe new-end), and then for each variable substitutes it in for regular occurences of v.
(define (generate-dbound-prefix v ty n new-end)
  (define vars (build-list n (lambda (x) (gensym v))))
  (define ty* (substitute-dots (map make-F vars) (and new-end (make-F new-end)) v ty))
  (values
    vars
    (for/list ([var (in-list vars)])
      (substitute (make-F var) v ty*))))


(define/cond-contract (cgen/filter context s t)
  (context? Filter? Filter? . -> . (or/c #f cset?))
  (match* (s t)
    [(e e) (empty-cset/context context)]
    [(e (Top:)) (empty-cset/context context)]
    ;; FIXME - is there something to be said about the logical ones?
    [((TypeFilter: s p) (TypeFilter: t p)) (cgen/inv context s t)]
    [((NotTypeFilter: s p) (NotTypeFilter: t p)) (cgen/inv context s t)]
    [(_ _) #f]))

;; s and t must be *latent* filter sets
(define/cond-contract (cgen/filter-set context s t)
  (context? FilterSet? FilterSet? . -> . (or/c #f cset?))
  (match* (s t)
    [(e e) (empty-cset/context context)]
    [((FilterSet: s+ s-) (FilterSet: t+ t-))
     (% cset-meet (cgen/filter context s+ t+) (cgen/filter context s- t-))]
    [(_ _) #f]))

(define/cond-contract (cgen/object context s t)
  (context? Object? Object? . -> . (or/c #f cset?))
  (match* (s t)
    [(e e) (empty-cset/context context)]
    [(e (Empty:)) (empty-cset/context context)]
    ;; FIXME - do something here
    [(_ _) #f]))

(define/cond-contract (cgen/seq context s-seq t-seq)
  (context? seq? seq? . -> . (or/c #f cset?))
  (match*/early (s-seq t-seq)
    ;; The simplest case - both are null-end
    [((seq ss (null-end))
      (seq ts (null-end)))
      (cgen/list context ss ts)]
    ;; One is null-end the other is uniform-end
    [((seq ss (null-end))
      (seq ts (uniform-end t-rest)))
     (cgen/list context ss (extend ss ts t-rest))]
    [((seq ss (uniform-end s-rest))
      (seq ts (null-end)))
     #f]
    ;; Both are uniform-end
    [((seq ss (uniform-end s-rest))
      (seq ts (uniform-end t-rest)))
     (cgen/list context
                (cons s-rest ss)
                (cons t-rest (extend ss ts t-rest)))]
    ;; dotted below, nothing above
    [((seq ss (dotted-end dty dbound))
      (seq ts (null-end)))
     #:return-unless (inferable-index? context dbound)
     #f
     #:return-unless (<= (length ss) (length ts))
     #f
     (define-values (vars new-tys) (generate-dbound-prefix dbound dty (- (length ts) (length ss)) #f))
     (define-values (ts-front ts-back) (split-at ts (length ss)))
     (% cset-meet
        (cgen/list context ss ts-front)
        (% move-vars-to-dmap (cgen/list (context-add context #:vars vars) new-tys ts-back) dbound vars))]
    ;; dotted above, nothing below
    [((seq ss (null-end))
      (seq ts (dotted-end dty dbound)))
     #:return-unless (inferable-index? context dbound)
     #f
     #:return-unless (<= (length ts) (length ss))
     #f
     (define-values (vars new-tys) (generate-dbound-prefix dbound dty (- (length ss) (length ts)) #f))
     (define-values (ss-front ss-back) (split-at ss (length ts)))
     (% cset-meet
        (cgen/list context ss-front ts)
        (% move-vars-to-dmap (cgen/list (context-add-vars context vars) ss-back new-tys) dbound vars))]

    ;; same dotted bound
    [((seq ss (dotted-end s-dty dbound))
      (seq ts (dotted-end t-dty dbound)))
     #:return-unless (= (length ss) (length ts))
     #f
     (% cset-meet
        (cgen/list context ss ts)
        (if (inferable-index? context dbound)
            (extend-tvars (list dbound)
              (% move-vars+rest-to-dmap (cgen (context-add-var context dbound) s-dty t-dty) null dbound))
            (cgen context s-dty t-dty)))]

    ;; bounds are different
    [((seq ss (dotted-end s-dty dbound))
      (seq ts (dotted-end t-dty dbound*)))
     #:when (inferable-index? context dbound)
     #:return-unless (= (length ss) (length ts)) #f
     #:return-when (inferable-index? context dbound*) #f
     (% cset-meet
        (cgen/list context ss ts)
        (extend-tvars (list dbound*)
          (% move-dotted-rest-to-dmap (cgen (context-add-var context dbound) s-dty t-dty) dbound dbound*)))]
    [((seq ss (dotted-end s-dty dbound))
      (seq ts (dotted-end t-dty dbound*)))
     #:when (inferable-index? context dbound*)
     #:return-unless (= (length ss) (length ts)) #f
     (% cset-meet
        (cgen/list context ss ts)
        (extend-tvars (list dbound)
          (% move-dotted-rest-to-dmap (cgen (context-add-var context dbound*) s-dty t-dty) dbound* dbound)))]

    ;; * <: ...
    [((seq ss (uniform-end s-rest))
      (seq ts (dotted-end t-dty dbound)))
     #:return-unless (inferable-index? context dbound)
     #f
     #:return-unless (<= (length ts) (length ss))
     #f
     (define new-bound (gensym dbound))
     (define-values (vars new-tys) (generate-dbound-prefix dbound t-dty (- (length ss) (length ts))
                                                           new-bound))
     (define-values (ss-front ss-back) (split-at ss (length ts)))
     (% cset-meet
        (cgen/list context ss-front ts)
        (% move-vars+rest-to-dmap
           (% cset-meet
              (cgen/list (context-add context #:bounds (list new-bound) #:vars vars #:indices (list new-bound))
                         ss-back new-tys)
              (cgen (context-add-var context dbound) s-rest t-dty))
           vars dbound #:exact #t))]

    [((seq ss (dotted-end s-dty dbound))
      (seq ts (uniform-end t-rest)))
     (cond
       [(inferable-index? context dbound)
        (define new-bound (gensym dbound))
        (define length-delta (- (length ts) (length ss)))
        (define-values (vars new-tys)
          (generate-dbound-prefix dbound s-dty (max 0 length-delta) new-bound))
        (% cset-meet
           (cgen/list context ss (if (positive? length-delta)
                                     (drop-right ts length-delta)
                                     (extend ss ts t-rest)))
           (% move-vars+rest-to-dmap
              (% cset-meet
                 (cgen/list (context-add context #:bounds (list new-bound) #:vars vars #:indices (list new-bound))
                            new-tys (take-right ts (max 0 length-delta)))
                 (cgen (context-add-var context dbound) s-dty t-rest))
              vars dbound))]
       [else
        (extend-tvars (list dbound)
          (cgen/seq (context-add context #:bounds (list dbound)) (seq ss (uniform-end s-dty)) t-seq))])]))

(define ((elim-temps elim) cm dm)
  (define (elim-in-c constr)
    (match constr
      [(c S T o) (c (elim S) (elim T) o)]
      [#f #f]
      [_ (error 'elim-in-c "unsupported constraint ~a" constr)]))
  
  (define cm* (for/hash ([(X C) (in-hash cm)])
                  (values X (elim-in-c C))))
  
  (define dm*
    (make-dmap
     (for/hash ([(k dc) (in-hash (dmap-map dm))])
       (values
        k
        (match dc
          [(dcon fixed rest)
           (dcon (map elim-in-c fixed) (elim-in-c rest))]
          [(dcon-exact fixed rest)
           (dcon-exact (map elim-in-c fixed) (elim-in-c rest))]
          [(dcon-dotted cs c bound)
           (dcon-dotted (map elim-in-c cs) (elim-in-c c) bound)])))))
  
  (cons cm* dm*))

(define ((elim-cs-temps temp-ids) cs)
  (define (elim t)
    (for/fold ([t t])
              ([temp-id (in-list temp-ids)])
      (subst-type t temp-id -empty-obj #t)))
  (% map/cset (elim-temps elim) cs))

(define/cond-contract (cgen/arr context s-arr t-arr)
  (context? arr? arr? . -> . (or/c #f cset?))

  (match* (s-arr t-arr)
    [((arr: ss s s-rest s-drest s-kws s-dep?) (arr: ts t t-rest t-drest t-kws t-dep?)) ;; TODO(AMK)
     (define (rest->end rest drest)
       (cond
         [rest (uniform-end rest)]
         [drest (dotted-end (car drest) (cdr drest))]
         [else (null-end)]))

     (define-values (temp-ids temp-objs)
       (for/lists (_1 _2) ([s (in-list ss)] [t (in-list ts)])
         (define id (genid))
         (values id (-id-path id))))

     ;; remove 'free' de bruijn indices that can escape their context if they
     ;; are bound to a type variable used outside of this function type
     (let ([ss (for/list ([s (in-list ss)])
                 (for/fold ([s s]) ([(o arg) (in-indexed (in-list temp-objs))])
                   (subst-type s (list 0 arg) o #t)))]
           [ts (for/list ([t (in-list ts)])
                 (for/fold ([t t]) ([(o arg) (in-indexed (in-list temp-objs))])
                   (subst-type t (list 0 arg) o #t)))]
           [s (for/fold ([s s]) ([(o arg) (in-indexed (in-list temp-objs))])
                (subst-result s (list 0 arg) o #t))]
           [t (for/fold ([t t]) ([(o arg) (in-indexed (in-list temp-objs))])
                (subst-result t (list 0 arg) o #t))])
       (define s-seq (seq ss (rest->end s-rest s-drest)))
       (define t-seq (seq ts (rest->end t-rest t-drest)))
       (cond
         [(and (null? s-kws)
               (null? t-kws)
               (% cset-meet
                  (cgen context s t)
                  (cgen/seq context t-seq s-seq)))
          => (elim-cs-temps temp-ids)] ;; TODO test this!
         [else #f]))]))
     
     

;; TODO(AMK) fields obj support
(define/cond-contract (cgen/flds context flds-s flds-t)
  (context? (listof fld?) (listof fld?)  . -> . (or/c #f cset?))
  (% cset-meet*
   (for/list/fail ([s (in-list flds-s)] [t (in-list flds-t)])
     (match* (s t)
       ;; mutable - invariant
       [((fld: s _ #t) (fld: t _ #t)) (cgen/inv context s t)]
       ;; immutable - covariant
       [((fld: s _ #f) (fld: t _ #f)) (cgen context s t)]))))

(define (cgen/inv context s t #:obj [obj -empty-obj]) ;; MARK
  (% cset-meet (cgen context s t #:obj obj) (cgen context t s #:obj obj)))


;; context : the context of what to infer/not infer
;; S : a type to be the subtype of T
;; T : a type
;; produces a cset which determines a substitution that makes S a subtype of T
;; implements the V |-_X S <: T => C judgment from Pierce+Turner, extended with
;; the index variables from the TOPLAS paper
(define/cond-contract (cgen context S T #:obj [current-object -empty-obj])
  ((context? (or/c Values/c ValuesDots? AnyValues?) (or/c Values/c ValuesDots? AnyValues?))
   (#:obj Object?)
   . ->* . (or/c #f cset?))
  (define obj (or current-object -empty-obj))
  ;; useful quick loop
  (define/cond-contract (cg S T obj)
    (Type/c Type/c Object? . -> . (or/c #f cset?))
    (cgen context S T #:obj obj))
  (define/cond-contract (cg/inv S T obj)
    (Type/c Type/c Object? . -> . (or/c #f cset?))
    (cgen/inv context S T #:obj obj))
  ;; this places no constraints on any variables
  (define empty (empty-cset/context context))
  ;; this constrains just x (which is a single var)
  (define (singleton S x T obj)
    (insert empty x S T obj))
  ;; FIXME -- figure out how to use parameters less here
  ;;          subtyping doesn't need to use it quite as much
  (define cs (current-seen))
  ;; if we've been around this loop before, we're done (for rec types)
  (if (seen? S T cs)
      empty
      (parameterize
          (;; remember S and T, and obtain everything we've seen from the context
           ;; we can't make this an argument since we may call back and forth with
           ;; subtyping, for example
           [current-seen (remember S T cs)])
        (match*/early
         (S T)
         ;; if they're equal, no constraints are necessary (CG-Refl)
         [(a b) #:when (type-equal? a b) empty]
         ;; CG-Top
         [(_ (Univ:)) empty]
         ;; AnyValues
         [((AnyValues: s-f) (AnyValues: t-f))
          (cgen/filter context s-f t-f)]
         
         [((or (Values: (list (Result: _ fs _) ...))
               (ValuesDots: (list (Result: _ fs _) ...) _ _))
           (AnyValues: t-f))
          (cset-join
           (filter identity
                   (for/list ([f (in-list fs)])
                     (match f
                       [(FilterSet: f+ f-)
                        (% cset-meet (cgen/filter context f+ t-f) (cgen/filter context f- t-f))]))))]
         
         ;; check all non Type/c first so that calling subtype is safe
         
         ;; check each element
         [((Result: s f-s o-s)
           (Result: t f-t o-t))
          (% cset-meet (cg s t o-s)
             (cgen/filter-set context f-s f-t)
             (cgen/object context o-s o-t))]
         
         ;; Values just delegate to cgen/seq, except special handling for -Bottom.
         ;; A single -Bottom in a Values means that there is no value returned and so any other
         ;; Values or ValuesDots should be above it.
         [((ValuesSeq: s-seq) (ValuesSeq: t-seq))
          ;; Check for a substition that S is below (ret -Bottom).
          (define bottom-case
            (match S
              [(Values: (list (Result: s f-s o-s)))
               (cg s -Bottom o-s)] ;; is empty-obj correct obj here?
              [else #f]))
          (define regular-case
            (cgen/seq context s-seq t-seq))
          ;; If we want the OR of the csets that the two cases return.
          (cset-join
           (filter values
                   (list bottom-case regular-case)))]
         
         ;; they're subtypes. easy.
         [(a b) 
          #:when (subtype a b #:obj current-object)
          empty]
         
         ;; Lists delegate to sequences
         [((ListSeq: s-seq) (ListSeq: t-seq))
          (cgen/seq context s-seq t-seq)]
         
         ;; refinements are erased to their bound
         [((Refinement: S _) T)
          (cg S T current-object)]
         
         ;; variables that are in X and should be constrained
         ;; all other variables are compatible only with themselves
         [((F: (? (inferable-var? context) v)) T)
          #:return-when
          (match T
            ;; fail when v* is an index variable
            [(F: v*) (and (bound-index? v*) (not (bound-tvar? v*)))]
            [_ #f])
          #f
          ;; constrain v to be below T (but don't mention bounds)
          (singleton (Un) v (var-demote T (context-bounds context)) current-object)]
         
         [(S (F: (? (inferable-var? context) v)))
          #:return-when
          (match S
            [(F: v*) (and (bound-index? v*) (not (bound-tvar? v*)))]
            [_ #f])
          #f
          ;; constrain v to be above S (but don't mention bounds)
          (singleton (var-promote S (context-bounds context)) v Univ current-object)]
         
         ;; recursive names should get resolved as they're seen
         [(s (? Name? t))
          (cg s (resolve-once t) current-object)]
         [((? Name? s) t)
          (cg (resolve-once s) t current-object)]
         
         ;; constrain b1 to be below T, but don't mention the new vars
         [((Poly: v1 b1) T) (cgen (context-add context #:bounds v1) b1 T #:obj current-object)]
         
         ;; constrain *each* element of es to be below T, and then combine the constraints
         [((Union: es) T)
          (define cs (for/list/fail ([e (in-list es)]) (cg e T current-object)))
          (and cs (cset-meet* (cons empty cs)))]
         
         ;; find *an* element of es which can be made to be a supertype of S
         ;; FIXME: we're using multiple csets here, but I don't think it makes a difference
         ;; not using multiple csets will break for: ???
         [(S (Union: es))
          (cset-join
           (for*/list ([e (in-list es)]
                       [v (in-value (cg S e current-object))]
                       #:when v)
             v))]
         
         ;; two structs with the same name
         ;; just check pairwise on the fields
         [((Struct: nm _ flds proc _ _) (Struct: nm* _ flds* proc* _ _))
          #:when (free-identifier=? nm nm*)
          (let ([proc-c
                 (cond [(and proc proc*)
                        (cg proc proc* -empty-obj)] ;; TODO(AMK) more detailed obj here?
                       [proc* #f]
                       [else empty])])
            (% cset-meet proc-c (cgen/flds context flds flds*)))]
         
         ;; two prefab structs with the same key
         [((Prefab: k ss) (Prefab: k* ts))
          #:when (and (prefab-key-subtype? k k*)
                      (>= (length ss) (length ts)))
          (% cset-meet*
             (for/list/fail ([s (in-list ss)]
                             [t (in-list ts)]
                             [mut? (in-list (prefab-key->field-mutability k*))])
                            (if mut?
                                (cg/inv s t)
                                (cg s t))))]
         
         ;; two struct names, need to resolve b/c one could be a parent
         [((Name: n _ #t) (Name: n* _ #t))
          (if (free-identifier=? n n*)
              empty ;; just succeed now
              (% cg (resolve-once S) (resolve-once T) current-object))]
         ;; pairs are pointwise
         [((Pair: a b) (Pair: a* b*))
          (let ([lhs-cs (cg a a* (-car-of current-object))]
                 [rhs-cs (cg b b* (-cdr-of current-object))])
            (% cset-meet lhs-cs rhs-cs))]
         
         ;; sequences are covariant
         [((Sequence: ts) (Sequence: ts*))
          (cgen/list context ts ts*)]
         [((Listof: t) (Sequence: (list t*)))
          (cg t t* -empty-obj)]
         [((Pair: t1 t2) (Sequence: (list t*)))
          (% cset-meet
             (cg t1 t* (-car-of current-object))
             (cg t2 (-lst t*) (-cdr-of current-object)))]
         [((MListof: t) (Sequence: (list t*)))
          (cg t t* -empty-obj)]
         ;; To check that mutable pair is a sequence we check that the cdr is
         ;; both an mutable list and a sequence
         [((MPair: t1 t2) (Sequence: (list t*)))
          (% cset-meet
             (cg t1 t* (-car-of current-object))
             (cg t2 T (-cdr-of current-object))
             (cg t2 (Un -Null (make-MPairTop)) (-cdr-of current-object)))]
         [((List: ts) (Sequence: (list t*)))
          (% cset-meet* (for/list/fail ([t (in-list ts)])
                                       (cg t t* -empty-obj)))]
         [((HeterogeneousVector: ts) (HeterogeneousVector: ts*))
          (% cset-meet (cgen/list context ts ts*) (cgen/list context ts* ts))]
         [((HeterogeneousVector: ts) (Vector: s))
          (define ts* (map (λ _ s) ts)) ;; invariant, everything has to match
          (% cset-meet (cgen/list context ts ts*) (cgen/list context ts* ts))]
         [((HeterogeneousVector: ts) (Sequence: (list t*)))
          (% cset-meet* (for/list/fail ([t (in-list ts)])
                                       (cg t t* -empty-obj)))]
         [((Vector: t) (Sequence: (list t*)))
          (cg t t* -empty-obj)]
         [((Base: 'String _ _ _) (Sequence: (list t*)))
          (cg -Char t* -empty-obj)]
         [((Base: 'Bytes _ _ _) (Sequence: (list t*)))
          (cg -Nat t* -empty-obj)]
         [((Base: 'Input-Port _ _ _) (Sequence: (list t*)))
          (cg -Nat t* -empty-obj)]
         [((Value: (? exact-nonnegative-integer? n)) (Sequence: (list t*)))
          (define possibilities
            (list
             (list byte? -Byte)
             (list portable-index? -Index)
             (list portable-fixnum? -NonNegFixnum)
             (list values -Nat)))
          (define type
            (for/or ([pred-type (in-list possibilities)])
              (match pred-type
                ((list pred? type)
                 (and (pred? n) type)))))
          (cg type t* -empty-obj)]
         [((Base: _ _ _ #t) (Sequence: (list t*)))
          (define type
            (for/or ([t (in-list (list -Byte -Index -NonNegFixnum -Nat))])
              (and (subtype S t #:obj current-object) t)))
          (% cg type t* -empty-obj)]
         [((Hashtable: k v) (Sequence: (list k* v*)))
          (cgen/list context (list k v) (list k* v*))]
         [((Set: t) (Sequence: (list t*)))
          (cg t t* -empty-obj)]
         
         ;; Mu's just get unfolded
         ;; We unfold S first so that unions are handled in S before T
         [((? Mu? s) t) (cg (unfold s) t current-object)]
         [(s (? Mu? t)) (cg s (unfold t) current-object)]
         
         ;; resolve applications
         [((App: _ _ _) _)
          (% cg (resolve-once S) T current-object)]
         [(_ (App: _ _ _))
          (% cg S (resolve-once T) current-object)]
         
         ;; If the struct names don't match, try the parent of S
         ;; Needs to be done after App and Mu in case T is actually the current struct
         ;; but not currently visible
         [((Struct: nm (? Type? parent) _ _ _ _) other)
          (cg parent other current-object)]
         
         ;; Invariant here because struct types aren't subtypes just because the
         ;; structs are (since you can make a constructor from the type).
         [((StructType: s) (StructType: t))
          (cg/inv s t -empty-obj)]
         
         ;; vectors are invariant - generate constraints *both* ways
         [((Vector: e) (Vector: e*))
          (cg/inv e e* -empty-obj)]
         ;; boxes are invariant - generate constraints *both* ways
         [((Box: e) (Box: e*))
          (cg/inv e e* -empty-obj)]
         [((Weak-Box: e) (Weak-Box: e*))
          (cg/inv e e* -empty-obj)]
         [((MPair: s t) (MPair: s* t*))
          (% cset-meet
             (cg/inv s s* (-car-of current-object))
             (cg/inv t t* (-cdr-of current-object)))]
         [((Channel: e) (Channel: e*))
          (cg/inv e e* -empty-obj)]
         [((Async-Channel: e) (Async-Channel: e*))
          (cg/inv e e* -empty-obj)]
         [((ThreadCell: e) (ThreadCell: e*))
          (cg/inv e e* -empty-obj)]
         [((Continuation-Mark-Keyof: e) (Continuation-Mark-Keyof: e*))
          (cg/inv e e* -empty-obj)]
         [((Prompt-Tagof: s t) (Prompt-Tagof: s* t*))
          (% cset-meet (cg/inv s s* -empty-obj) (cg/inv t t* -empty-obj))]
         [((Promise: e) (Promise: e*))
          (cg e e* -empty-obj)]
         [((Ephemeron: e) (Ephemeron: e*))
          (cg e e* -empty-obj)]
         [((CustodianBox: e) (CustodianBox: e*))
          (cg e e* -empty-obj)]
         [((Set: a) (Set: a*))
          (cg a a* -empty-obj)]
         [((Evt: a) (Evt: a*))
          (cg a a* -empty-obj)]
         [((Base: 'Semaphore _ _ _) (Evt: t))
          (cg S t -empty-obj)]
         [((Base: 'Output-Port _ _ _) (Evt: t))
          (cg S t -empty-obj)]
         [((Base: 'Input-Port _ _ _) (Evt: t))
          (cg S t -empty-obj)]
         [((Base: 'TCP-Listener _ _ _) (Evt: t))
          (cg S t -empty-obj)]
         [((Base: 'Thread _ _ _) (Evt: t))
          (cg S t -empty-obj)]
         [((Base: 'Subprocess _ _ _) (Evt: t))
          (cg S t -empty-obj)]
         [((Base: 'Will-Executor _ _ _) (Evt: t))
          (cg S t -empty-obj)]
         [((Base: 'LogReceiver _ _ _) (Evt: t ))
          (cg (make-HeterogeneousVector
               (list -Symbol -String Univ
                     (Un (-val #f) -Symbol)))
              t
              -empty-obj)]
         [((Base: 'Place _ _ _) (Evt: t))
          (cg Univ t -empty-obj)]
         [((Base: 'Base-Place-Channel _ _ _) (Evt: t))
          (cg Univ t -empty-obj)]
         [((CustodianBox: t) (Evt: t*)) (cg S t* -empty-obj)]
         [((Channel: t) (Evt: t*)) (cg t t* -empty-obj)]
         [((Async-Channel: t) (Evt: t*)) (cg t t* -empty-obj)]
         ;; we assume all HTs are mutable at the moment
         [((Hashtable: s1 s2) (Hashtable: t1 t2))
          ;; for mutable hash tables, both are invariant
          (% cset-meet (cg/inv s1 t1 -empty-obj) (cg/inv s2 t2 -empty-obj))]
         ;; syntax is covariant
         [((Syntax: s1) (Syntax: s2))
          (cg s1 s2 -empty-obj)]
         ;; futures are covariant
         [((Future: s1) (Future: s2))
          (cg s1 s2 -empty-obj)]
         ;; parameters are just like one-arg functions
         [((Param: in1 out1) (Param: in2 out2))
          (% cset-meet (cg in2 in1 -empty-obj) (cg out1 out2 -empty-obj))]
         [((Function: (list s-arr ...))
           (Function: (list t-arr ...)))
          (% cset-meet*
             (for/list/fail
              ([t-arr (in-list t-arr)])
              ;; for each element of t-arr, we need to get at least one element of s-arr that works
              (let ([results (for*/list ([s-arr (in-list s-arr)]
                                         [v (in-value (cgen/arr context s-arr t-arr))]
                                         #:when v)
                               v)])
                ;; ensure that something produces a constraint set
                (and (not (null? results))
                     (cset-join results)))))]
         
         ;; Refined Types
         [(t1 t2)
          #:when (or (Refine? t1) (Refine? t2))
          (define o (if (non-empty-obj? current-object) current-object (-id-path (genid))))
          (match t1
            ;; t1 is a refined type
            [(Refine/obj: o rt1 rp1)
             (match t2
               ;;t2 also a refined type, check if
               ;; t2's prop is provable and proceed
               [(Refine/obj: o rt2 rp2)
                (define assumptions (list rp1 (-is-type o rt1)))
                (and (proves (lexical-env) assumptions rp2)
                     (cg rt1 rt2 o))]
               ;; t1 only is refined, simply raise the lower bound
               ;; to obvious super type of t1
               [_ (cg rt1 t2 o)])]
            ;; only t2 is refined type
            [_
             (match-define (Refine/obj: o rt2 rp2) t2)
             ;; proceed if rp2 is provable
             (and (proves (lexical-env) (list) rp2)
                  (cg t1 rt2 o))])]
         [(_ _)
          ;; nothing worked, and we fail
          #f]))))

;; C : cset? - set of constraints found by the inference engine
;; X : (listof symbol?) - type variables that must have entries
;; Y : (listof symbol?) - index variables that must have entries
;; R : Type/c - result type into which we will be substituting
(define/cond-contract (subst-gen C X Y R)
  (cset? (listof symbol?) (listof symbol?) (or/c Values/c AnyValues? ValuesDots?)
   . -> . (or/c #f substitution/c))
  (define var-hash (free-vars-hash (free-vars* R)))
  (define idx-hash (free-vars-hash (free-idxs* R)))
  ;; c : Constaint
  ;; variance : Variance
  (define (constraint->type v variance)
    (match v
      [(c S T o)
       (evcase variance
               [Constant S]
               [Covariant S]
               [Contravariant T]
               [Invariant
                (let ([gS (generalize S)])
                  (if (subtype gS T #:obj o)
                      gS
                      S))])]))

  ;; Since we don't add entries to the empty cset for index variables (since there is no
  ;; widest constraint, due to dcon-exacts), we must add substitutions here if no constraint
  ;; was found.  If we're at this point and had no other constraints, then adding the
  ;; equivalent of the constraint (dcon null (c Bot X Top)) is okay.
  (define (extend-idxs S)
    (hash-union
     (for/hash ([v (in-list Y)]
                #:unless (hash-has-key? S v))
       (let ([var (hash-ref idx-hash v Constant)])
         (values v
                 (evcase var
                         [Constant (i-subst null)]
                         [Covariant (i-subst null)]
                         [Contravariant (i-subst/starred null Univ)]
                         ;; TODO figure out if there is a better subst here
                         [Invariant (i-subst null)]))))
     S))
  (match (car (cset-maps C))
    [(cons cmap (dmap dm))
     (let ([subst (hash-union
                   (for/hash ([(k dc) (in-hash dm)])
                     (define (c->t c) (constraint->type c (hash-ref idx-hash k Constant)))
                     (values
                      k
                      (match dc
                        [(dcon fixed #f)
                         (i-subst (map c->t fixed))]
                        [(or (dcon fixed rest) (dcon-exact fixed rest))
                         (i-subst/starred
                          (map c->t fixed)
                          (c->t rest))]
                        [(dcon-dotted fixed dc dbound)
                         (i-subst/dotted
                          (map c->t fixed)
                          (c->t dc)
                          dbound)])))
                   (for/hash ([(k v) (in-hash cmap)])
                     (values k (let ([t (constraint->type v (hash-ref var-hash k Constant))])
                                 (t-subst t)))))])
       ;; verify that we got all the important variables
       (and (for/and ([v (in-list X)])
              (let ([entry (hash-ref subst v #f)])
                ;; Make sure we got a subst entry for a type var
                ;; (i.e. just a type to substitute)
                (and entry (t-subst? entry))))
            (extend-idxs subst)))]))

;; context : the context of what to infer/not infer
;; S : a list of types to be the subtypes of T
;; T : a list of types
;; expected-cset : a cset representing the expected type, to meet early and
;;  keep the number of constraints in check. (empty by default)
;; produces a cset which determines a substitution that makes the Ss subtypes of the Ts
(define/cond-contract (cgen/list context S T
                                 #:expected-cset [expected-cset (empty-cset '() '())]
                                 #:objs [objs #f])
  ((context? (listof Values/c) (listof Values/c))
   (#:expected-cset cset? #:objs (or/c #f (listof Object?)))
   . ->* .
   (or/c cset? #f))
  (and (= (length S) (length T))
       (% cset-meet*
          (for/list/fail ([s (in-list S)] 
                          [t (in-list T)]
                          [o (in-sequence-forever (or objs '()) -empty-obj)])
                         ;; We meet early to prune the csets to a reasonable size.
                         ;; This weakens the inference a bit, but sometimes avoids
                         ;; constraint explosion.
                         (let ([cs (cgen context s t #:obj o)])
                           (% cset-meet cs expected-cset))))))



;; X : variables to infer
;; Y : indices to infer
;; S : actual argument types
;; T : formal argument types
;; R : result type
;; expected : #f or the expected type
;; returns a substitution
;; if R is #f, we don't care about the substituion
;; just return a boolean result
(define infer
 (let ()
   (define/cond-contract (infer X Y S T R [expected #f] #:objs [objs #f])
     (((listof symbol?) (listof symbol?) (listof Type/c) (listof Type/c)
                        (or/c #f Values/c ValuesDots?))
      ((or/c #f Values/c AnyValues? ValuesDots?)
       #:objs (or/c #f (listof Object?)))
      . ->* . (or/c boolean? substitution/c))
     (define ctx (context null X Y ))
     (define expected-cset
       (if expected
           (match* (R expected)
             [((Result: _ _ _) (Result: _ _ _))
              (cgen ctx R expected)]
             [((Result: t fs o) (? Type?))
              (cgen ctx t expected #:obj (or (and (non-empty-obj? o) o)
                                             -empty-obj))]
             [(_ _) (cgen ctx R expected)])
           (empty-cset '() '())))
     
     (and expected-cset
          (let* ([cs (cgen/list ctx S T #:expected-cset expected-cset #:objs objs)]
                 [cs (% cset-meet cs expected-cset)])
            (and cs (if R (subst-gen cs X Y R) #t)))))
  infer)) ;to export a variable binding and not syntax

;; like infer, but T-var is the vararg type:
(define (infer/vararg X Y S S-Objs T T-var R [expected #f])
  (define new-T (if T-var (extend S T T-var) T))
  (and ((length S) . >= . (length T))
         (infer X Y S new-T R expected #:objs S-Objs)))

;; like infer, but dotted-var is the bound on the ...
;; and T-dotted is the repeated type
(define (infer/dots X dotted-var S T T-dotted R must-vars #:expected [expected #f])
  (early-return
   (define short-S (take S (length T)))
   (define rest-S (drop S (length T)))
   (define ctx (context null X (list dotted-var)))
   (define expected-cset (if expected
                             (cgen ctx R expected)
                             (empty-cset '() '())))
   #:return-unless expected-cset #f
   (define cs-short (cgen/list ctx short-S T #:expected-cset expected-cset))
   #:return-unless cs-short #f
   (define-values (new-vars new-Ts)
     (generate-dbound-prefix dotted-var T-dotted (length rest-S) #f))
   (define cs-dotted (cgen/list (context-add-vars ctx new-vars) rest-S new-Ts
                                #:expected-cset expected-cset))
   #:return-unless cs-dotted #f
   (define cs-dotted* (move-vars-to-dmap cs-dotted dotted-var new-vars))
   #:return-unless cs-dotted* #f
   (define cs (cset-meet cs-short cs-dotted*))
   #:return-unless cs #f
   (define m (cset-meet cs expected-cset))
   #:return-unless m #f
   (subst-gen m X (list dotted-var) R)))


;(trace subst-gen)
;(trace cgen)
;(trace cgen/list)
;(trace cgen/arr)
;(trace cgen/seq)
