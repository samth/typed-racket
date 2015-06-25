#lang racket/unit

(require "../utils/utils.rkt"
	 (types abbrev union subtype restrict)
         (rep object-rep)
	 unstable/sequence
         "fail.rkt" "signatures.rkt" "constraint-structs.rkt"
         racket/match
         racket/list)

(import dmap^)
(export constraints^)

;; Widest constraint possible
(define no-constraint (make-c (Un) Univ -empty-obj))

;; Create an empty constraint map from a set of type variables X and
;; index variables Y.  For now, we add the widest constraints for
;; variables in X to the cmap and create an empty dmap.
(define (empty-cset X Y)
  (make-cset (list (cons (for/hash ([x (in-list X)])
                           (values x no-constraint))
                         (make-dmap (make-immutable-hash null))))))


;; add the constraints S <: var <: T to every map in cs
(define (insert cs var S T obj)
  (match cs
    [(struct cset (maps))
     (make-cset (for/list ([(map dmap) (in-pairs maps)])
                  (cons (hash-set map var (make-c S T (or obj -empty-obj)))
                        dmap)))]))

;; meet: Type Type -> Type
;; intersect the given types. produces a lower bound on both, but
;; perhaps not the GLB
(define (meet S T obj)
  (let ([s* (restrict S T)])
    (if (and (subtype s* S #:obj obj)
             (subtype s* T #:obj obj))
        s*
        (Un))))

;; join: Type Type -> Type
;; union the given types
(define (join T U) (Un T U))

(define (join-objs o o*)
  (cond
    [(and o
          (or (object-equal? o o*)
              (and (non-empty-obj? o)
                   (not (non-empty-obj? o*)))))
     o]
    [else -empty-obj]))

;; meet of two variable constraints
;; never fails
;; if var is provided, the resulting constraint uses it, otherwise it
;; uses the variable from `c1` (which must be the same as the one from
;; `c2`)
(define (c-meet c1 c2 [var #f])
  ;(printf "c-meet ~a ~a [var ~a]\n\n" c1 c2 var)
  (match*/early (c1 c2)
    [((struct c (S T o)) (struct c (S* T* o*)))
     (let ([S (join S S*)]
           [T (meet T T* o)]
           [o (join-objs o o*)])
       (and (subtype S T #:obj o)
            (make-c S T o)))]))


;; compute the meet of two constraint sets
;; returns #f for failure
(define cset-meet
  (case-lambda
    [() (empty-cset null null)]
    [(x) x]
    [(x y)
     (match* (x y)
      [((struct cset (maps1)) (struct cset (maps2)))
       (define maps (for*/list ([(map1 dmap1) (in-pairs (remove-duplicates maps1))]
                                [(map2 dmap2) (in-pairs (remove-duplicates maps2))]
                                [v (in-value (% cons
                                                (hash-union/fail map1 map2 #:combine c-meet)
                                                (dmap-meet dmap1 dmap2)))]
                                #:when v)
                      v))
       (cond [(null? maps)
              #f]
             [else (make-cset maps)])])]
    [(x . ys)
     (for/fold ([x x]) ([y (in-list ys)])
       (% cset-meet x y))]))

;; combines a list of csets using cset-meet individually
;; returns #f for failure
(define (cset-meet* args)
  (apply cset-meet args))

;; produces a cset of all of the maps in all of the given csets
;; FIXME: should this call `remove-duplicates`?
(define (cset-join l)
  (let ([mapss (map cset-maps l)])
    (make-cset (apply append mapss))))
