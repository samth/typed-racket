#lang racket/base

(require (rename-in "../utils/utils.rkt")
         (rep type-rep object-rep filter-rep rep-utils)
         (prefix-in c: (contract-req))
         (types subtype base-abbrev)
         racket/match racket/lazy-require)

(provide unsafe-make-Refine*)

(lazy-require
 ["../typecheck/tc-subst.rkt" (subst-type subst-filter)]
 ["restrict.rkt" (restrict)]
 ["filter-ops.rkt" (-and)]
 ;["../infer/restrict.rkt" (infer)]
 ["remove-intersect.rkt" (remove)])
;; separates out obvious types (list 0 0) is and is not from other props
;; so refinement type can be restricted/updated with types it's directly
;; refined with
;; e.g. to help with simplifying (Refine [x : (U Bool Int)] (x -: Int)) and/or
;; (Refine [x : (U Bool Int)] (x -! Bool)) to Int, since they have
;; props which *directly* refine their type
(define/cond-contract (partition-refinement-prop p)
  (c:-> Filter?
        (values (c:listof Type?) ;; positive types for (list 0 0)
                (c:listof Type?) ;; negative types for (list 0 0)
                (c:listof Filter?))) ;; other props
  (match p
    [(TypeFilter: t (Path: '() (list 0 0)))
     (values (list (subst-type t (list 0 0) -empty-obj #t)) '() '())]
    [(NotTypeFilter: t (Path: '() (list 0 0)))
     (values '() (list (subst-type t (list 0 0) -empty-obj #t)) '())]
    [(AndFilter: ps)
     (define-values (tss+ tss- pss)
       (for/lists (ts+ ts- ps) ([p (in-list ps)])
         (partition-refinement-prop p)))
     (values (apply append tss+)
             (apply append tss-)
             (apply append pss))]
    [_ (values '() '() (list p))]))

;; unsafe-make-Ref
;; unsafe because (list 0 0) is exposed/free in p
;; since there is no Refine wrapper around this yet
(define/cond-contract (unsafe-make-Refine* t p)
  (c:-> Type? Filter? Type?)
  (cond
    ;; unnest refinements of refinements
    [(Refine? t)
     (match-let ([(Refine: x x-t x-p) t])
       (define p* (subst-filter p (list 0 0) (-id-path x) #t))
       (unsafe-make-Refine* x-t (subst-filter (-and x-p p*) x (-id-path (list 0 0)) #t)))]
    [else
     (match p
       [(TypeFilter: (Refine-unsafe: t-inner p-inner)
                     (Path: '() (list 0 0)))
        (unsafe-make-Refine* (restrict t-inner t) p-inner)]
       [(TypeFilter: t-inner (Path: '() (list 0 0)))
        (restrict t-inner t)]
       [(AndFilter: ps)
        (define-values (ts+ ts- ps*)
          (let-values ([(tss+ tss- pss) (for/lists (l1 l2 l3) ([p (in-list ps)])
                                          (partition-refinement-prop p))])
            (values (apply append tss+) (apply append tss-) (apply append pss))))
        (define t-after+
          (for/fold ([t t]) ([t* (in-list ts+)])
            (restrict t* t)))
        (define t-after-
          (for/fold ([t t-after+]) ([t* (in-list ts-)])
            (remove t t*)))
        (unsafe-make-Refine t-after- (apply -and ps*))]
       [_ (unsafe-make-Refine t p)])]))

