#lang racket/base

(require racket/list racket/match
         syntax/id-table
         (except-in "../utils/utils.rkt" env)
         (contract-req)
         (rep type-rep)
         (rep object-rep type-rep rep-utils filter-rep)
         (only-in "../utils/tc-utils.rkt" int-err))

(define Any (make-Univ))
;; ty+ is the known type of this obj
;; ty- is the type this obj is known to not be
(define-struct/cond-contract type-info ([ty+ (and/c Type? (not/c Bottom?) (not/c Refine?))]
                                        [ty- (or/c #f (and/c Type? (not/c Bottom?) (not/c Univ?)))])
  #:transparent
  #:property prop:custom-write
  (lambda (ti prt mode)
    (fprintf prt "[(+ ~a),(- ~a)]" 
             (type-info-ty+ ti)
             (and (type-info-ty- ti) ""))))

(define top-type-info (type-info Any #f))

;; id-table is a free-id-table of identifiers to type-info *OR* aliased object
;;   (if an id aliases an object, then you must look up that object for its type info)
;; props is a list of known propositions
;; aliases is a free-id-table of identifiers to objects
;; SLIs is the list of current linear constraint systems
(define-struct/cond-contract env ([id-table immutable-free-id-table?]
                                  [lexp-table (and/c hash? hash-equal? immutable?)]
                                  [props (listof Filter/c)]
                                  [SLIs (listof SLI?)])
  #:transparent
  #:property prop:custom-write
  (lambda (e prt mode)
    (fprintf prt "(ENV \n  {id Types/Aliases: ~a}\n  {LExp Types: ~a}\n  {SLIs: ~a}\n  {Props: ~a})" 
             (free-id-table-map (env-id-table e) list)
             (hash-map (env-lexp-table e) list)
             (env-SLIs e)
             (env-props e))))

(provide/cond-contract
  [env? predicate/c]
  [raw-lookup-id-type (env? identifier? (identifier? . -> . any) . -> . any)]
  [raw-lookup-id-not-type (env? identifier? (identifier? . -> . any) . -> . any)]
  [lookup-lexp-type (env? LExp? procedure? . -> . any)]
  [env-props (env? . -> . (listof Filter/c))]
  [env-props+SLIs (env? . -> . (listof Filter/c))]
  [env-SLIs (env? . -> . (listof SLI?))]
  [replace-props (env? (listof Filter/c) . -> . env?)]
  [empty-env env?]
  [raw-lookup-alias (env? identifier? (identifier? . -> . (or/c #f Object?)) . -> . (or/c #f non-empty-obj?))]
  [env-extract-props (env? . -> . (values env? (listof Filter/c)))]
  [env-extract-props+slis (env? . -> . (values env? (listof (and/c Filter/c
                                                                   (not/c SLI?))) (listof SLI?)))]
  [naive-extend/id-type-info (env?
                              identifier?
                              (and/c Type/c
                                     (not/c Bottom?)
                                     (not/c Refine?))
                              (and/c Type/c
                                     (not/c Univ?))
                              . -> . env?)]
  [naive-extend/id-type+ (env? identifier? (and/c Type/c
                                              (not/c Bottom?)
                                              (not/c Refine?))
                           . -> . env?)]
  [naive-extend/id-type- (env? identifier? Type/c . -> . env?)]
  [naive-extend/id-types (env? (listof (cons/c identifier? (and/c Type/c
                                                               (not/c Bottom?)
                                                               (not/c Refine?)))) 
                            . -> . env?)]
  [extend/aliases (env? (listof (cons/c identifier? non-empty-obj?)) 
                        . -> . env?)]
  [env-erase-id-type (-> env? identifier? env?)]
  [env-erase-lexp-type (-> env? LExp? env?)]
  [naive-extend/lexp-type (-> env? LExp? Type/c env?)])


(define empty-env
  (env
   (make-immutable-free-id-table)
   (hash)
   null
   null))

(define (env-extract-props e)
  (match-let ([(env idt lexpt ps sli) e])
    (values (env idt lexpt null null) (append sli ps))))

(define (env-extract-props+slis e)
  (match-let ([(env idt lexpt ps sli) e])
    (values (env idt lexpt null null) ps sli)))

(define (env-props+SLIs e)
  (match-let ([(env _ _ ps sli) e])
    (append sli ps)))

(define (replace-props e new-ps)
  (match-let ([(env idt lexpt _ _) e])
    (define-values
      (slis* ps*) (partition SLI? new-ps))
    (env idt lexpt ps* slis*)))

#;(define (replace-SLIs e slis)
  (match-let ([ e])
    (env tys ntys props als slis)))

(define (raw-lookup-id-type e key fail)
  (define v (free-id-table-ref (env-id-table e) key (λ () #f)))
  (cond
    [(type-info? v) (type-info-ty+ v)]
    [else (fail key)]))

(define (lookup-lexp-type e key fail)
  (hash-ref (env-lexp-table e) key fail))

(define (raw-lookup-id-not-type e key fail)
  (define v (free-id-table-ref (env-id-table e) key (λ () #f)))
  (cond
    [(and (type-info? v)
          (type-info-ty- v))
     => values]
    [else (fail key)]))


(define (env-erase-id-type e id)
  (match-let ([(env idt lexpt ps sli) e])
    (env (free-id-table-remove idt id)
         lexpt
         ps
         sli)))

(define (env-erase-lexp-type e lexp)
  (match-let ([(env idt lexpt ps sli) e])
    (env idt
         (hash-remove lexpt lexp)
         ps
         sli)))

;; extend that works on single arguments
(define (naive-extend/id-type-info e id t+ t-)
  (match-let ([(env idt lexpt ps sli) e])
    (env (free-id-table-set idt id (type-info t+ (and (not (Bottom? t-)) t-)))
         lexpt
         ps
         sli)))


(define (naive-extend/id-type e id type)
  (naive-extend/id-types e (list (cons id type))))

(define (naive-extend/id-type+ e id type)
  (naive-extend/id-types e (list (cons id type))))

(define (naive-extend/lexp-type e l type)
  (match-let ([(env idt lexpt ps sli) e])
    (env idt (hash-set lexpt l type) ps sli)))

;; not-type extend that works on single arguments
(define (naive-extend/id-type- e id type-)
  (cond
    [(Bottom? type-) e]
    [else
     (match-let ([(env idt lexpt ps sli) e])
       (define ti (free-id-table-ref idt id (λ () top-type-info)))
       (cond
         [(type-info? ti)
          (env (free-id-table-set idt id (type-info (type-info-ty+ ti) type-))
               lexpt
               ps
               sli)]
         [else (int-err "extending type- for id aliasing an object. id ~a, aliasing ~a"
                        id ti)]))]))

;; extends an environment with types (no aliases)
;; DOES NOT FLATTEN NESTED REFINEMENT TYPE PROPS
(define (naive-extend/id-types e ids/types)
  (match-let*
      ([(env idt lexpt ps sli) e]
       [idt* (for/fold ([idt idt]) 
                       ([id/ty (in-list ids/types)])
               (match-define (cons id ty) id/ty)
               (define ti (free-id-table-ref idt id (λ () top-type-info)))
               (cond
                 [(type-info? ti)
                  (free-id-table-set idt id (type-info ty (type-info-ty- ti)))]
                 [else (int-err "extending w/ type for id aliasing an object. id ~a, aliasing ~a"
                                id ti)]))])
    (env idt* lexpt ps sli)))

(define (raw-lookup-alias e id fail)
  (define a (free-id-table-ref (env-id-table e) id (λ () #f)))
  (or (and (non-empty-obj? a) a)
      (fail id)))

;; extends an environment with aliases
(define (extend/aliases e ids/aliases)
  (match-let*
      ([(env idt lexpt ps sli) e]
       [idt* (for/fold ([idt idt]) 
                       ([id/al (in-list ids/aliases)])
               (match-define (cons id alias) id/al)
               (free-id-table-set idt id alias))])
    (env idt* lexpt ps sli)))


#|
(trace raw-lookup-id-type)
(trace raw-lookup-id-not-type)
(trace lookup-lexp-type)
(trace env-props)
(trace env-props+SLIs)
(trace env-SLIs)
(trace replace-props)
(trace raw-lookup-alias)
(trace env-extract-props)
(trace env-extract-props+slis)
(trace naive-extend/id-type-info)
(trace naive-extend/id-type+)
(trace naive-extend/id-type-)
(trace naive-extend/id-types)
(trace extend/aliases)
(trace env-erase-id-type)
(trace env-erase-lexp-type)
(trace naive-extend/lexp-type)
|#