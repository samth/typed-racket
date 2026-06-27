#lang racket/base
(require syntax/modcollapse (for-template racket/base) racket/match racket/list)
(define to-require null)
(define (add-mod! m)
  (set! to-require (cons m to-require)))

(define (do-requires [ns (current-namespace)])
  (parameterize ([current-namespace ns])
    (for ([m (in-list to-require)]
          #:when m)
      (dynamic-require (module-path-index-join '(submod "." #%type-decl) m)
                       #f))))

;; adjust: require-spec -> require-spec
;; rewrite a spec that works in a module M to one that works in a submodule of M
(define (adjust p)
  (match p
    [`(submod "." ,r0 ,rest ...)
     `(submod ".." ,r0 . ,rest)]
    [`(submod ,(and up (or "." "..")) ,rest ...)
     `(submod ".." ,up . ,rest)]
    [_ p]))

;; ->mp : module-path-index? symbol? -> require-spec
;; combine a module-path-index with a submodule, producing an sexp we can manipulate
(define (->mp mpi submod)
  (collapse-module-path-index (module-path-index-join `(submod "." ,submod) mpi)))

;; generate code to require the modules that have the definitions of the
;; predefined contracts, so references to them resolve in the residual program
(define (get-contract-requires)
  (filter-map
   (lambda (m)
     (and m
          (let ([mpi (module-path-index-join '(submod "." #%contract-defs) m)])
            ;; only require modules that actually have a #%contract-defs submodule
            (and (module-declared? mpi #t)
                 #`(#%require #,(adjust (->mp m '#%contract-defs)))))))
   to-require))

;; dynamically require the #%contract-defs-names submodules, which populate
;; the predef-contracts table.  Tolerant: modules without that submodule
;; (i.e. ones that register no predefined contracts) are simply skipped.
(define (do-contract-requires [ns (current-namespace)])
  (parameterize ([current-namespace ns])
    (for ([m (in-list to-require)]
          #:when m)
      (define mpi (module-path-index-join '(submod "." #%contract-defs-names) m))
      (when (module-declared? mpi #t)
        (dynamic-require mpi #f)))))

(provide add-mod! do-requires
         get-contract-requires do-contract-requires)
