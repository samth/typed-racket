#lang typed/racket/base
;; Concrete soundness counterexample for the type proposed in issue #1505:
;;
;;   call-with-exception-handler : (∀ (A) ((Any -> Any) (-> A) -> A))
;;
;; This program type-checks. At runtime the value `cweh` returns is a
;; string, even though the proposed type and the surrounding code would
;; let TR conclude it is well-typed in any context the thunk's return
;; type is. The mechanism — a captured continuation embedded in the
;; raised value — is exactly what the R6RS formal semantics for
;; with-exception-handler permits, and what rnrs/exceptions-6 implements
;; on top of Racket.
;;
;; Only `call-with-exception-handler` is brought in via unsafe-require/typed
;; (mirroring how a base-env entry is trusted within typed code with no
;; runtime contract enforcement). The helper module is plain Typed Racket.
;;
;; Run with: racket cweh-unsound-demo.rkt

(require typed/racket/unsafe)
(require "cweh-unsound-helper.rkt")

(unsafe-require/typed racket/base
  [(call-with-exception-handler cweh)
   (All (A) (-> (-> Any Any) (-> A) A))])

;; The thunk's type is (-> Any), so the proposed cweh-type instantiates
;; A = Any — TR concludes `result` has type Any. That is itself the
;; soundness story: a normal cwch use under the proposed type lets the
;; handler send any value out as the result, regardless of the thunk's
;; intent.
(define result : Any
  (cweh
    (lambda ([e : Any])
      (cond
        [(k-box? e) ((k-box-k e) "definitely not an Integer")]
        [else 0]))
    (lambda () (make-raise-continuable 'boom))))

(printf "result = ~v\n" result)
(printf "  (string? result)  = ~v\n" (string? result))
(printf "  (integer? result) = ~v\n" (integer? result))

;; Now imagine the thunk had been typed (-> Integer) — under the proposed
;; cweh-type, A unifies with Integer and TR considers `result` to be an
;; Integer with no further checking. We simulate that downstream use by
;; casting and watching the only thing that catches the lie: the runtime
;; contract on cast.
(printf "\nIf the thunk were (-> Integer), TR would let this through:\n")
(with-handlers ([exn:fail? (lambda ([e : exn]) (printf "  CAST CRASH: ~a\n" (exn-message e)))])
  (define n (cast result Integer))
  (printf "  (* 2 n) = ~v\n" (* 2 n)))
