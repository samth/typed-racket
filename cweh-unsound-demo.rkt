#lang typed/racket/base
;; Demonstration for the call-with-exception-handler discussion in
;; issue #1505. Run with: racket cweh-unsound-demo.rkt
;;
;; What this shows
;; ---------------
;; A handler installed by `call-with-exception-handler` CAN choose the
;; result of the surrounding call — not by returning normally (Racket
;; re-raises that), but by tail-calling a captured continuation that
;; lives inside the raised value. The helper module implements such a
;; raise-continuable: the continuation of the raise call is captured
;; into a `k-box`, the handler pulls it out, and tail-calls it with
;; whatever value it likes. That value flows back as `make-raise-
;; continuable`'s return, hence as the thunk's return, hence as the
;; surrounding `call-with-exception-handler`'s return.
;;
;; This mirrors the formal R6RS semantics for `with-exception-handler`
;; and `raise-continuable` Robby pointed at, and the same shape that
;; rnrs/exceptions-6 uses on top of Racket.
;;
;; What this does NOT show
;; -----------------------
;; This program does NOT exhibit Typed Racket unsoundness. The static
;; type of `result` is `Any`, and the runtime value is a string —
;; which is a perfectly legitimate inhabitant of `Any`. TR's current
;; built-in type
;;
;;   call-with-exception-handler : (∀ a. (Any -> a) (-> a) -> a)
;;
;; produces the same outcome on the same code (a = Any here). The
;; program type-checks and runs without `unsafe-require/typed`.
;;
;; To go from `Any` to a more specific type the user has to write
;; `(cast result T)`, and the runtime contract on `cast` catches the
;; mismatch. So nothing leaks past the type system without a runtime
;; check; the current and the proposed types both rely on that.
;;
;; What would be needed for real unsoundness in TR
;; -----------------------------------------------
;; Either (a) a path where the handler's normal RETURN flows back as
;; the result of `call-with-exception-handler` without a cast in the
;; way (Racket's c-w-e-h doesn't have such a path; cases 2/3 of the
;; earlier scenario file confirmed it re-raises), or (b) a helper that
;; type-erases the captured continuation AND a way to assert a more
;; specific type without cast (only available via unsafe-require/typed
;; or unsafe-cast — both explicitly unsafe). Without one of those, the
;; proposed type
;;
;;   call-with-exception-handler : (∀ A. (Any -> Any) (-> A) -> A)
;;
;; appears sound for Racket's `call-with-exception-handler`, even
;; though it's strictly more permissive than the current type (it
;; admits cloudrac3r's example-1, which the current type rejects).

(require (file "cweh-unsound-helper.rkt"))

(define result : Any
  (call-with-exception-handler
    (lambda ([e : Any])
      (cond
        [(k-box? e)
         ;; Tail-call the captured continuation with a string.
         ((k-box-k e) "value chosen by the handler")]
        [else 0]))
    (lambda () (make-raise-continuable 'boom))))

(printf "result          = ~v\n" result)
(printf "(string? result) = ~v\n" (string? result))
(printf "static type of result is Any — that is consistent.\n")

(printf "\nIf we now (cast result Integer), the contract on cast catches it:\n")
(with-handlers ([exn:fail? (lambda ([e : exn]) (printf "  CAST CRASH: ~a\n" (exn-message e)))])
  (define n (cast result Integer))
  (printf "  (* 2 n) = ~v\n" (* 2 n)))
