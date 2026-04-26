#lang typed/racket/base
;; Concrete soundness counterexample for the type proposed in issue #1505:
;;
;;   call-with-exception-handler : (∀ (A) ((Any -> Any) (-> A) -> A))
;;
;; This program type-checks and claims `result : Integer`, but at runtime
;; `result` is the string "definitely not an Integer" and using it as an
;; integer crashes. The mechanism — a captured continuation embedded in the
;; raised value — is exactly what the R6RS formal semantics for
;; with-exception-handler permits, and what rnrs/exceptions-6 implements on
;; top of Racket. (This file uses a hand-rolled k-box for clarity; the
;; structure is identical to rnrs:raise-continuable.)
;;
;; Run with: racket cweh-unsound-demo.rkt
;;
;; Note: we use `unsafe-require/typed` so that no `parametric->/c` contracts
;; are inserted at the boundary. That mirrors how a base-env entry for
;; call-with-exception-handler is treated: the type is trusted within typed
;; code with no runtime contract enforcement.

(require typed/racket/unsafe)

(unsafe-require/typed "cweh-unsound-helper.rkt"
  [#:opaque KBox k-box?]
  [k-box-k (-> KBox (-> Any Nothing))]
  ;; make-raise-continuable can in fact return Any when the handler
  ;; reinvokes the captured continuation, but we type it Nothing to
  ;; emulate the way `raise` is typed in TR — that's part of why the
  ;; combination with the proposed cweh type is unsound.
  [make-raise-continuable (-> Any Nothing)])

;; Forge cloudrac3r's proposed type for call-with-exception-handler:
(unsafe-require/typed racket/base
  [(call-with-exception-handler cweh)
   (All (A) (-> (-> Any Any) (-> A) A))])

(: trust-me (-> Integer))
(define (trust-me)
  (cweh
    (lambda ([e : Any])
      (cond
        [(k-box? e)
         ;; Tail-call the captured continuation with a string.
         ((k-box-k e) "definitely not an Integer")]
        [else 0]))
    (lambda () (make-raise-continuable 'boom))))

(define result (trust-me))

(printf "Typed Racket statically thinks  result : Integer\n")
(printf "  result            = ~v\n" result)
(printf "  (string? result)  = ~v\n" (string? result))
(printf "  (integer? result) = ~v\n" (integer? result))

(printf "Now use it as Integer — compute (* 2 result):\n")
(with-handlers ([exn:fail? (lambda ([e : exn]) (printf "  CRASH: ~a\n" (exn-message e)))])
  (printf "  (* 2 result) = ~v\n" (* 2 result)))
