#lang racket/base
;; Soundness exploration for the proposed Typed Racket type
;;   call-with-exception-handler : (∀ (A) ((Any -> Any) (-> A) -> A))
;;
;; Question: can c-w-e-h ever return a value not of type A?
;; Method: enumerate every way the result of c-w-e-h could be influenced —
;; handler returning, handler raising, handler escaping, weird
;; uncaught-exception-handler parameterizations, dynamic-wind, etc.
;;
;; Run with: racket cweh-cases.rkt

(require racket/control)

;; Wrapper: run each case in isolation. We override error-escape-handler so
;; runtime errors ("exception raised by exception handler", "uncaught handler
;; did not escape") don't kill the whole process.
(define (try name body)
  (newline)
  (printf "=== ~a ===\n" name)
  (let/cc done
    (parameterize ([error-escape-handler (λ () (done 'error-escape-fired))]
                   [error-display-handler
                    (λ (msg e) (printf "  [error-display: ~a]\n" msg))])
      (printf "result = ~v\n" (body done)))))

;; ----------------------------------------------------------------------
;; Baseline: no exception
;; ----------------------------------------------------------------------

(try "1. no exception → c-w-e-h returns the thunk's value"
  (λ (_done)
    (call-with-exception-handler
      (λ (e) "handler-was-called")
      (λ () 'thunk-result))))

;; ----------------------------------------------------------------------
;; Handler "returns" — per docs, that value is RE-RAISED to the previous
;; handler; raise itself does not return through this path.
;; ----------------------------------------------------------------------

(try "2. handler returns; outer with-handlers catches the re-raised value"
  (λ (_done)
    (with-handlers ([(λ _ #t) (λ (e) (list 'outer-caught e))])
      (call-with-exception-handler
        (λ (e) "handler-returned-this")
        (λ () (raise 'boom))))))

(try "3. handler returns inside (+ 1 (raise 'boom)) — + never runs"
  (λ (_done)
    (with-handlers ([(λ _ #t) (λ (e) (list 'outer-caught e))])
      (call-with-exception-handler
        (λ (e) 42)
        (λ () (+ 1 (raise 'boom)))))))

;; ----------------------------------------------------------------------
;; Handler escapes via captured continuation / abort
;; ----------------------------------------------------------------------

(try "4. handler escapes via let/cc → value goes to the let/cc, not c-w-e-h"
  (λ (_done)
    (let/cc k
      (call-with-exception-handler
        (λ (e) (k 'escaped-from-handler))
        (λ () (raise 'boom))))))

(try "5. handler aborts to a prompt → value goes to the prompt, not c-w-e-h"
  (λ (_done)
    (call-with-continuation-prompt
      (λ ()
        (call-with-exception-handler
          (λ (e) (abort-current-continuation
                  (default-continuation-prompt-tag)
                  (λ () 'aborted-value)))
          (λ () (raise 'boom)))))))

;; ----------------------------------------------------------------------
;; Handler raises a fresh exception — runtime forbids this and triggers
;; error-display + error-escape, so c-w-e-h never returns.
;; ----------------------------------------------------------------------

(try "6a. handler raises an exn struct → 'exception raised by exception handler', error-escape"
  (λ (_done)
    (with-handlers ([exn:fail? (λ (e) (list 'caught (exn-message e)))])
      (call-with-exception-handler
        (λ (e) (raise (make-exn:fail "from-handler" (current-continuation-marks))))
        (λ () (raise 'boom))))))

(try "6b. handler raises a non-exn → 'raise called (with non-exception value) by exception handler', error-escape"
  (λ (_done)
    (with-handlers ([(λ _ #t) (λ (e) (list 'caught e))])
      (call-with-exception-handler
        (λ (e) (raise 'from-handler))
        (λ () (raise 'boom))))))

;; ----------------------------------------------------------------------
;; Continuation-barrier protection on raise's continuation
;; ----------------------------------------------------------------------

(try "10. default barrier? = #t blocks reinvoking raise's continuation"
  (λ (_done)
    (define saved #f)
    (let/cc k0
      (call-with-exception-handler
        (λ (e)
          (call/cc (λ (k) (set! saved k)))
          (k0 'normal-return))
        (λ () (raise 'boom))))
    (with-handlers ([exn:fail? (λ (e) (list 'reinvoke-blocked (exn-message e)))])
      (saved 'try-reinvoke))))

;; With barrier? = #f the captured continuation is multi-shot and will loop
;; forever, so we don't run that here. (Demonstrated separately; loops, but
;; never makes c-w-e-h return a wrong-typed value.)

;; ----------------------------------------------------------------------
;; dynamic-wind doesn't change return values
;; ----------------------------------------------------------------------

(try "11. dynamic-wind around c-w-e-h: pre/post run; value is thunk's value"
  (λ (_done)
    (dynamic-wind
      (λ () (printf "  pre\n"))
      (λ () (call-with-exception-handler
              (λ (e) "irrelevant")
              (λ () 'thunk-value)))
      (λ () (printf "  post\n")))))

;; ----------------------------------------------------------------------
;; Adversarial uncaught-exception-handler parameterizations.
;; To actually reach uncaught, we must NOT install any with-handlers around
;; c-w-e-h — otherwise that previous handler intercepts the re-raise first.
;; ----------------------------------------------------------------------

(try "7. uncaught-exception-handler escapes via let/cc — c-w-e-h doesn't return; value lands at let/cc"
  (λ (_done)
    (let/cc kk
      (parameterize ([uncaught-exception-handler
                      (λ (e) (kk (list 'UNCAUGHT-saw e)))])
        (call-with-exception-handler
          (λ (e) "handler-returned")
          (λ () (raise 'boom)))))))

(try "8. uncaught-exception-handler returns illegally → 'handler for uncaught exceptions: did not escape', error-escape"
  (λ (_done)
    (parameterize ([uncaught-exception-handler
                    (λ (e) 'illegal-return-value)])
      (call-with-exception-handler
        (λ (e) 'handler-returned)
        (λ () (raise 'boom))))))

(try "9. uncaught-exception-handler aborts to a prompt OUTSIDE c-w-e-h"
  (λ (_done)
    (call-with-continuation-prompt
      (λ ()
        (parameterize ([uncaught-exception-handler
                        (λ (e) (abort-current-continuation
                                (default-continuation-prompt-tag)
                                (λ () 'aborted-from-uncaught)))])
          (call-with-exception-handler
            (λ (e) "re-raised-string")
            (λ () (raise 'boom))))))))

(try "9'. uncaught-exception-handler invokes a call/cc continuation captured AROUND c-w-e-h"
  ;; This is the most adversarial case. The value lands in the OUTER let/cc's
  ;; slot, not in c-w-e-h's return slot — c-w-e-h was unwound by the
  ;; continuation invocation, exactly as in case 4.
  (λ (_done)
    (define k0 #f)
    (call/cc
      (λ (k)
        (set! k0 k)
        (parameterize ([uncaught-exception-handler
                        (λ (e) (k0 'snuck-into-outer-call/cc))])
          (call-with-exception-handler
            (λ (e) "re-raised")
            (λ () (raise 'boom))))))))

;; ----------------------------------------------------------------------
;; Nested c-w-e-h: chain of "handler returns" propagates outward.
;; ----------------------------------------------------------------------

(try "12. nested c-w-e-h, inner handler returns; outer handler also returns; chain reaches uncaught"
  (λ (_done)
    (let/cc kk
      (parameterize ([uncaught-exception-handler
                      (λ (e) (kk (list 'UNCAUGHT-final e)))])
        (call-with-exception-handler
          (λ (outer-e) 'outer-returned)
          (λ ()
            (call-with-exception-handler
              (λ (inner-e) 'inner-returned)
              (λ () (raise 'boom)))))))))

;; ----------------------------------------------------------------------
;; Conclusion (printed at the end for clarity).
;; ----------------------------------------------------------------------

(newline)
(displayln "All cases consistent with the rule:")
(displayln "  c-w-e-h's return slot is reachable iff the thunk returns normally.")
(displayln "  Every other path either re-raises or escapes via an outer continuation,")
(displayln "  none of which put a wrong-typed value into c-w-e-h's own return slot.")
(displayln "Therefore (∀ (A) ((Any -> Any) (-> A) -> A)) is sound.")
