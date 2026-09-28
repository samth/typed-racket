# Typed Racket: Alternatives to Fix Missing Expected Type for Keyword Function Arguments (Issue #1464)

This document proposes alternative approaches to address the issue where Typed Racket does not provide an expected type when type checking the arguments to a keyword function.

Repository context: this write-up references files under `typed-racket-lib/typed-racket/typecheck/`.

## Problem Statement

Currently, calls to keyword functions typecheck keyword-argument expressions without an expected type. As a result, constructs that rely on expected types (e.g., lambdas, polymorphic uses) fail or infer less precisely in keyword positions. Positional arguments already benefit from expected-type propagation and heuristics in several paths; keyword arguments do not.

## Affected Code Paths

- `tc-app/tc-app-keywords.rkt`: parses and checks keyword applications; runs the keyword loop and delegates positional args to `tc/funapp`.
- `tc-app/tc-app-main.rkt`: uses an “agreement across arrows” heuristic to provide per-argument expected types for positional args.
- `tc-funapp.rkt`: the core function application checker, including case-> selection, inference, and expected-type use for positional args.

---

## Plan 1: General Propagation for Keyword Args

### Summary
Typecheck each keyword-argument expression with its formal keyword type as the expected type, and apply the “agreement across arrows” heuristic to keywords where applicable.

### Key Changes
- In `tc-app-keywords.rkt`, avoid eagerly computing keyword-arg types via `(stx-map tc-expr/t kw-args)`. Instead, upon matching a formal `(Keyword: k* t req?)`, typecheck the corresponding argument with expected type `t` (e.g., via `tc-expr/check` or `single-value` with an expected).
- When multiple `case->` arrows survive keyword filtering, compute a per-keyword “consensus expected type” (analogous to `tc/app-main.rkt` for positional args). If all remaining arrows agree on a keyword’s type, use it as the expected for that keyword argument.
- Continue delegating positional arguments to `tc/funapp`, preserving existing expected-type behavior.

### Pros
- Consistent fix: keyword arguments benefit from expected types like positional args.
- Mostly localized to `tc-app-keywords.rkt`.
- Earlier, more precise errors for mismatched keyword arguments.

### Cons/Risks
- Error ordering may change; keyword mismatches could be reported earlier.
- Care is needed to avoid evaluating unmatched or absent keywords.

### Tests
- Success: lambdas/polymorphic expressions as keyword args that require expected types.
- Failure: ensure wrong keyword-arg types are reported at the keyword site with clear messages.
- Mixed `case->` signatures with consistent vs inconsistent keyword types.

---

## Plan 2: Special-Case When No Keyword Arguments

### Summary
If a keyword function is called with zero keyword arguments, route the application through the regular positional-argument path so those args benefit from existing expected-type heuristics.

### Key Changes
- In `tc-app-keywords.rkt`, detect empty `kw-arg-list`, bypass the keyword loop, and delegate to the same path as `tc/app-regular` (or directly invoke `tc/funapp` with per-arg expectations derived via the `tc-app-main.rkt` heuristic).

### Pros
- Very simple, low-risk improvement for a common case.
- No changes to keyword matching or error handling when keywords are present.

### Cons/Risks
- Does not improve cases where keyword arguments are supplied.
- Maintains divergence between positional and keyword paths.

### Tests
- Optional-keyword function called without keywords: positional lambdas should infer using per-arg expectations.
- Ensure behavior unchanged when keywords are present.

---

## Plan 3: Better Loop Heuristic When No Overall Expected Type

### Summary
After filtering arrows by viable keyword sets, compute per-argument expected types for both positional and keyword arguments using agreement across the surviving arrows. Use these to typecheck subexpressions in the absence of an overall expected type.

### Key Changes
- In `tc-app-keywords.rkt`, run a two-phase process: (1) filter arrows by keyword viability (non-error mode), (2) for provided keywords and positional args, compute agreement-based expected types across the remaining arrows and typecheck subexpressions with those expectations. Fall back to current behavior when there is no agreement.

### Pros
- Improves the no-expected-type scenario specifically (requested in the issue).
- Localized to keyword application handling; reuses established heuristics.

### Cons/Risks
- More complex control flow (filter → agree → check).
- No benefit when surviving arrows disagree on types.

### Tests
- `case->` where keywords prune the set; verify improved inference via agreement for both keyword and positional args.
- Ambiguous cases should fall back gracefully without regressions.

---

## Plan 4: Centralize Keyword Handling in `tc/funapp`

### Summary
Move keyword argument checking into `tc/funapp`, unifying positional and keyword logic for agreement, expected typing, and inference.

### Key Changes
- Extend `tc/funapp` and arrow application logic to accept and check keyword arguments alongside positional:
  - Match keyword sets against each arrow.
  - Apply per-arg expected types to keywords using the same heuristics as for positionals.
  - Where sound and supported, incorporate keyword types into polymorphic inference.
- Reduce `tc-app-keywords.rkt` to desugaring and structured handoff into `tc/funapp`.

### Pros
- Single source of truth for application typing; fewer duplicated heuristics.
- Natural place to integrate keyword types into inference and object/prop handling.
- Better long-term maintainability.

### Cons/Risks
- Largest footprint and regression surface; requires thorough test coverage.
- Must preserve error-message quality and ordering.

### Tests
- Matrix across required/optional keywords, intersections, polymorphism, row/PolyRow, with/without overall expected type.
- Error priority and message stability.

---

## Plan 5: Minimal-Risk `check-below` for Keyword Args

### Summary
Keep current structure, but after computing each keyword-arg type, run `check-below` against the formal keyword type. This triggers expected-style checking paths (e.g., lambdas) without reworking the loop.

### Key Changes
- In `tc-app-keywords.rkt`, for matched `(Keyword: k* t req?)`, send the kw-arg’s `tc-result` to `check-below` with expected `(ret t)` instead of only subtyping.

### Pros
- Smallest conceptual change; leverages existing checking machinery used for positional args.
- Improves keyword-arg expressiveness where constructs react to being “checked”.

### Cons/Risks
- Initial kw-arg types are still synthesized without expectations; some constructs only improve when starting with an expected type.
- Does not add agreement heuristics for keywords.

### Tests
- Keyword args that previously needed an expected type (especially lambdas).
- Ensure no regressions when types are already precise.

---

## Recommendations
- Quick, low-risk improvement: combine Plan 2 (no-keywords fast-path) with Plan 5 (`check-below` for provided keywords).
- Principled, localized fix with good payoff: Plan 1.
- Long-term convergence and maintainability: Plan 4 (requires broader testing and careful migration).

## Open Questions / Edge Cases
- Interaction with `RestDots?` and mandatory keyword parameters across intersections and polymorphic cases.
- Error ordering consistency compared to today’s messages.
- Whether to incorporate keyword types into inference (Plan 4) and under what constraints.

## Code Pointers
- Keyword application entry: `typed-racket-lib/typed-racket/typecheck/tc-app/tc-app-keywords.rkt`
- Dispatch and agreement heuristic for positional args: `tc-app/tc-app-main.rkt`
- Core function application and inference: `tc-funapp.rkt`

