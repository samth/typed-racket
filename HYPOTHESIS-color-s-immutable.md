# Hypothesis: Color% Missing s-immutable Field

## Problem Statement

When using the "insert large letters" dialog in DrRacket, an error occurs:
```
color->immutable-color
  /Users/robby/git/plt/racket/collects/racket/draw/private/color.rkt:109:0
```

The error happens because untyped code tries to access the `s-immutable` field on a Color% object that came from typed code.

## Root Cause Analysis

### What's Happening

1. **Color% Type Definition** (typed-racket-more/typed/racket/private/gui-types.rkt:105-119)
   - The `Color%` type defines methods like `is-immutable?`, `red`, `green`, `blue`, etc.
   - **MISSING**: The type does NOT define the `s-immutable` field

2. **Untyped Racket Code** (racket/draw/private/color.rkt)
   - The function `color-is-immutable?` uses `class-field-accessor` to access the `s-immutable` field
   - The function `color->immutable-color` calls `color-is-immutable?`

3. **Contract Boundary**
   - When a Color% object crosses from typed to untyped code, Typed Racket generates an `object/c-opaque` contract
   - This contract ONLY includes fields/methods explicitly listed in the type
   - Fields not in the type are protected by `restrict-typed-field/c` which blocks all access

4. **The Error**
   - Untyped code tries: `(get-field s-immutable color-obj)`
   - The contract blocks this with: "cannot read or write field hidden by Typed Racket"

### Why This Is The Issue

From `typed-racket/utils/opaque-object.rkt` (lines 22-27):
```racket
;; Fields:
;; -------
;; Fields are blocked from access without a contract in all cases.
```

The `object/c-opaque` contract (lines 61-75):
- Gets the actual fields on the object
- Removes fields that are in the contract
- For remaining fields, applies `restrict-typed-field/c` which blocks access

The `restrict-typed-field/c` contract (lines 196-209):
- Raises a blame error: "cannot read or write field hidden by Typed Racket"

## Solution

Add the `s-immutable` field to the `Color%` type definition:

```racket
(define-type Color%
  (Class (init-rest (U (List)
                       (List Byte Byte Byte)
                       (List Byte Byte Byte Real)
                       (List String)))
         (field [s-immutable Boolean])  ; ADD THIS LINE
         [red (-> Byte)]
         [green (-> Byte)]
         [blue (-> Byte)]
         [alpha (-> Real)]
         [set (case->
               (Byte Byte Byte -> Void)
               (Byte Byte Byte Real -> Void))]
         [copy-from ((Instance Color%) -> (Instance Color%))]
         [is-immutable? (-> Boolean)]
         [ok? (-> #t)]))
```

## Other Types to Check

The following types also have `is-immutable?` methods and may need the field:
- `Brush%` (line 160)
- `Pen%` (line 191)

## Test Cases Created

1. **typed-racket-test/succeed/color-s-immutable-field.rkt**
   - Shows that with the field in the type, untyped code can access it

2. **typed-racket-test/fail/color-missing-s-immutable-field.rkt**
   - Shows that without the field in the type, access is blocked

3. **test-color-field-access.rkt** (development test)
   - Demonstrates both success and failure cases

## References

- Chat conversation with robby about the issue
- `typed-racket/utils/opaque-object.rkt` - opaque object contract implementation
- `typed-racket/static-contracts/combinators/object.rkt` - object contract combinators
- `typed-racket-more/typed/racket/private/gui-types.rkt` - GUI type definitions
