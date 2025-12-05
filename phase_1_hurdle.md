# Phase 1 Parser Hurdle: List Parsing Implementation

## Current Status

**Parse Success Rate**: 90.1% (73/81 examples parsing, 8 failures)

**Remaining Parse Failures**:
- i4.in, eval.in, queens.in - Prolog list syntax `[]`, `[a,b,c]`, `[H|T]`
- andrews.in, zebra4.in - Formula parser issues
- cn.in, mission.in - Operator edge cases
- zebra2.in - Multiple clauses per line

## Problem Description

Implemented Prolog list parsing support but encountered a critical bug and potential infinite loop:

### Bug Fixed
**Location**: src/parser/syntax.rs:946-972 (`parse_list_header` function)

**Issue**: The function `parse_list_header()` was matching `list([])` as a multi-line list section header (like `list(usable)`) instead of recognizing it as a clause containing a Prolog list term.

**Fix Applied** (line 961-963):
```rust
// Validate that name is a simple identifier (not a complex expression like [])
// List section names should be alphanumeric identifiers, not Prolog list syntax
if name.is_empty() || name.contains(|c: char| !c.is_alphanumeric() && c != '_') {
    return None;
}
```

This ensures list section names like "usable", "sos", "demodulators" are accepted, but `[]` and other complex expressions are rejected.

### Current Blocker

**Symptom**: Regression tests hang/timeout when run after the fix. Simple manual test (`list([]).`) works fine.

**Suspected Causes**:
1. **Infinite recursion** in `parse_list()` function (src/parser/syntax.rs:660-700)
2. **Infinite loop** when parsing lists containing complex terms
3. **Unrelated issue** triggered by the validation change

## Implementation Details

### List Parsing Function (src/parser/syntax.rs:660-700)

Desugars Prolog lists to nested `$cons` applications:
- `[]` → `$nil`
- `[a,b,c]` → `$cons(a, $cons(b, $cons(c, $nil)))`
- `[H|T]` → `$cons(H, T)`

**Potential Issues**:
1. Line 665: `let inner = &text[1..text.len() - 1].trim();` - Creates `&&str` instead of `&str`
2. Recursive calls to `parse_term()` which may call back to `parse_list()` - could cause infinite loop if not making progress
3. `split_arguments()` might not handle edge cases correctly

### Integration Point

Line 545-548 in `parse_term()`:
```rust
// Check for Prolog-style lists: [], [a,b,c], [H|T]
if text.starts_with('[') && text.ends_with(']') {
    return parse_list(text, symbols, operators);
}
```

## Files Modified

1. **src/parser/syntax.rs** (lines 545-548, 660-700, 961-963)
   - Added list parsing check in `parse_term()`
   - Implemented `parse_list()` function
   - Fixed `parse_list_header()` validation

2. **src/parser/operator.rs** (lines 10-25, 55-68, 140-146)
   - Added `Postfix` and `PostfixLeftAssoc` to `Fixity` enum
   - Added `is_postfix()` method
   - Added `postfix_operators()` query method

## Testing

**Manual Test**:
```bash
echo "list([])." > /tmp/test.in
./target/release/otter /tmp/test.in
# Result: Parses successfully
```

**Regression Test**:
```bash
./target/release/regression
# Result: Hangs/timeout (does not complete within 2+ minutes)
```

## Next Steps to Resolve

1. **Debug the infinite loop**:
   - Add logging to `parse_list()` to trace execution
   - Check if certain input patterns cause infinite recursion
   - Profile which test file causes the hang

2. **Fix the `&&str` issue** on line 665:
   ```rust
   // Before
   let inner = &text[1..text.len() - 1].trim();
   // After
   let inner = text[1..text.len() - 1].trim();
   ```

3. **Add termination guards**:
   - Ensure `parse_list()` always makes progress (removes brackets)
   - Add depth limiting or cycle detection if needed

4. **Test incrementally**:
   - Test just i4.in, eval.in, queens.in individually
   - Identify which specific input causes the hang

## Goal

Achieve 100% parse success rate (81/81) by fixing all parser-related issues. All remaining failures are parser issues, not inference engine issues, so Phase 1 can reach 100% without Phase 2 work.
