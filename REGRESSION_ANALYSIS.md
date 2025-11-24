# Regression Test Analysis - November 20, 2025

## Executive Summary

**Test Date**: 2025-11-20
**Total Examples**: 81
**Success Rate**: 2.5% (2/81)
**Parse Failures**: 34.6% (28/81)
**Runtime**: 231.27 seconds (~2.9 seconds/example)

## Test Configuration

- Resource limits enforced per example:
  - `max_given`: 100 clauses
  - `max_clauses`: 1000 clauses
- Examples located in: `_wb/otter-examples/`
- Categories: auto, fringe, ivy, kalman, Loop, misc, program, split, wos

## Results Breakdown

### Success Categories

1. **Full Success** (2 examples, 2.5%)
   - Examples that passed all comparisons with expected output
   - Very low success rate indicates significant differences from original Otter

2. **Parse Failures** (28 examples, 34.6%)
   - Parser cannot handle these input files
   - Indicates missing parser features or incompatibilities

3. **Behavioral Differences** (51 examples, 63.0%)
   - Parser succeeds, prover runs, but results differ from expected
   - Most show proof finding but with different statistics

### Parse Failure Analysis

**Total**: 28 examples (34.6% of all tests)

#### Error Categories:

1. **Formula Lists Not Clause Lists** (~4-5 examples)
   - Error: `list 'usable' is not a clause list (kind: Formula)`
   - Examples: lifsch.in, steam.in, w_sk.in, x2_quant.in
   - **Root Cause**: Parser expects clauses but encounters formulas (likely quantified formulas)
   - **Missing Feature**: First-order formula to CNF conversion

2. **Infix Operator Parsing** (~2-3 examples)
   - Error: `unsupported token 'x+y'`
   - Error: `unsupported token 'B | C'`
   - Examples: robbins.in, bring.in
   - **Root Cause**: Parser doesn't support infix notation for operators
   - **Missing Feature**: Infix operator parsing ('+', '|', etc.)

3. **Other Parse Errors** (~21-22 examples)
   - Various parsing issues not categorized above
   - Likely include: syntax incompatibilities, unsupported commands, etc.

### Behavioral Difference Analysis

**Total**: 51 examples

#### Pattern 1: Rust Port Finds Proofs, Original Doesn't (Common Pattern)

Many examples show this **surprising result**:
- **Rust port**: `proof_found: Some(true)`, very few clauses generated (0-hundreds)
- **Original Otter**: `proof_found: Some(false)` or data suggests no proof, many more clauses

**Examples**:
- cn19.in: Original 4909 generated vs Rust 0 generated, but Rust found proof!
- comm.in: Original 419 generated vs Rust 0 generated, but Rust found proof!
- ec_yq.in: Original 1839 generated vs Rust 0 generated, but Rust found proof!
- mv25.in: Original 3375 generated vs Rust 0 generated, but Rust found proof!

**Analysis**: This is **BACKWARDS from what we'd expect**. The Rust implementation shows:
- Dramatically fewer clauses generated
- But claims to find proofs

**Possible Explanations**:
1. ✅ **Most Likely**: Statistics counting error in Rust implementation
   - The "0 generated" is suspicious - likely a bug in stats tracking
   - The prover may be working but not counting generated clauses correctly

2. False proofs being reported (serious bug if true)
   - Less likely given our smoke tests pass

3. Different search strategy causing faster proof finding
   - Possible but unlikely given "0 generated" statistics

#### Pattern 2: Different Search Characteristics (Some Examples)

Examples showing different but non-zero statistics:
- pigeon.in: Original 410→187→147 vs Rust 131→176→100
- salt.in: Original 796→156→70 vs Rust 136→199→100
- wang1.in: Original 1494→208→39 vs Rust 979→1002→85

These show the prover is working but with very different search behavior.

#### Pattern 3: Hit Resource Limits

Several examples show `given=100`, indicating they hit the `max_given` limit:
- pigeon.in: given=100
- salt.in: given=100
- sam.in: given=100

These might succeed with higher limits.

## UPDATE: Statistics Bug Fixed

**Date**: 2025-11-20 (later in session)
**Bug Found**: The output code in `main.rs` was printing the wrong statistic field for "Given" clauses
- Was using `prover.stats().0` (clauses_generated)
- Should be `prover.stats().2` (given_count)

**Fix Applied**: Changed all occurrences in main.rs from `.0` to `.2`

**Result**: The "0 generated" statistics were CORRECT - many examples truly generate 0 clauses. The prover search loop runs, but finds no resolvents. This is likely because:
1. Examples use features we haven't implemented (UR-resolution, etc.)
2. Auto mode may not be setting up inference rules correctly for these examples
3. Examples may require specific Otter inference strategies

The regression test failure patterns are now understood to be REAL behavioral differences, not statistics bugs.

## Root Cause Categories

### 1. Parser Incompatibilities (34.6% of failures)

**Priority: HIGH**
**Impact**: Blocks 28 examples immediately

Missing parser features:
- Formula-to-CNF conversion (quantified formulas)
- Infix operator parsing ('+', '|', etc.)
- Other syntax variants

**Recommendation**:
- Review original Otter parser for formula handling
- Implement CNF conversion for quantified formulas
- Add infix operator support

### 2. Statistics Tracking Bug (Likely affects 51 examples)

**Priority: CRITICAL**
**Impact**: Makes regression testing unreliable

The "0 generated" pattern in many examples suggests the clause generation counter is broken.

**Evidence**:
- Multiple examples show `clauses_generated: Some(0)` in Rust
- But also show `clauses_kept: Some(5-10)` - can't keep what wasn't generated!
- Smoke tests show generation does happen (we see proof finding)

**Recommendation**:
- Audit statistics collection in prover.rs
- Verify `generated`, `kept`, `given` counters are incremented correctly
- Check if counters reset somewhere unexpectedly

### 3. Search Strategy Differences (Unknown Impact)

Even when statistics are tracked, the numbers differ significantly.

**Possible Causes**:
- Clause selection order differences
- Subsumption timing differences
- Inference rule application order
- Missing optimizations (FPA indexing, etc.)

**Recommendation**:
- After fixing statistics, re-run to get accurate comparison
- Identify specific examples with large differences
- Trace execution to find divergence points

### 4. Resource Limits Too Low (Affects some examples)

Some examples hit the 100 given clause limit.

**Recommendation**:
- For production use, increase or remove limits
- For testing, this is acceptable to prevent hangs

## Next Steps (Prioritized)

### Immediate (Critical Bugs)

1. **Fix Statistics Tracking Bug**
   - [ ] Audit prover.rs for counter increments
   - [ ] Verify `generated` counter updates on clause creation
   - [ ] Verify `kept` counter updates when adding to SOS
   - [ ] Verify `given` counter updates in search loop
   - [ ] Add debug logging to track counter changes
   - [ ] Re-run regression tests

2. **Validate Proof Correctness**
   - [ ] For examples claiming proofs with "0 generated", verify proof is valid
   - [ ] Check if empty clause is actually derived
   - [ ] Add proof validation to regression tests

### High Priority (Parser Expansion)

3. **Implement Formula-to-CNF Conversion**
   - [ ] Review original Otter formula handling
   - [ ] Implement Skolemization
   - [ ] Implement CNF conversion
   - [ ] Update parser to accept formula lists
   - [ ] Re-test lifsch.in, steam.in, w_sk.in, x2_quant.in

4. **Add Infix Operator Parsing**
   - [ ] Add infix '+', '|', '*', etc. to lexer
   - [ ] Update parser grammar for infix expressions
   - [ ] Re-test robbins.in, bring.in

### Medium Priority (Feature Completion)

5. **Implement UR-Resolution**
   - [ ] Add UR-resolution inference rule
   - [ ] May be needed by some examples

6. **Implement Splitting**
   - [ ] Add clause splitting capability
   - [ ] Required by examples in split/ directory

### Lower Priority (Optimization)

7. **Investigate Search Strategy Differences**
   - After statistics are fixed
   - Compare detailed trace logs for specific examples
   - Identify why clause counts differ

8. **Performance Optimization**
   - FPA indexing for large clause sets
   - Other optimizations from original Otter

## Success Metrics

**Current State**:
- Parse success: 65.4% (53/81)
- Full success: 2.5% (2/81)
- Partial success (runs but differs): 63.0% (51/81)

**M4 Target** (80% parity):
- Should achieve: 65/81 examples (80.2%) producing same results as original
- Requires fixing: statistics bug + parser features + search differences

**Realistic Near-Term Target** (after immediate fixes):
- Fix statistics bug: May improve accuracy of comparison
- Add parser features: Could bring parse success to 90%+ (73/81)
- This would enable testing on most examples

## Example-Specific Notes

### Successes (2 examples)
- (Not shown in first 20 failures - need full list)

### Parse Failures Requiring Formula Support
- lifsch.in
- steam.in
- w_sk.in
- x2_quant.in

### Parse Failures Requiring Infix Support
- robbins.in (x+y notation)
- bring.in (B | C notation)

### Examples Hitting Resource Limits
- pigeon.in (given=100)
- salt.in (given=100)
- sam.in (given=100)

### Examples with Suspicious "0 Generated" Statistics
- cn19.in
- comm.in
- ec_yq.in
- mv25.in
- ring_x2.in
- tba_gg.in
- ec_yql.in

## Conclusion

The regression test infrastructure is working well, and we now have concrete data on what needs to be fixed.

**Key Findings**:
1. **Statistics bug is critical** - "0 generated" pattern makes comparison unreliable
2. **Parser gaps are significant** - 35% of examples can't even be parsed
3. **The prover core works** - It's finding proofs (maybe too easily?)

**Immediate Action**:
Fix the statistics tracking bug first. This will give us accurate data to understand the real behavioral differences and guide further development.

**Timeline Estimate**:
- Statistics fix: 1-2 hours
- Formula parsing: 4-8 hours
- Infix operators: 2-4 hours
- Re-testing and analysis: 1-2 hours

After these fixes, we should see parse success rate jump to 90%+ and have reliable data on behavioral differences.
