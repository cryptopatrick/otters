# Mayor.md - Critical Analysis of Otter Proof Rate

**Analysis Date**: December 10, 2025
**Initial Status**: 0/81 proofs (0%)
**Current Status**: 7/81 proofs (8.6%) ← After Phase 1 fix
**Target**: 73/81 proofs (90%)

---

## Phase 1 Results (Completed)

**What was fixed:**
1. Added problem type detection (equality, max_lits, horn)
2. Implemented strategy selection based on problem type
3. Enabled paramodulation for equational problems
4. Fixed clause movement (positive to SOS for equality problems)

**Proofs now found (7/81 = 8.6%):**
- fringe/rob_ocd.in (equality)
- kalman/ex_1.in, ex_2.in, ex_3.in, ex_4.in (hyperresolution)
- program/mission.in (hyperresolution)
- split/group2.in (hyperresolution)

**Remaining blockers:**
- Search explosion in equational problems (missing demodulation)
- Missing LRPO term ordering
- Missing directional paramodulation
- Some examples need specific flags

---

## Executive Summary (Original Analysis)

The Otter Rust port was fundamentally broken because **auto mode did not enable the correct inference rules for the problem type**. The prover:

1. **Parses correctly** (100% parse rate)
2. **Runs but generates 0 new clauses** because wrong inference rules are enabled
3. **Saturates immediately** after processing 1 given clause

**Root Cause**: The auto mode strategy detection (`automatic_1_settings()` in C Otter) is completely missing from the Rust port.

---

## The Problem in Detail

### Test Case: comm.in (Group Theory Commutator)

```
set(auto).
list(usable).
x = x.                           % reflexivity
f(e,x) = x.                      % identity
f(g(x),x) = e.                   % inverse
f(f(x,y),z) = f(x,f(y,z)).       % associativity
h(x,y) = f(x,f(y,f(g(x),g(y)))). % commutator definition
f(x,f(x,x)) = e.                 % x³ = e
h(h(a,b),b) != e.                % negated goal
end_of_list.
```

**Current Rust behavior**:
```
Parsed successfully: Lists: 1, Commands: 1
Given: 1, Generated: 0, Kept: 7
SEARCH SATURATED (no proof found)
```

**Expected C Otter behavior**:
- Detects: `equality=1, max_lits=1` → pure equational problem
- Enables: `KNUTH_BENDIX` (which enables para_from, para_into, demod, back_demod)
- Finds proof in 0.01 seconds

### Why Generated: 0?

The Rust auto mode enables:
- `use_hyper_res = true`
- `use_ur_res = true`
- `use_binary_res = true`

But for **pure equality problems**, these are useless:
- Binary resolution needs complementary literals (P vs -P) - equality has none
- Hyperresolution needs negative literals as nuclei - all literals are positive equalities
- UR-resolution same issue

**Paramodulation is required** for equality reasoning, but it's NOT enabled.

---

## C Otter Auto Mode Logic (misc.c:2154-2268)

The C Otter `automatic_1_settings()` function:

1. **Scans clauses** to detect:
   - `propositional`: no variables?
   - `horn`: at most 1 positive literal per clause?
   - `equality`: any clause contains "="?
   - `max_lits`: maximum literals in any clause?
   - `symmetry`: has symmetry axiom (x=y → y=x)?

2. **Selects strategy** based on characteristics:

| Condition | Strategy | Key Flags |
|-----------|----------|-----------|
| propositional | Propositional | HYPER_RES, PROPOSITIONAL |
| equality && max_lits==1 | **KNUTH_BENDIX** | PARA_FROM, PARA_INTO, DEMOD, BACK_DEMOD |
| !horn && !equality | Non-Horn | HYPER_RES, FACTOR, UNIT_DELETION |
| horn && !equality | Horn | HYPER_RES |
| !horn && equality | Non-Horn+Eq | KNUTH_BENDIX, HYPER_RES, FACTOR, UNIT_DELETION |
| horn && equality | Horn+Eq | KNUTH_BENDIX, HYPER_RES |

### KNUTH_BENDIX (ANL_EQ) Flag Cascade (options.c:751-764)

When KNUTH_BENDIX is set:
```c
auto_change_flag(fp, PARA_FROM, 1);
auto_change_flag(fp, PARA_INTO, 1);
auto_change_flag(fp, PARA_FROM_LEFT, 1);
auto_change_flag(fp, PARA_FROM_RIGHT, 0);     // directional!
auto_change_flag(fp, PARA_INTO_LEFT, 1);
auto_change_flag(fp, PARA_INTO_RIGHT, 0);     // directional!
auto_change_flag(fp, PARA_FROM_VARS, 1);
auto_change_flag(fp, EQ_UNITS_BOTH_WAYS, 1);
auto_change_flag(fp, DYNAMIC_DEMOD_ALL, 1);
auto_change_flag(fp, BACK_DEMOD, 1);
auto_change_flag(fp, PROCESS_INPUT, 1);
auto_change_flag(fp, LRPO, 1);
```

---

## Missing Components in Rust Port

### Critical (Required for any proofs)

1. **Problem Type Detection**
   - Function to detect: propositional, horn, equality, max_lits, symmetry
   - Location: Should be in `builder.rs` before building prover

2. **Strategy Selection**
   - Implement the 6-way branch from `automatic_1_settings()`
   - Each branch enables different inference rules

3. **KNUTH_BENDIX Flag Cascade**
   - When equational problem detected, enable:
     - `use_para_from = true`
     - `use_para_into = true`
     - `use_demod = true`
     - Plus directional flags (already partially implemented but never used)

### High Priority (For 50%+ proof rate)

4. **Clause Movement in Auto Mode**
   - C Otter moves positive clauses to SOS, negative to usable
   - Current Rust moves negative to SOS (opposite!)
   - This affects inference direction

5. **Demodulation Integration**
   - `DYNAMIC_DEMOD_ALL`: Auto-extract demodulators from new equalities
   - `BACK_DEMOD`: Rewrite existing clauses when new demodulator found

6. **LRPO (Lexicographic Path Ordering)**
   - Required for orienting equalities (l=r vs r=l)
   - Prevents infinite loops in paramodulation

### Medium Priority (For 70%+ proof rate)

7. **EQ_UNITS_BOTH_WAYS**
   - When adding unit equality, add both orientations
   - Critical for completeness

8. **Process Input**
   - Pre-process input clauses (demodulate, extract demodulators)

---

## Implementation Plan

### Phase 1: Emergency Fix (1-2 hours)

**Goal**: Get some proofs working

1. **Add problem type detection** to `builder.rs`:
```rust
fn detect_problem_type(clauses: &[Clause], eq_symbol: SymbolId) -> ProblemType {
    let has_equality = clauses.iter().any(|c| clause_has_equality(c, eq_symbol));
    let max_lits = clauses.iter().map(|c| c.literals.len()).max().unwrap_or(0);
    let is_horn = clauses.iter().all(|c| is_horn_clause(c));

    ProblemType { has_equality, max_lits, is_horn }
}
```

2. **Enable paramodulation for equational problems**:
```rust
if problem.has_equality && problem.max_lits == 1 {
    // Pure equational - KNUTH_BENDIX
    self.config.use_para_from = true;
    self.config.use_para_into = true;
    self.config.use_demod = true;
}
```

3. **Fix clause movement** (positive to SOS for equational):
```rust
// For equational problems, positive clauses go to SOS
if problem.has_equality {
    for clause in usable_clauses {
        if is_positive_clause(&clause) {
            sos_clauses.push(clause);
        } else {
            remaining_usable.push(clause);
        }
    }
}
```

### Phase 2: Full Auto Mode (1-2 days)

1. Implement all 6 strategy branches
2. Add KNUTH_BENDIX flag cascade
3. Add LRPO for term ordering
4. Add EQ_UNITS_BOTH_WAYS

### Phase 3: Polish (1 week)

1. Directional paramodulation (already partially done)
2. Back demodulation
3. Hints mechanism
4. Hot list

---

## Verification Steps

After Phase 1, test:
```bash
./target/release/otter _wb/otter-examples/auto/comm.in
```

Expected: Should find proof (currently times out)

After Phase 2, test:
```bash
./target/release/regression
```

Expected: ~50% proof rate

---

## Key Files to Modify

| File | Changes |
|------|---------|
| `src/inference/builder.rs` | Add problem detection, strategy selection |
| `src/inference/prover.rs` | Already has para_into/para_from config, just needs enabling |
| `src/inference/mod.rs` | Export new types if needed |

---

## Conclusion

The 0% proof rate is not a subtle bug - it's a fundamental architectural omission. The Rust port has inference rules implemented but never enabled for the appropriate problem types. The fix is straightforward once the problem type detection is added.

**Estimated effort to reach 50% proof rate**: 1-2 days
**Estimated effort to reach 90% proof rate**: 1-2 weeks
