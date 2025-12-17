# Development Process for Otters (Otter 3.3 Rust Port)

This document describes the development process, tools, and techniques used to work on the Otters project. It's designed to help continue development when the AI assistant is unavailable.

---

## Project Overview

**Goal**: Port the Otter 3.3 theorem prover from C to Rust, achieving 90% (73/81) proof success rate on the example suite.

**Current Status**: ~15-18/81 proofs (18-22%)

**Key Files**:
- `src/inference/linked_ur.rs` - Linked UR-Resolution (currently being fixed)
- `src/inference/prover.rs` - Main prover loop
- `src/inference/builder.rs` - Builds prover from parsed Otter input
- `_wb/otter-source/` - Original C source code for reference
- `_wb/otter-examples/` - Test suite with 81 example problems

---

## Build Commands

### Basic Build
```bash
cargo build --release    # Optimized build
cargo build             # Debug build (slower, better errors)
```

### Run Single Example
```bash
./target/release/otter _wb/otter-examples/auto/cn19.in 2>&1 | tail -20
```

### Run Regression Suite
```bash
./target/release/regression 2>&1 | grep -E "Total|Proofs found|Success"
```

### Quick Proof Count Script
```bash
#!/bin/bash
count=0
for file in _wb/otter-examples/*/*.in; do
    if timeout 5 ./target/release/otter "$file" 2>&1 | grep -q "PROOF FOUND"; then
        count=$((count + 1))
        echo "PROOF: $file"
    fi
done
echo "Proofs found: $count/81"
```

---

## Debugging Techniques

### 1. Add eprintln! Statements
Add tracing to understand program flow:
```rust
eprintln!("DEBUG: entering function X with arg={:?}", arg);
```

### 2. Isolate Single Test Case
Find a small example that demonstrates the bug:
```bash
# Find smallest failing test
for file in _wb/otter-examples/auto/*.in; do
    if ! timeout 2 ./target/release/otter "$file" 2>&1 | grep -q "PROOF FOUND"; then
        wc -l "$file"  # Show line count
    fi
done
```

### 3. Compare with C Otter
Original Otter is often available to compare:
```bash
# If you have C Otter compiled
./_wb/otter3.3/bin/otter < _wb/otter-examples/auto/cn19.in
```

### 4. Check for Stack Overflow
If you get stack overflow, likely infinite recursion:
- Add iteration counters with safety limits
- Check recursive function termination conditions

---

## Key Algorithmic Concepts

### Linked UR-Resolution

**Purpose**: Chain multiple unit resolutions together using a tree-based search with backtracking.

**C Implementation Reference**: `_wb/otter-source/linkur.c`

**Key Functions**:
- `initialize_tree()` - Create search tree from nucleus clause
- `forward()` - Navigate tree to find next goal
- `backward()` - Backtrack when resolution fails
- `build_ur_resolvent()` - Construct final clause from completed tree
- `generate_resolvent()` - Try to resolve a goal with usable clauses

**Critical Bug Points** (identified in this session):
1. **Target Pointer**: The C implementation uses a `target` pointer to designate which literal becomes the final resolvent. `target == NULL` means empty clause (proof).
2. **Substitution Composition**: Substitutions must accumulate/compose, not replace each other.
3. **Tree Structure**: Should be depth-first, not breadth-first.
4. **Goal Instantiation**: Goals must be instantiated via accumulated substitution before resolution.

### Given-Clause Loop
Main saturation-based proof search:
1. Pick a clause from SOS (set of support)
2. Generate all inferences with usable clauses
3. Add new clauses to SOS
4. Repeat until empty clause found or limits reached

---

## Current Work: Linked UR Fix

### Plan File Location
`/Users/cp/.claude/plans/mutable-inventing-frog.md`

### Current Step
**Step 1-2 Complete**: Added target tracking and updated `build_ur_resolvent()`

### Remaining Steps
3. Verify substitution composition works correctly
4. Test with simple cases
5. Add alternative clause exploration (backtracking)
6. Add tracing for debugging
7. Run full regression

### Key Code Changes Made

1. **TreeInit struct** (line ~127): Returns target pointer from `initialize_tree()`
```rust
pub struct TreeInit {
    pub root: Rc<RefCell<LinkNode>>,
    pub target: Option<Rc<RefCell<LinkNode>>>,
    pub children: Vec<Rc<RefCell<LinkNode>>>,
}
```

2. **build_ur_resolvent()** (line ~354): Now uses target-based logic
```rust
fn build_ur_resolvent(
    target: Option<&Rc<RefCell<LinkNode>>>,
    subst: &Substitution,
    nucleus: &Clause,
) -> Clause {
    match target {
        Some(target_node) => {
            // Unit clause: apply substitution to target's goal
            ...
        }
        None => {
            // Empty clause - proof found!
            Clause::new(vec![])
        }
    }
}
```

3. **linked_ur_resolve()** (line ~415): Updated to use TreeInit and skip target during traversal

---

## Testing Strategy

### Unit Tests
```bash
cargo test linked_ur   # Run linked_ur module tests
cargo test            # Run all tests
```

### Integration Tests
```bash
# Test specific example
./target/release/otter _wb/otter-examples/auto/reflexivity.in 2>&1

# Should see "PROOF FOUND" for working examples
```

### Regression Tests
```bash
./target/release/regression 2>&1 | tee /tmp/regression.txt

# Count successes
grep -c "PROOF" /tmp/regression.txt
```

---

## Common Rust Issues

### Borrow Checker with RefCell
When using `Rc<RefCell<T>>`:
```rust
// BAD - holds borrow too long
let borrowed = node.borrow();
do_something(borrowed.field);
node.borrow_mut().other_field = x;  // ERROR: still borrowed!

// GOOD - scope the borrow
{
    let borrowed = node.borrow();
    do_something(borrowed.field);
}  // borrow ends here
node.borrow_mut().other_field = x;  // OK
```

### Rust 2024 Match Ergonomics
```rust
// Old style (may error in 2024)
if let Some(ref t) = target { ... }

// New style
if let Some(t) = target { ... }
```

---

## Useful Shell Commands

### Find files containing pattern
```bash
grep -r "target" src/inference/linked_ur.rs
```

### Count lines in file
```bash
wc -l src/inference/linked_ur.rs
```

### Show specific lines
```bash
sed -n '330,380p' src/inference/linked_ur.rs
```

### Timeout a command
```bash
timeout 5 ./target/release/otter example.in
```

---

## Reference Materials

- **Original C Source**: `_wb/otter-source/linkur.c` (especially lines 1145-1175 for `build_ur_resolvent`)
- **PRD**: `_dev/PRD.md` - Product requirements document
- **Plan**: `/Users/cp/.claude/plans/mutable-inventing-frog.md` - Detailed implementation plan

---

## Next Steps (Priority Order)

1. **Test the current build**: Run `./target/release/regression` to see if proof count changed
2. **Add debug tracing** to `linked_ur_resolve()` to see what's happening
3. **Verify simple case works**: Test with `reflexivity.in` (simple proof)
4. **Fix any issues found** in substitution handling
5. **Implement alternative clause exploration** if needed

Good luck!
