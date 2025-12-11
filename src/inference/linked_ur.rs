//! Linked UR-Resolution implementation.
//!
//! Linked UR-resolution extends basic UR-resolution by chaining multiple
//! unit resolutions together using a tree-based search with backtracking.
//! This allows finding deeper proofs than standard UR-resolution.
//!
//! Based on the original Otter 3.3 linkur.c implementation.

use crate::data::{Clause, ClauseId, Literal, Term};
use crate::inference::{Substitution, Unifier};
use std::cell::RefCell;
use std::rc::Rc;

/// Configuration for linked UR-resolution.
#[derive(Clone, Debug)]
pub struct LinkedURConfig {
    /// Maximum depth of the search tree
    pub max_depth: usize,
    /// Maximum size of generated resolvent
    pub max_deduction_size: usize,
    /// Enable subsumable unit check optimization
    pub enable_subsumable_check: bool,
    /// Enable unit deletion optimization
    pub enable_unit_deletion: bool,
}

impl Default for LinkedURConfig {
    fn default() -> Self {
        Self {
            max_depth: 20,
            max_deduction_size: 100,
            enable_subsumable_check: false,
            enable_unit_deletion: false,
        }
    }
}

/// Node in the linked UR search tree.
///
/// Each node represents a literal (goal) that needs to be resolved.
/// The tree structure allows backtracking when no resolution is found.
pub struct LinkNode {
    // Tree navigation pointers
    parent: Option<Rc<RefCell<LinkNode>>>,
    first_child: Option<Rc<RefCell<LinkNode>>>,
    next_sibling: Option<Rc<RefCell<LinkNode>>>,
    prev_sibling: Option<Rc<RefCell<LinkNode>>>,

    // Node state
    first: bool,                        // First visit to this node?
    unit_deleted: bool,                 // Unit deletion applied?
    goal: Literal,                      // Literal to resolve
    goal_to_resolve: Option<Literal>,   // Instantiated form after substitution
    current_clause: Option<Clause>,     // Current clause being tried for resolution

    // Unification state
    subst: Substitution,

    // Distance metrics for optimization (will be used in Phase 6)
    near_poss_nuc: i32,
    farthest_sat: i32,
    target_dist: i32,
    back_up: i32,
}

impl LinkNode {
    /// Create a new link node for a goal literal.
    pub fn new(goal: Literal) -> Self {
        Self {
            parent: None,
            first_child: None,
            next_sibling: None,
            prev_sibling: None,
            first: true,
            unit_deleted: false,
            goal: goal.clone(),
            goal_to_resolve: Some(goal),
            current_clause: None,
            subst: Substitution::new(),
            near_poss_nuc: 0,
            farthest_sat: 0,
            target_dist: 0,
            back_up: 0,
        }
    }

    /// Get the depth of this node in the tree.
    pub fn depth(&self) -> usize {
        let mut depth = 0;
        let mut current = self.parent.clone();
        while let Some(parent_node) = current {
            depth += 1;
            current = parent_node.borrow().parent.clone();
        }
        depth
    }

    /// Check if this node is the root of the tree.
    pub fn is_root(&self) -> bool {
        self.parent.is_none()
    }

    /// Add a child node to this node.
    pub fn add_child(&mut self, child: Rc<RefCell<LinkNode>>) {
        if let Some(ref mut first_child) = self.first_child {
            // Add as sibling of existing children
            let mut last_child = first_child.clone();
            loop {
                let next_sibling = {
                    let borrowed = last_child.borrow();
                    borrowed.next_sibling.clone()
                };
                match next_sibling {
                    Some(next) => last_child = next,
                    None => break,
                }
            }
            last_child.borrow_mut().next_sibling = Some(child.clone());
            child.borrow_mut().prev_sibling = Some(last_child);
        } else {
            // First child
            self.first_child = Some(child);
        }
    }
}

/// Initialize the search tree from a given clause (nucleus).
///
/// Creates a root node and child nodes for each literal in the nucleus.
/// The root represents the entire nucleus, and each child represents
/// one literal that needs to be resolved away.
///
/// Based on C implementation at linkur.c:1372 (initialize_tree)
pub fn initialize_tree(given: &Clause) -> Option<Rc<RefCell<LinkNode>>> {
    if given.literals.is_empty() {
        return None;
    }

    // Create root node - represents the entire nucleus
    let root = Rc::new(RefCell::new(LinkNode::new(given.literals[0].clone())));

    // Create child nodes for each literal in the nucleus
    for literal in &given.literals {
        let child = Rc::new(RefCell::new(LinkNode::new(literal.clone())));
        child.borrow_mut().parent = Some(root.clone());
        root.borrow_mut().add_child(child);
    }

    Some(root)
}

/// Navigate forward in the tree to the next goal to resolve.
///
/// This implements the forward navigation logic from the C implementation.
/// It returns the next node to process, or None if we've reached a dead end.
///
/// Based on C implementation at linkur.c:1215 (forward)
pub fn forward(
    current: Rc<RefCell<LinkNode>>,
    target: Option<Rc<RefCell<LinkNode>>>,
) -> Option<Rc<RefCell<LinkNode>>> {
    let current_borrowed = current.borrow();

    // If this node has children, go to first child
    if let Some(ref first_child) = current_borrowed.first_child {
        return Some(first_child.clone());
    }

    // If this is the target, we're done
    if let Some(ref tgt) = target {
        if Rc::ptr_eq(&current, tgt) {
            return Some(current.clone());
        }
    }

    // Try to move to next sibling
    if let Some(ref next_sib) = current_borrowed.next_sibling {
        return Some(next_sib.clone());
    }

    // Move up to parent and continue
    let mut node = current.clone();
    loop {
        let parent = {
            let borrowed = node.borrow();
            borrowed.parent.clone()
        };

        match parent {
            None => return None, // Reached root with no siblings
            Some(p) => {
                // Check if parent is target
                if let Some(ref tgt) = target {
                    if Rc::ptr_eq(&p, tgt) {
                        return Some(p);
                    }
                }

                // Try parent's next sibling
                let next_sib = p.borrow().next_sibling.clone();
                if let Some(sib) = next_sib {
                    return Some(sib);
                }

                // Continue up the tree
                node = p;
            }
        }
    }
}

/// Navigate backward in the tree during backtracking.
///
/// When we can't find a resolvent for the current node, we need to backtrack
/// and try alternative paths. This function finds the next node to try by:
/// 1. Moving to the next sibling if available
/// 2. Otherwise moving up to the parent and trying its next sibling
/// 3. Continuing until we find an unexplored path or reach the root
///
/// Based on C implementation at linkur.c:557 (backward)
pub fn backward(
    current: Rc<RefCell<LinkNode>>,
    root: &Rc<RefCell<LinkNode>>,
) -> Option<Rc<RefCell<LinkNode>>> {
    // If we're at the root, search is exhausted
    if Rc::ptr_eq(&current, root) {
        return None;
    }

    let current_borrowed = current.borrow();

    // Try next sibling first
    if let Some(ref next_sib) = current_borrowed.next_sibling {
        return Some(next_sib.clone());
    }

    // No sibling available, move up to parent
    let parent = match &current_borrowed.parent {
        Some(p) => p.clone(),
        None => return None, // At root with no siblings
    };

    drop(current_borrowed); // Release borrow before recursion

    // Recursively backtrack from parent
    backward(parent, root)
}

/// Result of attempting to generate a resolvent.
#[derive(Clone, Debug)]
pub struct ResolventResult {
    /// The clause that unified with the goal
    pub clause: Clause,
    /// The substitution from unification
    pub substitution: Substitution,
    /// Which literal in the clause was unified (index)
    pub unified_literal_idx: usize,
}

/// Attempt to find a clause from the usable set that can resolve with the goal.
///
/// This function tries to unify the goal with complementary literals in each usable clause.
/// If successful, it returns the clause, substitution, and which literal unified.
///
/// Based on C implementation at linkur.c:1554 (generate_resolvent)
pub fn generate_resolvent(
    goal: &Literal,
    usable: &[Clause],
    current_subst: &Substitution,
) -> Option<ResolventResult> {
    // Try each usable clause
    for clause in usable {
        // Skip empty clauses
        if clause.literals.is_empty() {
            continue;
        }

        // Try to unify with each literal in the clause
        for (idx, literal) in clause.literals.iter().enumerate() {
            // Check if signs are complementary (one positive, one negative)
            if goal.sign == literal.sign {
                continue; // Same sign, can't resolve
            }

            // Try to unify the atoms
            let mut unifier = Unifier::new();

            // Apply current substitution to both goal and literal before unifying
            let goal_atom = current_subst.apply(&goal.atom);
            let literal_atom = current_subst.apply(&literal.atom);

            if unifier.unify(&goal_atom, &literal_atom).is_ok() {
                // Successful unification!
                // Compose the substitutions: current_subst followed by new substitution
                let new_subst = current_subst.compose(unifier.substitution());

                return Some(ResolventResult {
                    clause: clause.clone(),
                    substitution: new_subst,
                    unified_literal_idx: idx,
                });
            }
        }
    }

    None // No unifiable clause found
}

/// Result of linked UR-resolution.
#[derive(Clone, Debug)]
pub struct LinkedURResolvent {
    /// The resolvent clause
    pub clause: Clause,
    /// IDs of parent clauses (nucleus + satellites)
    pub parent_ids: Vec<Option<ClauseId>>,
    /// Substitution applied
    pub substitution: Substitution,
}

/// Build the final UR resolvent from a complete resolution path.
///
/// Walks back through the tree collecting all the clauses that were used,
/// and constructs the final unit clause with the accumulated substitution.
///
/// Build the final resolvent from a linked UR-resolution tree.
///
/// This function walks the resolution tree and collects any literals
/// that were not successfully resolved. These become the literals of
/// the final resolvent clause. If all literals were resolved, returns
/// an empty clause (indicating a proof).
///
/// Based on C implementation at linkur.c:1478 (build_ur_resolvent)
fn build_ur_resolvent(
    tree: &Rc<RefCell<LinkNode>>,
    nucleus: &Clause,
    subst: &Substitution,
) -> Clause {
    let mut unresolved_literals = Vec::new();

    // Walk through all child nodes (representing nucleus literals)
    let tree_borrowed = tree.borrow();
    let mut current_child = tree_borrowed.first_child.clone();

    while let Some(child_node) = current_child {
        let child = child_node.borrow();

        // If this child node was NOT successfully resolved (no current_clause),
        // its goal literal remains in the resolvent
        if child.current_clause.is_none() {
            // Apply the substitution to the goal literal
            let resolved_atom = subst.apply(&child.goal.atom);
            let resolved_lit = Literal::new(child.goal.sign, resolved_atom)
                .with_target(child.goal.target);
            unresolved_literals.push(resolved_lit);
        }

        // Move to next sibling
        current_child = child.next_sibling.clone();
    }

    // If no child nodes exist, this means we're working with the nucleus directly
    // Apply substitution to all nucleus literals
    if tree_borrowed.first_child.is_none() {
        for lit in &nucleus.literals {
            let resolved_atom = subst.apply(&lit.atom);
            let resolved_lit = Literal::new(lit.sign, resolved_atom)
                .with_target(lit.target);
            unresolved_literals.push(resolved_lit);
        }
    }

    let mut result = Clause::new(unresolved_literals);

    // Copy metadata from nucleus
    result.pick_weight = nucleus.pick_weight;
    result.heat_level = nucleus.heat_level;

    result
}

/// Perform linked UR-resolution on a given clause (nucleus).
///
/// This is the main entry point for linked UR-resolution. It takes a nucleus clause
/// (typically a unit clause) and attempts to resolve it with clauses from the usable set,
/// using a tree-based search with backtracking to find all possible resolution paths.
///
/// Based on C implementation at linkur.c:702 (linked_ur_res)
pub fn linked_ur_resolve(
    nucleus: &Clause,
    nucleus_id: Option<ClauseId>,
    usable: &[Clause],
    config: &LinkedURConfig,
) -> Vec<LinkedURResolvent> {
    let mut results = Vec::new();

    // Skip if nucleus has no literals (shouldn't happen)
    if nucleus.literals.is_empty() {
        return results;
    }

    // Initialize the search tree
    let root = match initialize_tree(nucleus) {
        Some(r) => r,
        None => return results,
    };

    // Start search from first child
    let mut current = match forward(root.clone(), None) {
        Some(node) => node,
        None => return results,
    };

    let mut depth = 0;
    let max_iterations = 1000; // Prevent infinite loops
    let mut iteration_count = 0;

    loop {
        iteration_count += 1;
        if iteration_count > max_iterations {
            break; // Safety limit
        }

        // Check depth limit
        if depth > config.max_depth {
            // Backtrack
            match backward(current.clone(), &root) {
                Some(next) => {
                    current = next;
                    depth = current.borrow().depth();
                    continue;
                }
                None => break, // Search exhausted
            }
        }

        // Get current goal to resolve
        let goal = current.borrow().goal.clone();
        let current_subst = current.borrow().subst.clone();

        // Try to find a clause that resolves with this goal
        match generate_resolvent(&goal, usable, &current_subst) {
            Some(resolvent) => {
                // Found a unifiable clause!

                // Update current node with the clause and substitution
                {
                    let mut node_mut = current.borrow_mut();
                    node_mut.current_clause = Some(resolvent.clause.clone());
                    node_mut.subst = resolvent.substitution.clone();
                    node_mut.first = false;
                }

                // Create children for remaining literals in the resolvent clause
                // (Skip the literal that unified)
                let remaining_literals: Vec<_> = resolvent.clause.literals
                    .iter()
                    .enumerate()
                    .filter(|(idx, _)| *idx != resolvent.unified_literal_idx)
                    .map(|(_, lit)| lit.clone())
                    .collect();

                if !remaining_literals.is_empty() {
                    // Create child nodes for each remaining literal
                    for lit in &remaining_literals {
                        let child = Rc::new(RefCell::new(LinkNode::new(lit.clone())));
                        child.borrow_mut().parent = Some(current.clone());
                        child.borrow_mut().subst = resolvent.substitution.clone();
                        current.borrow_mut().add_child(child);
                    }
                }

                // Check if we've fully resolved the tree (all literals resolved)
                let is_fully_resolved = remaining_literals.is_empty();

                if is_fully_resolved {
                    // Success! Build and record the resolvent
                    let final_clause = build_ur_resolvent(&root, nucleus, &resolvent.substitution);

                    let mut parent_ids = vec![nucleus_id];
                    // In full implementation, collect all satellite clause IDs

                    results.push(LinkedURResolvent {
                        clause: final_clause,
                        parent_ids,
                        substitution: resolvent.substitution.clone(),
                    });

                    // Backtrack to find more solutions
                    match backward(current.clone(), &root) {
                        Some(next) => {
                            current = next;
                            depth = current.borrow().depth();
                        }
                        None => break, // No more paths to explore
                    }
                } else {
                    // Move forward to resolve remaining literals
                    match forward(current.clone(), None) {
                        Some(next) => {
                            current = next;
                            depth = current.borrow().depth();
                        }
                        None => break,
                    }
                }
            }
            None => {
                // No resolvent found, backtrack
                match backward(current, &root) {
                    Some(next) => {
                        current = next;
                        depth = current.borrow().depth();
                    }
                    None => break, // Search exhausted
                }
            }
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{SymbolTable, SymbolKind};

    fn make_test_literal(name: &str, sign: bool, symbols: &mut SymbolTable) -> Literal {
        let pred_id = symbols.intern(name, 0, SymbolKind::Predicate);
        Literal::new(sign, Term::application(pred_id, vec![]))
    }

    #[test]
    fn test_link_node_creation() {
        let mut symbols = SymbolTable::new();
        let lit = make_test_literal("P", true, &mut symbols);
        let node = LinkNode::new(lit.clone());

        assert_eq!(node.goal, lit);
        assert!(node.is_root());
        assert_eq!(node.depth(), 0);
        assert!(node.first);
    }

    #[test]
    fn test_initialize_tree() {
        let mut symbols = SymbolTable::new();
        let p = make_test_literal("P", true, &mut symbols);
        let q = make_test_literal("Q", false, &mut symbols);
        let r = make_test_literal("R", true, &mut symbols);

        let clause = Clause::new(vec![p, q, r]);

        let root = initialize_tree(&clause).expect("tree creation failed");

        // Root should have 3 children (one per literal)
        let root_borrowed = root.borrow();
        assert!(root_borrowed.first_child.is_some());

        // Count children
        let mut count = 0;
        let mut child = root_borrowed.first_child.clone();
        while let Some(c) = child {
            count += 1;
            let c_borrowed = c.borrow();
            assert!(Rc::ptr_eq(&c_borrowed.parent.as_ref().unwrap(), &root));
            child = c_borrowed.next_sibling.clone();
        }
        assert_eq!(count, 3);
    }

    #[test]
    fn test_forward_navigation() {
        let mut symbols = SymbolTable::new();
        let p = make_test_literal("P", true, &mut symbols);
        let q = make_test_literal("Q", false, &mut symbols);

        let clause = Clause::new(vec![p, q]);

        let root = initialize_tree(&clause).expect("tree creation failed");

        // Forward from root should go to first child
        let next = forward(root.clone(), None).expect("forward failed");
        let next_borrowed = next.borrow();
        assert!(Rc::ptr_eq(&next_borrowed.parent.as_ref().unwrap(), &root));

        // Forward from first child should go to next sibling
        drop(next_borrowed);
        let next2 = forward(next.clone(), None);
        assert!(next2.is_some());
    }

    #[test]
    fn test_node_depth() {
        let mut symbols = SymbolTable::new();
        let p = make_test_literal("P", true, &mut symbols);

        let clause = Clause::new(vec![p]);

        let root = initialize_tree(&clause).expect("tree creation failed");
        assert_eq!(root.borrow().depth(), 0);

        let child = root.borrow().first_child.clone().unwrap();
        assert_eq!(child.borrow().depth(), 1);
    }

    #[test]
    fn test_generate_resolvent_simple() {
        use crate::data::{Term, VariableId};

        let mut symbols = SymbolTable::new();

        // Goal: P(a) (positive)
        let a = symbols.intern("a", 0, SymbolKind::Function);
        let goal = Literal::new(true, Term::application(
            symbols.intern("P", 1, SymbolKind::Predicate),
            vec![Term::application(a, vec![])],
        ));

        // Usable clause: -P(a) (negative)
        let clause = Clause::new(vec![Literal::new(false, Term::application(
            symbols.intern("P", 1, SymbolKind::Predicate),
            vec![Term::application(a, vec![])],
        ))]);

        let subst = Substitution::new();
        let result = generate_resolvent(&goal, &[clause], &subst);

        assert!(result.is_some());
        let res = result.unwrap();
        assert_eq!(res.unified_literal_idx, 0);
    }

    #[test]
    fn test_generate_resolvent_with_variables() {
        use crate::data::{Term, VariableId};

        let mut symbols = SymbolTable::new();
        let p_sym = symbols.intern("P", 1, SymbolKind::Predicate);

        // Goal: P(x) (positive, with variable)
        let goal = Literal::new(true, Term::application(
            p_sym,
            vec![Term::variable(VariableId::new(0))],
        ));

        // Usable clause: -P(a) (negative, with constant)
        let a = symbols.intern("a", 0, SymbolKind::Function);
        let clause = Clause::new(vec![Literal::new(false, Term::application(
            p_sym,
            vec![Term::application(a, vec![])],
        ))]);

        let subst = Substitution::new();
        let result = generate_resolvent(&goal, &[clause], &subst);

        assert!(result.is_some());
        let res = result.unwrap();
        // Should have unified x with a
        assert!(res.substitution.lookup(VariableId::new(0)).is_some());
    }

    #[test]
    fn test_substitution_apply() {
        use crate::data::{Term, VariableId};

        let mut subst = Substitution::new();
        let mut symbols = SymbolTable::new();
        let a = symbols.intern("a", 0, SymbolKind::Function);

        // x -> a
        let x = VariableId::new(0);
        subst.bind(x, Term::application(a, vec![]));

        // Apply to variable x
        let term = Term::variable(x);
        let result = subst.apply(&term);

        match result {
            Term::Application { symbol, .. } => assert_eq!(symbol, a),
            _ => panic!("Expected application"),
        }
    }

    #[test]
    fn test_substitution_compose() {
        use crate::data::{Term, VariableId};

        let mut s1 = Substitution::new();
        let mut s2 = Substitution::new();
        let mut symbols = SymbolTable::new();

        let a = symbols.intern("a", 0, SymbolKind::Function);
        let _b = symbols.intern("b", 0, SymbolKind::Function);

        let x = VariableId::new(0);
        let y = VariableId::new(1);

        // s1: x -> y
        s1.bind(x, Term::variable(y));

        // s2: y -> a
        s2.bind(y, Term::application(a, vec![]));

        // Composition should give: x -> a, y -> a
        let composed = s1.compose(&s2);

        // x should map to a (through y)
        let x_val = composed.lookup(x).unwrap();
        match x_val {
            Term::Application { symbol, .. } => assert_eq!(*symbol, a),
            _ => panic!("Expected x -> a"),
        }
    }

    #[test]
    fn test_backward_to_sibling() {
        let mut symbols = SymbolTable::new();
        let p = make_test_literal("P", true, &mut symbols);
        let q = make_test_literal("Q", false, &mut symbols);

        // Create a tree with 2 children
        let clause = Clause::new(vec![p, q]);
        let root = initialize_tree(&clause).expect("tree creation failed");

        // Navigate to first child
        let first_child = root.borrow().first_child.clone().unwrap();

        // Backward from first child should go to next sibling
        let next = backward(first_child, &root);
        assert!(next.is_some());

        let next_node = next.unwrap();
        // Should be the second child
        assert!(Rc::ptr_eq(&next_node.borrow().parent.as_ref().unwrap(), &root));
    }

    #[test]
    fn test_backward_to_parent() {
        let mut symbols = SymbolTable::new();
        let p = make_test_literal("P", true, &mut symbols);

        // Create a tree with 1 child (no siblings)
        let clause = Clause::new(vec![p]);
        let root = initialize_tree(&clause).expect("tree creation failed");

        // Navigate to the only child
        let only_child = root.borrow().first_child.clone().unwrap();

        // Backward from only child with no siblings should return None (exhausted)
        let result = backward(only_child, &root);
        assert!(result.is_none());
    }

    #[test]
    fn test_backward_from_root() {
        let mut symbols = SymbolTable::new();
        let p = make_test_literal("P", true, &mut symbols);

        let clause = Clause::new(vec![p]);
        let root = initialize_tree(&clause).expect("tree creation failed");

        // Backward from root should return None (search exhausted)
        let result = backward(root.clone(), &root);
        assert!(result.is_none());
    }

    #[test]
    fn test_linked_ur_resolve_simple() {
        use crate::data::Term;

        let mut symbols = SymbolTable::new();
        let p_sym = symbols.intern("P", 1, SymbolKind::Predicate);
        let a = symbols.intern("a", 0, SymbolKind::Function);

        // Nucleus: P(a) (positive unit clause)
        let nucleus = Clause::new(vec![Literal::new(
            true,
            Term::application(p_sym, vec![Term::application(a, vec![])]),
        )]);

        // Usable: -P(a) (negative unit clause)
        let usable = vec![Clause::new(vec![Literal::new(
            false,
            Term::application(p_sym, vec![Term::application(a, vec![])]),
        )])];

        let config = LinkedURConfig::default();
        let results = linked_ur_resolve(&nucleus, None, &usable, &config);

        // Should find a resolvent (empty clause = proof)
        assert!(!results.is_empty());
        assert_eq!(results[0].clause.literals.len(), 0); // Empty clause
    }
}
