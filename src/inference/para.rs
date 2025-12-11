//! Paramodulation (equational reasoning).
//!
//! Paramodulation is the primary inference rule for equality reasoning.
//! It allows replacing equals for equals within terms.
//!
//! Given:
//! - From clause: contains an equality l=r (or r=l)
//! - Into clause: contains a term that unifies with l
//! 
//! Paramodulation produces a new clause by replacing the unified term with r.
//!
//! Example:
//!   From: f(a) = b
//!   Into: P(f(a))
//!   Result: P(b)

use crate::data::{Clause, ClauseId, Literal, Term};
use crate::inference::{Substitution, Unifier};

/// Result of a paramodulation step.
#[derive(Clone, Debug)]
pub struct Paramodulant {
    /// The resulting clause
    pub clause: Clause,
    /// The "from" clause ID (containing the equality)
    pub from_id: Option<ClauseId>,
    /// The "into" clause ID (being paramodulated into)
    pub into_id: Option<ClauseId>,
    /// The substitution used
    pub substitution: Substitution,
}

/// Check if a literal is an equality.
fn is_equality(lit: &Literal, eq_symbol: crate::data::SymbolId) -> bool {
    if let Term::Application { symbol, args } = &lit.atom {
        *symbol == eq_symbol && args.len() == 2
    } else {
        false
    }
}

/// Extract left and right sides of an equality literal.
fn get_equality_sides(lit: &Literal) -> Option<(&Term, &Term)> {
    if let Term::Application { args, .. } = &lit.atom {
        if args.len() == 2 {
            return Some((&args[0], &args[1]));
        }
    }
    None
}

/// Perform paramodulation from a clause containing equalities into another clause.
///
/// This implements the para_into inference rule: finding positions in the "into"
/// clause where we can replace a term with its equal.
///
/// Directional flags control which orientations of equality are used:
/// - `para_from_left`: Use left side of equality as pattern (find l in l=r, replace with r)
/// - `para_from_right`: Use right side of equality as pattern (find r in l=r, replace with l)
/// - `para_into_left`: Allow replacing in left side of target equality
/// - `para_into_right`: Allow replacing in right side of target equality
pub fn paramodulate_into(
    from_clause: &Clause,
    from_id: Option<ClauseId>,
    into_clause: &Clause,
    into_id: Option<ClauseId>,
    eq_symbol: crate::data::SymbolId,
    para_from_left: bool,
    para_from_right: bool,
    para_into_left: bool,
    para_into_right: bool,
) -> Vec<Paramodulant> {
    let mut results = Vec::new();

    // Find positive equality literals in the from clause
    for from_lit in &from_clause.literals {
        if !from_lit.sign || !is_equality(from_lit, eq_symbol) {
            continue;
        }

        let Some((left, right)) = get_equality_sides(from_lit) else {
            continue;
        };

        // Try paramodulating into each literal of the into clause
        for (into_lit_idx, into_lit) in into_clause.literals.iter().enumerate() {
            // Check if we're paramodulating into an equality and apply directional restrictions
            let is_into_equality = is_equality(into_lit, eq_symbol);

            // Try left-to-right: find `left` in target, replace with `right`
            if para_from_left {
                let replacements = find_and_replace_subterms(
                    &into_lit.atom,
                    left,
                    right,
                    eq_symbol,
                    is_into_equality,
                    para_into_left,
                    para_into_right,
                );

                for (new_atom, subst) in replacements {
                    results.push(build_paramodulant(
                        from_clause,
                        from_id,
                        into_clause,
                        into_id,
                        from_lit,
                        into_lit_idx,
                        new_atom,
                        subst,
                    ));
                }
            }

            // Try right-to-left: find `right` in target, replace with `left`
            if para_from_right {
                let replacements = find_and_replace_subterms(
                    &into_lit.atom,
                    right,
                    left,
                    eq_symbol,
                    is_into_equality,
                    para_into_left,
                    para_into_right,
                );

                for (new_atom, subst) in replacements {
                    results.push(build_paramodulant(
                        from_clause,
                        from_id,
                        into_clause,
                        into_id,
                        from_lit,
                        into_lit_idx,
                        new_atom,
                        subst,
                    ));
                }
            }
        }
    }

    results
}

/// Build a paramodulant clause from the components.
fn build_paramodulant(
    from_clause: &Clause,
    from_id: Option<ClauseId>,
    into_clause: &Clause,
    into_id: Option<ClauseId>,
    from_lit: &Literal,
    into_lit_idx: usize,
    new_atom: Term,
    subst: Substitution,
) -> Paramodulant {
    let mut new_literals = Vec::new();

    // Add all literals from from_clause except the equality used
    for lit in &from_clause.literals {
        if !std::ptr::eq(lit, from_lit) {
            new_literals.push(subst.apply_to_literal(lit));
        }
    }

    // Add all literals from into_clause, with the modified one replaced
    for (idx, lit) in into_clause.literals.iter().enumerate() {
        if idx == into_lit_idx {
            new_literals.push(Literal::new(lit.sign, new_atom.clone()));
        } else {
            new_literals.push(subst.apply_to_literal(lit));
        }
    }

    let mut result_clause = Clause::new(new_literals);
    if let Some(id) = from_id {
        result_clause.add_parent(id);
    }
    if let Some(id) = into_id {
        result_clause.add_parent(id);
    }

    Paramodulant {
        clause: result_clause,
        from_id,
        into_id,
        substitution: subst,
    }
}

/// Find all positions in a term where we can replace it with an equal term.
///
/// For directional paramodulation into equalities:
/// - If target is an equality and para_into_left=false, don't replace in left side
/// - If target is an equality and para_into_right=false, don't replace in right side
fn find_and_replace_subterms(
    target: &Term,
    pattern: &Term,
    replacement: &Term,
    eq_symbol: crate::data::SymbolId,
    is_target_equality: bool,
    para_into_left: bool,
    para_into_right: bool,
) -> Vec<(Term, Substitution)> {
    let mut results = Vec::new();

    // Try to unify the entire term with the pattern
    let mut unifier = Unifier::new();
    if unifier.unify(target, pattern).is_ok() {
        let subst = unifier.into_substitution();
        let new_term = subst.apply(replacement);
        results.push((new_term, subst));
    }

    // Recursively try to replace subterms
    if let Term::Application { symbol, args } = target {
        for (i, arg) in args.iter().enumerate() {
            // If target is an equality, check directional restrictions
            if is_target_equality && *symbol == eq_symbol && args.len() == 2 {
                // i=0 is left side, i=1 is right side
                if i == 0 && !para_into_left {
                    continue; // Skip left side if not allowed
                }
                if i == 1 && !para_into_right {
                    continue; // Skip right side if not allowed
                }
            }

            let sub_replacements = find_and_replace_subterms(
                arg,
                pattern,
                replacement,
                eq_symbol,
                false, // Only the top-level term is the equality
                para_into_left,
                para_into_right,
            );

            for (new_arg, subst) in sub_replacements {
                let mut new_args = args.clone();
                new_args[i] = new_arg;
                let new_term = Term::Application {
                    symbol: *symbol,
                    args: new_args,
                };
                results.push((new_term, subst));
            }
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::symbol::{SymbolKind, SymbolTable};
    use crate::data::VariableId;

    fn make_var(id: u16) -> Term {
        Term::variable(VariableId::new(id))
    }

    fn make_const(table: &SymbolTable, name: &str) -> Term {
        let sym = table.intern(name, 0, SymbolKind::Constant);
        Term::application(sym, vec![])
    }

    fn make_fun(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Function);
        Term::application(sym, args)
    }

    fn make_pred(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Predicate);
        Term::application(sym, args)
    }

    #[test]
    fn paramodulate_simple() {
        let table = SymbolTable::new();
        let eq_sym = table.intern("=", 2, SymbolKind::Function);

        let a = make_const(&table, "a");
        let b = make_const(&table, "b");
        let f_a = make_fun(&table, "f", vec![a.clone()]);

        // From: f(a) = b
        let eq_lit = Literal::new(true, Term::application(eq_sym, vec![f_a.clone(), b.clone()]));
        let from_clause = Clause::new(vec![eq_lit]);

        // Into: P(f(a))
        let p_fa = make_pred(&table, "P", vec![f_a]);
        let into_clause = Clause::new(vec![Literal::new(true, p_fa)]);

        let results = paramodulate_into(
            &from_clause,
            None,
            &into_clause,
            None,
            eq_sym,
            true,  // para_from_left
            true,  // para_from_right
            true,  // para_into_left
            true,  // para_into_right
        );

        assert!(!results.is_empty(), "Should produce at least one paramodulant");
        // Result should be P(b)
        assert_eq!(results[0].clause.literals.len(), 1);
    }

    #[test]
    fn paramodulate_with_variable() {
        let table = SymbolTable::new();
        let eq_sym = table.intern("=", 2, SymbolKind::Function);

        let x = make_var(0);
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");
        let f_x = make_fun(&table, "f", vec![x.clone()]);
        let f_a = make_fun(&table, "f", vec![a.clone()]);

        // From: f(X) = b
        let eq_lit = Literal::new(true, Term::application(eq_sym, vec![f_x, b.clone()]));
        let from_clause = Clause::new(vec![eq_lit]);

        // Into: P(f(a))
        let p_fa = make_pred(&table, "P", vec![f_a]);
        let into_clause = Clause::new(vec![Literal::new(true, p_fa)]);

        let results = paramodulate_into(
            &from_clause,
            None,
            &into_clause,
            None,
            eq_sym,
            true,  // para_from_left
            true,  // para_from_right
            true,  // para_into_left
            true,  // para_into_right
        );

        assert!(!results.is_empty(), "Should produce paramodulant with X=a");
    }
}
