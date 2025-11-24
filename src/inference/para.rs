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
pub fn paramodulate_into(
    from_clause: &Clause,
    from_id: Option<ClauseId>,
    into_clause: &Clause,
    into_id: Option<ClauseId>,
    eq_symbol: crate::data::SymbolId,
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
            // Try replacing subterms in the into literal
            let replacements = find_and_replace_subterms(
                &into_lit.atom,
                left,
                right,
                &from_clause.literals,
                from_lit,
            );

            for (new_atom, subst) in replacements {
                // Build the result clause
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
                        new_literals.push(Literal::new(into_lit.sign, new_atom.clone()));
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

                results.push(Paramodulant {
                    clause: result_clause,
                    from_id,
                    into_id,
                    substitution: subst,
                });
            }
        }
    }

    results
}

/// Find all positions in a term where we can replace it with an equal term.
fn find_and_replace_subterms(
    target: &Term,
    pattern: &Term,
    replacement: &Term,
    from_lits: &[Literal],
    from_eq_lit: &Literal,
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
            let sub_replacements = find_and_replace_subterms(
                arg,
                pattern,
                replacement,
                from_lits,
                from_eq_lit,
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

        let results = paramodulate_into(&from_clause, None, &into_clause, None, eq_sym);

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

        let results = paramodulate_into(&from_clause, None, &into_clause, None, eq_sym);

        assert!(!results.is_empty(), "Should produce paramodulant with X=a");
    }
}
