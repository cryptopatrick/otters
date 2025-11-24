//! Unification algorithm for first-order terms.
//!
//! Implements the standard Robinson unification algorithm with occurs check.

use crate::data::{Literal, Term, VariableId};
use std::collections::HashMap;
use std::fmt;

/// A substitution mapping variables to terms.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Substitution {
    bindings: HashMap<VariableId, Term>,
}

impl Substitution {
    /// Create an empty substitution.
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a variable to a term.
    pub fn bind(&mut self, var: VariableId, term: Term) {
        self.bindings.insert(var, term);
    }

    /// Look up a variable's binding.
    pub fn lookup(&self, var: VariableId) -> Option<&Term> {
        self.bindings.get(&var)
    }

    /// Check if the substitution is empty.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Get the number of bindings.
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Iterate over all bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&VariableId, &Term)> {
        self.bindings.iter()
    }

    /// Apply this substitution to a term, returning a new term.
    pub fn apply(&self, term: &Term) -> Term {
        match term {
            Term::Variable { id, symbol } => {
                if let Some(bound_term) = self.lookup(*id) {
                    // Recursively apply to handle chains of substitutions
                    self.apply(bound_term)
                } else {
                    Term::Variable { id: *id, symbol: *symbol }
                }
            }
            Term::Application { symbol, args } => {
                let new_args = args.iter().map(|arg| self.apply(arg)).collect();
                Term::Application { symbol: *symbol, args: new_args }
            }
        }
    }

    /// Apply this substitution to a literal.
    pub fn apply_to_literal(&self, lit: &Literal) -> Literal {
        Literal::new(lit.sign, self.apply(&lit.atom)).with_target(lit.target)
    }

    /// Compose this substitution with another.
    /// The result applies self first, then other.
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = Substitution::new();

        // Apply other to all terms in self
        for (var, term) in &self.bindings {
            result.bind(*var, other.apply(term));
        }

        // Add bindings from other that aren't in self
        for (var, term) in &other.bindings {
            if !result.bindings.contains_key(var) {
                result.bind(*var, term.clone());
            }
        }

        result
    }
}

/// Errors that can occur during unification.
#[derive(Clone, Debug, PartialEq)]
pub enum UnificationError {
    /// Occurs check failed (variable occurs in term it's being unified with)
    OccursCheck { var: VariableId, term: Term },
    /// Symbol clash (different function symbols)
    SymbolClash { expected: Term, found: Term },
    /// Arity mismatch
    ArityMismatch { expected: usize, found: usize },
}

impl fmt::Display for UnificationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnificationError::OccursCheck { var, .. } => {
                write!(f, "occurs check failed for variable {:?}", var)
            }
            UnificationError::SymbolClash { .. } => {
                write!(f, "symbol clash during unification")
            }
            UnificationError::ArityMismatch { expected, found } => {
                write!(f, "arity mismatch: expected {}, found {}", expected, found)
            }
        }
    }
}

impl std::error::Error for UnificationError {}

/// Unifier for first-order terms.
#[derive(Clone, Debug, Default)]
pub struct Unifier {
    /// Current substitution being built
    substitution: Substitution,
}

impl Unifier {
    /// Create a new unifier.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the current substitution.
    pub fn substitution(&self) -> &Substitution {
        &self.substitution
    }

    /// Consume the unifier and return the substitution.
    pub fn into_substitution(self) -> Substitution {
        self.substitution
    }

    /// Reset the unifier for reuse.
    pub fn reset(&mut self) {
        self.substitution = Substitution::new();
    }

    /// Attempt to unify two terms.
    ///
    /// Returns Ok(()) if unification succeeds, updating the internal substitution.
    /// Returns Err if unification fails.
    pub fn unify(&mut self, t1: &Term, t2: &Term) -> Result<(), UnificationError> {
        // Apply current substitution to get the "dereferenced" terms
        let t1 = self.substitution.apply(t1);
        let t2 = self.substitution.apply(t2);

        match (&t1, &t2) {
            // Both are the same variable - already unified
            (Term::Variable { id: id1, .. }, Term::Variable { id: id2, .. })
                if id1 == id2 =>
            {
                Ok(())
            }

            // Variable on the left - bind it
            (Term::Variable { id, .. }, _) => {
                if self.occurs_in(*id, &t2) {
                    return Err(UnificationError::OccursCheck {
                        var: *id,
                        term: t2,
                    });
                }
                self.substitution.bind(*id, t2);
                Ok(())
            }

            // Variable on the right - bind it
            (_, Term::Variable { id, .. }) => {
                if self.occurs_in(*id, &t1) {
                    return Err(UnificationError::OccursCheck {
                        var: *id,
                        term: t1,
                    });
                }
                self.substitution.bind(*id, t1);
                Ok(())
            }

            // Both are applications
            (
                Term::Application { symbol: s1, args: args1 },
                Term::Application { symbol: s2, args: args2 },
            ) => {
                // Check symbol match
                if s1 != s2 {
                    return Err(UnificationError::SymbolClash {
                        expected: t1.clone(),
                        found: t2.clone(),
                    });
                }

                // Check arity match
                if args1.len() != args2.len() {
                    return Err(UnificationError::ArityMismatch {
                        expected: args1.len(),
                        found: args2.len(),
                    });
                }

                // Recursively unify arguments
                for (a1, a2) in args1.iter().zip(args2.iter()) {
                    self.unify(a1, a2)?;
                }

                Ok(())
            }
        }
    }

    /// Check if a variable occurs in a term.
    fn occurs_in(&self, var: VariableId, term: &Term) -> bool {
        match term {
            Term::Variable { id, .. } => {
                if *id == var {
                    return true;
                }
                // Check if this variable is bound to something containing var
                if let Some(bound) = self.substitution.lookup(*id) {
                    return self.occurs_in(var, bound);
                }
                false
            }
            Term::Application { args, .. } => {
                args.iter().any(|arg| self.occurs_in(var, arg))
            }
        }
    }
}

/// Convenience function to unify two terms.
pub fn unify(t1: &Term, t2: &Term) -> Result<Substitution, UnificationError> {
    let mut unifier = Unifier::new();
    unifier.unify(t1, t2)?;
    Ok(unifier.into_substitution())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::symbol::{SymbolKind, SymbolTable};

    fn make_var(id: u16) -> Term {
        Term::variable(VariableId::new(id))
    }

    fn make_const(table: &SymbolTable, name: &str) -> Term {
        let sym = table.intern(name, 0, SymbolKind::Constant);
        Term::application(sym, vec![])
    }

    fn make_app(table: &SymbolTable, name: &str, args: Vec<Term>) -> Term {
        let sym = table.intern(name, args.len() as u8, SymbolKind::Function);
        Term::application(sym, args)
    }

    #[test]
    fn unify_identical_variables() {
        let x = make_var(0);
        let result = unify(&x, &x);
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn unify_variable_with_constant() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        let result = unify(&x, &a);
        assert!(result.is_ok());
        let subst = result.unwrap();
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.apply(&x), a);
    }

    #[test]
    fn unify_identical_constants() {
        let table = SymbolTable::new();
        let a1 = make_const(&table, "a");
        let a2 = make_const(&table, "a");

        let result = unify(&a1, &a2);
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn unify_different_constants_fails() {
        let table = SymbolTable::new();
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        let result = unify(&a, &b);
        assert!(matches!(result, Err(UnificationError::SymbolClash { .. })));
    }

    #[test]
    fn unify_complex_terms() {
        let table = SymbolTable::new();
        // f(x, a) and f(b, y)
        let x = make_var(0);
        let y = make_var(1);
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        let t1 = make_app(&table, "f", vec![x.clone(), a.clone()]);
        let t2 = make_app(&table, "f", vec![b.clone(), y.clone()]);

        let result = unify(&t1, &t2);
        assert!(result.is_ok());
        let subst = result.unwrap();

        // x -> b, y -> a
        assert_eq!(subst.apply(&x), b);
        assert_eq!(subst.apply(&y), a);
    }

    #[test]
    fn unify_nested_terms() {
        let table = SymbolTable::new();
        // f(g(x)) and f(y)
        let x = make_var(0);
        let y = make_var(1);

        let inner = make_app(&table, "g", vec![x.clone()]);
        let t1 = make_app(&table, "f", vec![inner.clone()]);
        let t2 = make_app(&table, "f", vec![y.clone()]);

        let result = unify(&t1, &t2);
        assert!(result.is_ok());
        let subst = result.unwrap();

        // y -> g(x)
        assert_eq!(subst.apply(&y), inner);
    }

    #[test]
    fn occurs_check_fails() {
        let table = SymbolTable::new();
        // x and f(x) should fail occurs check
        let x = make_var(0);
        let fx = make_app(&table, "f", vec![x.clone()]);

        let result = unify(&x, &fx);
        assert!(matches!(result, Err(UnificationError::OccursCheck { .. })));
    }

    #[test]
    fn unify_with_shared_variable() {
        let table = SymbolTable::new();
        // f(x, x) and f(a, a)
        let x = make_var(0);
        let a = make_const(&table, "a");

        let t1 = make_app(&table, "f", vec![x.clone(), x.clone()]);
        let t2 = make_app(&table, "f", vec![a.clone(), a.clone()]);

        let result = unify(&t1, &t2);
        assert!(result.is_ok());
        let subst = result.unwrap();
        assert_eq!(subst.apply(&x), a);
    }

    #[test]
    fn unify_shared_variable_different_values_fails() {
        let table = SymbolTable::new();
        // f(x, x) and f(a, b)
        let x = make_var(0);
        let a = make_const(&table, "a");
        let b = make_const(&table, "b");

        let t1 = make_app(&table, "f", vec![x.clone(), x.clone()]);
        let t2 = make_app(&table, "f", vec![a, b]);

        let result = unify(&t1, &t2);
        assert!(result.is_err());
    }

    #[test]
    fn substitution_apply() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let a = make_const(&table, "a");

        let mut subst = Substitution::new();
        subst.bind(VariableId::new(0), a.clone());

        let t = make_app(&table, "f", vec![x]);
        let applied = subst.apply(&t);

        let expected = make_app(&table, "f", vec![a]);
        assert_eq!(applied, expected);
    }

    #[test]
    fn substitution_compose() {
        let table = SymbolTable::new();
        let x = make_var(0);
        let y = make_var(1);
        let a = make_const(&table, "a");

        // s1: x -> y
        let mut s1 = Substitution::new();
        s1.bind(VariableId::new(0), y.clone());

        // s2: y -> a
        let mut s2 = Substitution::new();
        s2.bind(VariableId::new(1), a.clone());

        // Compose: x -> a, y -> a
        let composed = s1.compose(&s2);
        assert_eq!(composed.apply(&x), a);
        assert_eq!(composed.apply(&y), a);
    }
}
