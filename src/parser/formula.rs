//! Formula parsing and conversion to clauses.
//!
//! Handles first-order formulas with quantifiers (all, exists)
//! and converts them to clause form through:
//! 1. Parsing the formula syntax
//! 2. Skolemization (removing existential quantifiers)
//! 3. CNF conversion (converting to conjunctive normal form)

use crate::data::{Clause, Literal, SymbolId, SymbolTable, Term, VariableId};
use crate::data::symbol::SymbolKind;
use crate::parser::ParseError;
use std::collections::HashMap;

/// A first-order formula with quantifiers and logical connectives.
#[derive(Clone, Debug, PartialEq)]
pub enum Formula {
    /// Atomic formula (predicate or equality)
    Atom(Literal),
    /// Negation
    Not(Box<Formula>),
    /// Conjunction (AND)
    And(Box<Formula>, Box<Formula>),
    /// Disjunction (OR)
    Or(Box<Formula>, Box<Formula>),
    /// Implication
    Implies(Box<Formula>, Box<Formula>),
    /// Biconditional (if and only if)
    Iff(Box<Formula>, Box<Formula>),
    /// Universal quantification
    Forall(String, Box<Formula>),
    /// Existential quantification
    Exists(String, Box<Formula>),
}

impl Formula {
    /// Convert formula to clauses through Skolemization and CNF conversion.
    pub fn to_clauses(&self, symbols: &SymbolTable) -> Result<Vec<Clause>, String> {
        // Step 1: Remove implications (A -> B becomes -A | B)
        let no_implies = self.remove_implications();

        // Step 2: Push negations inward (De Morgan's laws)
        let nnf = no_implies.to_negation_normal_form();

        // Step 3: Skolemize (remove existential quantifiers)
        let mut skolem_counter = 0;
        let skolemized = nnf.skolemize(&[], &mut skolem_counter, symbols);

        // Step 4: Drop universal quantifiers (they're implicit in clauses)
        let quantifier_free = skolemized.drop_universal();

        // Step 5: Convert to CNF
        let cnf = quantifier_free.to_cnf();

        // Step 6: Extract clauses from CNF
        cnf.extract_clauses()
    }

    /// Remove implications: A -> B becomes -A | B
    /// Remove biconditionals: A <-> B becomes (A -> B) & (B -> A) becomes (-A | B) & (-B | A)
    fn remove_implications(&self) -> Formula {
        match self {
            Formula::Implies(a, b) => {
                let not_a = Formula::Not(Box::new(a.remove_implications()));
                let b_clean = b.remove_implications();
                Formula::Or(Box::new(not_a), Box::new(b_clean))
            }
            Formula::Iff(a, b) => {
                // A <-> B becomes (A -> B) & (B -> A)
                // which becomes (-A | B) & (-B | A)
                let a_clean = a.remove_implications();
                let b_clean = b.remove_implications();
                let not_a = Formula::Not(Box::new(a_clean.clone()));
                let not_b = Formula::Not(Box::new(b_clean.clone()));
                let left = Formula::Or(Box::new(not_a), Box::new(b_clean));
                let right = Formula::Or(Box::new(not_b), Box::new(a_clean));
                Formula::And(Box::new(left), Box::new(right))
            }
            Formula::Not(f) => Formula::Not(Box::new(f.remove_implications())),
            Formula::And(a, b) => Formula::And(
                Box::new(a.remove_implications()),
                Box::new(b.remove_implications()),
            ),
            Formula::Or(a, b) => Formula::Or(
                Box::new(a.remove_implications()),
                Box::new(b.remove_implications()),
            ),
            Formula::Forall(var, f) => {
                Formula::Forall(var.clone(), Box::new(f.remove_implications()))
            }
            Formula::Exists(var, f) => {
                Formula::Exists(var.clone(), Box::new(f.remove_implications()))
            }
            Formula::Atom(_) => self.clone(),
        }
    }

    /// Convert to negation normal form (push negations inward)
    fn to_negation_normal_form(&self) -> Formula {
        match self {
            Formula::Not(f) => match &**f {
                // Double negation: --A becomes A
                Formula::Not(inner) => inner.to_negation_normal_form(),
                // De Morgan: -(A & B) becomes (-A | -B)
                Formula::And(a, b) => {
                    let not_a = Formula::Not(Box::new((**a).clone())).to_negation_normal_form();
                    let not_b = Formula::Not(Box::new((**b).clone())).to_negation_normal_form();
                    Formula::Or(Box::new(not_a), Box::new(not_b))
                }
                // De Morgan: -(A | B) becomes (-A & -B)
                Formula::Or(a, b) => {
                    let not_a = Formula::Not(Box::new((**a).clone())).to_negation_normal_form();
                    let not_b = Formula::Not(Box::new((**b).clone())).to_negation_normal_form();
                    Formula::And(Box::new(not_a), Box::new(not_b))
                }
                // Quantifier negation: -all x P becomes exists x -P
                Formula::Forall(var, inner) => {
                    let neg_inner = Formula::Not(Box::new((**inner).clone())).to_negation_normal_form();
                    Formula::Exists(var.clone(), Box::new(neg_inner))
                }
                // Quantifier negation: -exists x P becomes all x -P
                Formula::Exists(var, inner) => {
                    let neg_inner = Formula::Not(Box::new((**inner).clone())).to_negation_normal_form();
                    Formula::Forall(var.clone(), Box::new(neg_inner))
                }
                // Atom: keep negation
                Formula::Atom(_) => self.clone(),
                // Should not have implications/biconditionals at this point
                Formula::Implies(_, _) => panic!("Implications should be removed before NNF"),
                Formula::Iff(_, _) => panic!("Biconditionals should be removed before NNF"),
            },
            Formula::And(a, b) => Formula::And(
                Box::new(a.to_negation_normal_form()),
                Box::new(b.to_negation_normal_form()),
            ),
            Formula::Or(a, b) => Formula::Or(
                Box::new(a.to_negation_normal_form()),
                Box::new(b.to_negation_normal_form()),
            ),
            Formula::Forall(var, f) => {
                Formula::Forall(var.clone(), Box::new(f.to_negation_normal_form()))
            }
            Formula::Exists(var, f) => {
                Formula::Exists(var.clone(), Box::new(f.to_negation_normal_form()))
            }
            Formula::Atom(_) => self.clone(),
            Formula::Implies(_, _) => panic!("Implications should be removed before NNF"),
            Formula::Iff(_, _) => panic!("Biconditionals should be removed before NNF"),
        }
    }

    /// Skolemize: replace existential quantifiers with Skolem functions
    fn skolemize(
        &self,
        universal_vars: &[String],
        counter: &mut usize,
        symbols: &SymbolTable,
    ) -> Formula {
        match self {
            Formula::Exists(var, f) => {
                // Create Skolem function: sk_N(univ_vars...)
                let skolem_name = format!("sk_{}", counter);
                *counter += 1;

                let skolem_sym = symbols.intern(
                    &skolem_name,
                    universal_vars.len() as u8,
                    SymbolKind::Function,
                );

                // Replace var with skolem function applied to universal vars
                let mut new_f = (**f).clone();
                new_f = new_f.substitute_var(var, &self.make_skolem_term(skolem_sym, universal_vars));

                // Continue skolemizing
                new_f.skolemize(universal_vars, counter, symbols)
            }
            Formula::Forall(var, f) => {
                // Add to universal vars and continue
                let mut new_universal = universal_vars.to_vec();
                new_universal.push(var.clone());
                let inner = f.skolemize(&new_universal, counter, symbols);
                Formula::Forall(var.clone(), Box::new(inner))
            }
            Formula::And(a, b) => Formula::And(
                Box::new(a.skolemize(universal_vars, counter, symbols)),
                Box::new(b.skolemize(universal_vars, counter, symbols)),
            ),
            Formula::Or(a, b) => Formula::Or(
                Box::new(a.skolemize(universal_vars, counter, symbols)),
                Box::new(b.skolemize(universal_vars, counter, symbols)),
            ),
            Formula::Not(f) => {
                Formula::Not(Box::new(f.skolemize(universal_vars, counter, symbols)))
            }
            Formula::Atom(_) => self.clone(),
            Formula::Implies(_, _) => panic!("Implications should be removed before Skolemization"),
            Formula::Iff(_, _) => panic!("Biconditionals should be removed before Skolemization"),
        }
    }

    /// Create a Skolem term from function symbol and universal variables
    fn make_skolem_term(&self, skolem_sym: SymbolId, universal_vars: &[String]) -> Term {
        if universal_vars.is_empty() {
            // Skolem constant (no universal variables)
            Term::Application {
                symbol: skolem_sym,
                args: vec![],
            }
        } else {
            // Skolem function applied to universal variables
            let args = universal_vars
                .iter()
                .map(|var_name| {
                    // Convert variable name to VariableId
                    // Use first character as variable index (a=0, b=1, etc.)
                    let first_char = var_name.bytes().next().unwrap_or(b'a');
                    let var_id = if first_char >= b'a' && first_char <= b'z' {
                        VariableId::new((first_char - b'a') as u16)
                    } else if first_char >= b'A' && first_char <= b'Z' {
                        VariableId::new((first_char - b'A') as u16)
                    } else {
                        VariableId::new(0)
                    };
                    Term::variable(var_id)
                })
                .collect();
            Term::Application {
                symbol: skolem_sym,
                args,
            }
        }
    }

    /// Substitute a variable with a term throughout the formula
    fn substitute_var(&self, var: &str, term: &Term) -> Formula {
        match self {
            Formula::Atom(lit) => {
                Formula::Atom(Literal::new(lit.sign, Self::substitute_in_term(&lit.atom, var, term)))
            }
            Formula::Not(f) => Formula::Not(Box::new(f.substitute_var(var, term))),
            Formula::And(a, b) => Formula::And(
                Box::new(a.substitute_var(var, term)),
                Box::new(b.substitute_var(var, term)),
            ),
            Formula::Or(a, b) => Formula::Or(
                Box::new(a.substitute_var(var, term)),
                Box::new(b.substitute_var(var, term)),
            ),
            Formula::Forall(v, f) => {
                if v == var {
                    // Don't substitute bound variables
                    self.clone()
                } else {
                    Formula::Forall(v.clone(), Box::new(f.substitute_var(var, term)))
                }
            }
            Formula::Exists(v, f) => {
                if v == var {
                    // Don't substitute bound variables
                    self.clone()
                } else {
                    Formula::Exists(v.clone(), Box::new(f.substitute_var(var, term)))
                }
            }
            Formula::Implies(a, b) => Formula::Implies(
                Box::new(a.substitute_var(var, term)),
                Box::new(b.substitute_var(var, term)),
            ),
            Formula::Iff(a, b) => Formula::Iff(
                Box::new(a.substitute_var(var, term)),
                Box::new(b.substitute_var(var, term)),
            ),
        }
    }

    /// Substitute a variable in a term
    fn substitute_in_term(t: &Term, var: &str, replacement: &Term) -> Term {
        match t {
            Term::Variable { id: vid, symbol } => {
                // Check if this variable matches
                let var_char = var.bytes().next().unwrap_or(b'a');
                let expected_id = if var_char >= b'a' && var_char <= b'z' {
                    VariableId::new((var_char - b'a') as u16)
                } else if var_char >= b'A' && var_char <= b'Z' {
                    VariableId::new((var_char - b'A') as u16)
                } else {
                    VariableId::new(0)
                };
                if *vid == expected_id {
                    replacement.clone()
                } else {
                    Term::Variable { id: *vid, symbol: *symbol }
                }
            }
            Term::Application { symbol, args } => {
                let new_args = args
                    .iter()
                    .map(|arg| Self::substitute_in_term(arg, var, replacement))
                    .collect();
                Term::Application {
                    symbol: *symbol,
                    args: new_args,
                }
            }
        }
    }

    /// Drop universal quantifiers (they're implicit in clauses)
    fn drop_universal(&self) -> Formula {
        match self {
            Formula::Forall(_, f) => f.drop_universal(),
            Formula::And(a, b) => Formula::And(
                Box::new(a.drop_universal()),
                Box::new(b.drop_universal()),
            ),
            Formula::Or(a, b) => Formula::Or(
                Box::new(a.drop_universal()),
                Box::new(b.drop_universal()),
            ),
            Formula::Not(f) => Formula::Not(Box::new(f.drop_universal())),
            Formula::Atom(_) => self.clone(),
            Formula::Exists(_, _) => panic!("Existential quantifiers should be skolemized"),
            Formula::Implies(_, _) => panic!("Implications should be removed"),
            Formula::Iff(_, _) => panic!("Biconditionals should be removed"),
        }
    }

    /// Convert to CNF (conjunctive normal form)
    fn to_cnf(&self) -> Formula {
        match self {
            // Distribute OR over AND: (A | (B & C)) becomes (A | B) & (A | C)
            Formula::Or(a, b) => {
                let a_cnf = a.to_cnf();
                let b_cnf = b.to_cnf();

                match (&a_cnf, &b_cnf) {
                    (Formula::And(a1, a2), _) => {
                        // (A1 & A2) | B becomes (A1 | B) & (A2 | B)
                        let left = Formula::Or(a1.clone(), Box::new(b_cnf.clone())).to_cnf();
                        let right = Formula::Or(a2.clone(), Box::new(b_cnf)).to_cnf();
                        Formula::And(Box::new(left), Box::new(right))
                    }
                    (_, Formula::And(b1, b2)) => {
                        // A | (B1 & B2) becomes (A | B1) & (A | B2)
                        let left = Formula::Or(Box::new(a_cnf.clone()), b1.clone()).to_cnf();
                        let right = Formula::Or(Box::new(a_cnf), b2.clone()).to_cnf();
                        Formula::And(Box::new(left), Box::new(right))
                    }
                    _ => Formula::Or(Box::new(a_cnf), Box::new(b_cnf)),
                }
            }
            Formula::And(a, b) => {
                Formula::And(Box::new(a.to_cnf()), Box::new(b.to_cnf()))
            }
            Formula::Not(f) => Formula::Not(Box::new(f.to_cnf())),
            Formula::Atom(_) => self.clone(),
            _ => panic!("Unexpected formula type in CNF conversion"),
        }
    }

    /// Extract clauses from CNF formula
    fn extract_clauses(&self) -> Result<Vec<Clause>, String> {
        match self {
            Formula::And(a, b) => {
                let mut clauses = a.extract_clauses()?;
                clauses.extend(b.extract_clauses()?);
                Ok(clauses)
            }
            // Single clause (disjunction of literals)
            _ => {
                let literals = self.extract_literals()?;
                Ok(vec![Clause::new(literals)])
            }
        }
    }

    /// Extract literals from a disjunction
    fn extract_literals(&self) -> Result<Vec<Literal>, String> {
        match self {
            Formula::Or(a, b) => {
                let mut lits = a.extract_literals()?;
                lits.extend(b.extract_literals()?);
                Ok(lits)
            }
            Formula::Not(f) => {
                if let Formula::Atom(lit) = &**f {
                    Ok(vec![Literal::new(!lit.sign, lit.atom.clone())])
                } else {
                    Err("Expected atom in negation".to_string())
                }
            }
            Formula::Atom(lit) => Ok(vec![lit.clone()]),
            _ => Err(format!("Unexpected formula in literal extraction: {:?}", self)),
        }
    }
}

/// Parse a formula from text
pub fn parse_formula(text: &str, symbols: &SymbolTable) -> Result<Formula, ParseError> {
    let text = text.trim();
    if text.is_empty() {
        return Err(ParseError {
            line: 0,
            column: 0,
            message: "Empty formula".to_string(),
        });
    }

    let mut parser = FormulaParser {
        text,
        pos: 0,
        symbols,
    };

    parser.parse_formula()
}

/// Internal parser state for recursive descent parsing
struct FormulaParser<'a> {
    text: &'a str,
    pos: usize,
    symbols: &'a SymbolTable,
}

impl<'a> FormulaParser<'a> {
    fn parse_formula(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();
        self.parse_implication()
    }

    /// Parse implication and biconditional (lowest precedence)
    fn parse_implication(&mut self) -> Result<Formula, ParseError> {
        let left = self.parse_or()?;

        self.skip_whitespace();
        // Check for biconditional first (it's longer than implication)
        if self.peek_str("<->") {
            self.advance(3);
            let right = self.parse_implication()?;
            Ok(Formula::Iff(Box::new(left), Box::new(right)))
        } else if self.peek_str("->") {
            self.advance(2);
            let right = self.parse_implication()?;
            Ok(Formula::Implies(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    /// Parse OR (disjunction)
    fn parse_or(&mut self) -> Result<Formula, ParseError> {
        let mut left = self.parse_and()?;

        loop {
            self.skip_whitespace();
            if self.peek_char() == Some('|') && !self.peek_str("||") {
                self.advance(1);
                let right = self.parse_and()?;
                left = Formula::Or(Box::new(left), Box::new(right));
            } else {
                break;
            }
        }

        Ok(left)
    }

    /// Parse AND (conjunction)
    fn parse_and(&mut self) -> Result<Formula, ParseError> {
        let mut left = self.parse_quantifier()?;

        loop {
            self.skip_whitespace();
            if self.peek_char() == Some('&') && !self.peek_str("&&") {
                self.advance(1);
                let right = self.parse_quantifier()?;
                left = Formula::And(Box::new(left), Box::new(right));
            } else {
                break;
            }
        }

        Ok(left)
    }

    /// Parse quantifiers (all, exists)
    /// Supports both single and multiple variables: all x (...) and all x y z (...)
    fn parse_quantifier(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();

        if self.peek_str("all ") {
            self.advance(4);
            // Parse all variables until we hit something that's not a variable
            let mut vars = Vec::new();
            loop {
                self.skip_whitespace();
                // Check if we're at the start of the body (opening paren or formula)
                if self.peek_char() == Some('(') || self.peek_char() == Some('-')
                    || self.peek_str("all ") || self.peek_str("exists ") {
                    break;
                }
                let var = self.parse_variable()?;
                vars.push(var);
            }

            if vars.is_empty() {
                return Err(ParseError {
                    line: 0,
                    column: self.pos,
                    message: "Expected at least one variable after 'all'".to_string(),
                });
            }

            // Parse the body once
            self.skip_whitespace();
            let mut body = self.parse_quantifier()?;

            // Wrap in nested Forall quantifiers (right-to-left)
            for var in vars.into_iter().rev() {
                body = Formula::Forall(var, Box::new(body));
            }
            Ok(body)
        } else if self.peek_str("exists ") {
            self.advance(7);
            // Parse all variables until we hit something that's not a variable
            let mut vars = Vec::new();
            loop {
                self.skip_whitespace();
                // Check if we're at the start of the body (opening paren or formula)
                if self.peek_char() == Some('(') || self.peek_char() == Some('-')
                    || self.peek_str("all ") || self.peek_str("exists ") {
                    break;
                }
                let var = self.parse_variable()?;
                vars.push(var);
            }

            if vars.is_empty() {
                return Err(ParseError {
                    line: 0,
                    column: self.pos,
                    message: "Expected at least one variable after 'exists'".to_string(),
                });
            }

            // Parse the body once
            self.skip_whitespace();
            let mut body = self.parse_quantifier()?;

            // Wrap in nested Exists quantifiers (right-to-left)
            for var in vars.into_iter().rev() {
                body = Formula::Exists(var, Box::new(body));
            }
            Ok(body)
        } else {
            self.parse_unary()
        }
    }

    /// Parse unary (negation)
    fn parse_unary(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();

        if self.peek_char() == Some('-') && !self.peek_str("->") {
            self.advance(1);
            let inner = self.parse_unary()?;
            Ok(Formula::Not(Box::new(inner)))
        } else {
            self.parse_primary()
        }
    }

    /// Parse primary (atom or parenthesized formula)
    fn parse_primary(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();

        if self.peek_char() == Some('(') {
            self.advance(1);
            let formula = self.parse_formula()?;
            self.skip_whitespace();
            if self.peek_char() != Some(')') {
                return Err(ParseError {
                    line: 0,
                    column: self.pos,
                    message: "Expected ')'".to_string(),
                });
            }
            self.advance(1);
            Ok(formula)
        } else {
            // Parse atomic formula (predicate or equality)
            self.parse_atom()
        }
    }

    /// Parse atomic formula (predicate or equality)
    fn parse_atom(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();
        let start = self.pos;

        // Find the end of the atom, respecting nested parentheses
        let mut paren_depth = 0;
        while self.pos < self.text.len() {
            let ch = self.peek_char();
            match ch {
                Some('(') => {
                    paren_depth += 1;
                    self.pos += 1;
                }
                Some(')') => {
                    if paren_depth == 0 {
                        // This closes the formula, not the atom
                        break;
                    }
                    paren_depth -= 1;
                    self.pos += 1;
                }
                Some('&') | Some('|') if paren_depth == 0 => break,
                Some('<') if paren_depth == 0 && self.peek_str("<->") => break,
                Some('-') if paren_depth == 0 && self.peek_str("->") => break,
                _ => self.pos += 1,
            }
        }

        let atom_text = self.text[start..self.pos].trim();
        if atom_text.is_empty() {
            return Err(ParseError {
                line: 0,
                column: start,
                message: "Expected atom".to_string(),
            });
        }

        // Convert lowercase variables to uppercase for clause parser
        let normalized = Self::normalize_variables(atom_text);

        // Parse using existing literal parser (returns (Literal, attributes))
        let (literal, _) = crate::parser::syntax::parse_literal_internal(
            &normalized,
            self.symbols,
        )?;

        Ok(Formula::Atom(literal))
    }

    /// Convert lowercase variables (formula convention) to uppercase (clause convention)
    fn normalize_variables(text: &str) -> String {
        let mut result = String::with_capacity(text.len());
        let mut chars = text.chars().peekable();

        while let Some(ch) = chars.next() {
            if ch.is_ascii_lowercase() && ch.is_alphabetic() {
                // Check if this is a variable (single letter or letter not followed by alphanumeric)
                let next_is_alphanum = chars.peek().map(|c| c.is_alphanumeric()).unwrap_or(false);
                if !next_is_alphanum {
                    // Single letter variable - convert to uppercase
                    result.push(ch.to_ascii_uppercase());
                } else {
                    // Part of a function/predicate name - keep as is
                    result.push(ch);
                }
            } else {
                result.push(ch);
            }
        }

        result
    }

    /// Parse a variable name
    fn parse_variable(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        let start = self.pos;

        while self.pos < self.text.len() {
            let ch = self.text.as_bytes()[self.pos] as char;
            if ch.is_alphanumeric() || ch == '_' {
                self.pos += 1;
            } else {
                break;
            }
        }

        if self.pos == start {
            return Err(ParseError {
                line: 0,
                column: self.pos,
                message: "Expected variable name".to_string(),
            });
        }

        Ok(self.text[start..self.pos].to_string())
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.text.len() {
            let ch = self.text.as_bytes()[self.pos] as char;
            if ch.is_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn peek_char(&self) -> Option<char> {
        if self.pos < self.text.len() {
            Some(self.text.as_bytes()[self.pos] as char)
        } else {
            None
        }
    }

    fn peek_str(&self, s: &str) -> bool {
        self.text[self.pos..].starts_with(s)
    }

    fn advance(&mut self, n: usize) {
        self.pos += n;
    }
}
