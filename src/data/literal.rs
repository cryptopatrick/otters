use super::term::Term;

/// Representation of a clause literal.
#[derive(Clone, Debug, PartialEq)]
pub struct Literal {
    pub sign: bool,
    pub atom: Term,
    pub target: bool,
}

impl Literal {
    pub fn new(sign: bool, atom: Term) -> Self {
        Self { sign, atom, target: false }
    }

    pub fn with_target(mut self, target: bool) -> Self {
        self.target = target;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::Literal;
    use crate::data::VariableId;
    use crate::data::term::Term;

    #[test]
    fn create_literal() {
        let term = Term::variable(VariableId::new(1));
        let lit = Literal::new(true, term.clone());
        assert!(lit.sign);
        assert_eq!(lit.atom, term);
        assert!(!lit.target);
    }
}
