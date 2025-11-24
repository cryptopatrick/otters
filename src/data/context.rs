use super::{Term, VariableId};

pub const MAX_VARS: usize = 64;

/// Status associated with a variable binding inside a substitution context.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum ContextStatus {
    #[default]
    Unbound,
    Bound,
    Frozen,
}

/// Substitution context that mirrors the legacy `struct context` layout.
#[derive(Clone, Debug)]
pub struct Context {
    terms: [Option<Term>; MAX_VARS],
    statuses: [ContextStatus; MAX_VARS],
    multiplier: i32,
    built_in_multiplier: i32,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            terms: std::array::from_fn(|_| None),
            statuses: [ContextStatus::Unbound; MAX_VARS],
            multiplier: 1,
            built_in_multiplier: 1,
        }
    }
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn assign(&mut self, var: VariableId, term: Term) {
        let index = var.as_u16() as usize;
        if index >= MAX_VARS {
            panic!("variable index {} exceeds MAX_VARS", index);
        }
        self.terms[index] = Some(term);
        self.statuses[index] = ContextStatus::Bound;
    }

    pub fn lookup(&self, var: VariableId) -> Option<&Term> {
        let index = var.as_u16() as usize;
        self.terms.get(index).and_then(|entry| entry.as_ref())
    }

    pub fn clear(&mut self, var: VariableId) {
        let index = var.as_u16() as usize;
        if index < MAX_VARS {
            self.terms[index] = None;
            self.statuses[index] = ContextStatus::Unbound;
        }
    }

    pub fn reset(&mut self) {
        for slot in &mut self.terms {
            *slot = None;
        }
        self.statuses.fill(ContextStatus::Unbound);
        self.multiplier = 1;
        self.built_in_multiplier = 1;
    }

    pub fn status(&self, var: VariableId) -> ContextStatus {
        let index = var.as_u16() as usize;
        self.statuses.get(index).copied().unwrap_or(ContextStatus::Unbound)
    }

    pub fn set_status(&mut self, var: VariableId, status: ContextStatus) {
        let index = var.as_u16() as usize;
        if index < MAX_VARS {
            self.statuses[index] = status;
        }
    }

    pub fn multiplier(&self) -> i32 {
        self.multiplier
    }

    pub fn set_multiplier(&mut self, multiplier: i32) {
        self.multiplier = multiplier;
    }

    pub fn built_in_multiplier(&self) -> i32 {
        self.built_in_multiplier
    }

    pub fn set_built_in_multiplier(&mut self, multiplier: i32) {
        self.built_in_multiplier = multiplier;
    }
}

/// Trail entry recording substitutions to facilitate backtracking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrailEntry {
    pub context: usize,
    pub variable: VariableId,
}

/// Trail stack used for unification undo operations.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Trail {
    entries: Vec<TrailEntry>,
}

impl Trail {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, context: usize, variable: VariableId) {
        self.entries.push(TrailEntry { context, variable });
    }

    pub fn pop(&mut self) -> Option<TrailEntry> {
        self.entries.pop()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::{Context, ContextStatus, Trail};
    use crate::data::{Term, VariableId};

    #[test]
    fn context_assign_and_lookup() {
        let mut ctx = Context::new();
        let var = VariableId::new(1);
        ctx.assign(var, Term::variable(var));
        assert!(ctx.lookup(var).is_some());
        assert_eq!(ctx.status(var), ContextStatus::Bound);
        ctx.clear(var);
        assert!(ctx.lookup(var).is_none());
    }

    #[test]
    fn trail_push_and_pop() {
        let mut trail = Trail::new();
        trail.push(0, VariableId::new(2));
        assert_eq!(trail.len(), 1);
        let entry = trail.pop().expect("entry");
        assert_eq!(entry.context, 0);
        assert_eq!(entry.variable, VariableId::new(2));
        assert!(trail.is_empty());
    }
}
