use std::collections::HashMap;
use std::sync::{
    RwLock,
    atomic::{AtomicU32, Ordering},
};

/// Identifier for a symbol registered in the symbol table.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(u32);

impl SymbolId {
    pub const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    pub const fn as_raw(self) -> u32 {
        self.0
    }
}

/// Kinds of symbols recognised by the prover.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Function,
    Predicate,
    Constant,
    Variable,
    Evaluator,
    Special,
}

/// Metadata recorded for each symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: String,
    pub arity: u8,
    pub kind: SymbolKind,
}

impl Symbol {
    pub fn new(
        id: SymbolId,
        name: impl Into<String>,
        arity: u8,
        kind: SymbolKind,
    ) -> Self {
        Self { id, name: name.into(), arity, kind }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SymbolKey {
    name: String,
    arity: u8,
}

impl SymbolKey {
    fn new(name: &str, arity: u8) -> Self {
        Self { name: name.to_string(), arity }
    }
}

/// Symbol table used throughout the prover.  Eventually this mirrors the
/// behaviour of the `built_in_symbols` and related routines from the C
/// implementation.
#[derive(Debug, Default)]
pub struct SymbolTable {
    next_id: AtomicU32,
    symbols: RwLock<HashMap<SymbolKey, Symbol>>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(
        &self,
        name: impl AsRef<str>,
        arity: u8,
        kind: SymbolKind,
    ) -> SymbolId {
        let key = SymbolKey::new(name.as_ref(), arity);
        {
            let guard = self.symbols.read().expect("symbol table poisoned");
            if let Some(existing) = guard.get(&key) {
                return existing.id;
            }
        }

        let mut guard = self.symbols.write().expect("symbol table poisoned");
        if let Some(existing) = guard.get(&key) {
            return existing.id;
        }

        let id = SymbolId(self.next_id.fetch_add(1, Ordering::SeqCst));
        guard.insert(key, Symbol::new(id, name.as_ref(), arity, kind));
        id
    }

    pub fn get(&self, id: SymbolId) -> Option<Symbol> {
        let guard = self.symbols.read().expect("symbol table poisoned");
        guard.values().find(|symbol| symbol.id == id).cloned()
    }

    pub fn len(&self) -> usize {
        let guard = self.symbols.read().expect("symbol table poisoned");
        guard.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::{SymbolKind, SymbolTable};

    #[test]
    fn interning_assigns_ids() {
        let table = SymbolTable::new();
        let id_a = table.intern("f", 2, SymbolKind::Function);
        let id_b = table.intern("f", 2, SymbolKind::Function);
        assert_eq!(id_a, id_b, "interning must be stable for identical keys");
        assert_eq!(table.len(), 1);
    }
}
