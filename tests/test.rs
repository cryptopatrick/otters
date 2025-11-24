use otters::{
    Clause, ClauseArena, ClauseId, ClauseList, Context, ContextStatus,
    ExampleSuite, FlagSet, ImdNode, ImdNodeKind, Literal, ParameterSet,
    ParameterValue, Parser, RegressionExecutor, Statistics, SymbolKind,
    SymbolTable, Term, TermKind, VariableId,
};

#[test]
fn example_suite_has_inputs() {
    let suite = ExampleSuite::default();
    let cases =
        suite.available_cases().expect("example discovery should succeed");
    assert!(!cases.is_empty(), "expected at least one regression case");
}

#[test]
fn symbol_table_interning() {
    let table = SymbolTable::new();
    let f = table.intern("f", 2, SymbolKind::Function);
    let g = table.intern("f", 2, SymbolKind::Function);
    assert_eq!(f, g, "interning must avoid duplicates");
}

#[test]
fn flags_and_parameters_basic_usage() {
    let mut flags = FlagSet::new();
    flags.enable("report");
    assert!(flags.is_enabled("report"));

    let mut params = ParameterSet::new();
    params.set("max_seconds", ParameterValue::Integer(10));
    assert_eq!(params.get_int("max_seconds"), Some(10));
}

#[test]
fn clause_arena_assigns_monotonic_ids() {
    let mut arena = ClauseArena::new();
    let clause_a = Clause::new(vec![Literal::new(
        true,
        Term::variable(VariableId::new(0)),
    )]);
    let clause_b = Clause::new(vec![Literal::new(
        false,
        Term::variable(VariableId::new(1)),
    )]);
    let id_a = arena.insert(clause_a);
    let id_b = arena.insert(clause_b);
    assert_eq!(id_a, ClauseId(1));
    assert_eq!(id_b, ClauseId(2));
    assert!(arena.get(id_a).is_some());
}

#[test]
fn clause_list_orders_members() {
    let mut list = ClauseList::new("sos");
    list.push(ClauseId(3));
    list.push(ClauseId(1));
    let collected: Vec<_> = list.iter().cloned().collect();
    assert_eq!(collected, vec![ClauseId(3), ClauseId(1)]);
}

#[test]
fn statistics_counters_increment() {
    let mut stats = Statistics::new();
    stats.increment("clauses_generated");
    stats.increment_by("clauses_generated", 4);
    assert_eq!(stats.get("clauses_generated"), Some(5));
    stats.reset("clauses_generated");
    assert!(stats.get("clauses_generated").is_none());
}

#[test]
fn context_assignment() {
    let mut ctx = Context::new();
    let var = VariableId::new(0);
    ctx.assign(var, Term::variable(var));
    assert_eq!(ctx.status(var), ContextStatus::Bound);
}

#[test]
fn parser_handles_simple_input() {
    let parser = Parser::new();
    let input = "list(usable).\n P(a).\n end_of_list.";
    let parsed =
        parser.parse_str(input).expect("parser should accept simple list");
    assert_eq!(parsed.lists.len(), 1);
}

#[test]
fn regression_executor_dry_run() {
    let executor = RegressionExecutor::new(ExampleSuite::default());
    let summary = executor.run_dry();
    assert!(summary.total() > 0);
}

#[test]
fn indexing_node_constructors() {
    let table = SymbolTable::new();
    let pred = table.intern("p", 0, SymbolKind::Predicate);
    let mut node = ImdNode::new(ImdNodeKind::Symbol(pred));
    node.add_child(ImdNode::new(ImdNodeKind::Variable));
    assert_eq!(node.children.len(), 1);
}

#[test]
fn term_kind_variable_application() {
    let table = SymbolTable::new();
    let const_id = table.intern("a", 0, SymbolKind::Constant);
    let term = Term::application(const_id, vec![]);
    assert_eq!(term.kind(), TermKind::Name);
}
