use crate::data::{
    Clause, ClauseArena, ClauseAttribute, ClauseAttributeValue, ClauseList,
    Literal, SymbolId, SymbolKind, SymbolTable, Term, VariableId,
};
use std::fmt;

/// Different kinds of list sections encountered in Otter input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ListKind {
    Clause,
    Formula,
    Weight,
    Unknown(String),
}

impl fmt::Display for ListKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ListKind::Clause => write!(f, "clause"),
            ListKind::Formula => write!(f, "formula"),
            ListKind::Weight => write!(f, "weight"),
            ListKind::Unknown(value) => write!(f, "{}", value),
        }
    }
}

/// A single list section (e.g., `list(usable)` or `weight_list(pick_given)`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListSection {
    pub name: String,
    pub kind: ListKind,
    pub raw_entries: Vec<String>,
}

impl ListSection {
    pub fn to_clause_list(
        &self,
        arena: &mut ClauseArena,
        symbols: &SymbolTable,
        operators: &crate::parser::OperatorTable,
    ) -> Result<ClauseList, ParseError> {
        if !matches!(self.kind, ListKind::Clause) {
            return Err(ParseError::new(
                0,
                0,
                format!(
                    "list `{}` is not a clause list (kind: {:?})",
                    self.name, self.kind
                ),
            ));
        }

        let mut list = ClauseList::new(&self.name);
        for entry in &self.raw_entries {
            let mut clause = parse_clause(entry, symbols, operators)?;
            clause.add_attribute(ClauseAttribute::new(
                "list",
                ClauseAttributeValue::Text(self.name.clone()),
            ));
            clause.add_attribute(ClauseAttribute::new(
                "list_kind",
                ClauseAttributeValue::Text(self.kind.to_string()),
            ));
            let id = arena.insert(clause);
            list.push(id);
        }
        Ok(list)
    }

    pub fn weight_entries(&self) -> Result<Vec<WeightEntry>, ParseError> {
        if !matches!(self.kind, ListKind::Weight) {
            return Err(ParseError::new(
                0,
                0,
                format!("list `{}` is not a weight list", self.name),
            ));
        }

        let mut entries = Vec::new();
        for raw in &self.raw_entries {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                continue;
            }
            if !trimmed.starts_with("weight(") || !trimmed.ends_with(')') {
                return Err(ParseError::new(
                    0,
                    0,
                    format!("invalid weight entry: {}", trimmed),
                ));
            }
            let inner = &trimmed[7..trimmed.len() - 1];
            let comma_index =
                find_top_level_char(inner, ',').ok_or_else(|| {
                    ParseError::new(0, 0, "weight entry missing comma")
                })?;
            let term_part = inner[..comma_index].trim();
            let weight_part = inner[comma_index + 1..].trim();
            let weight = weight_part
                .parse::<i32>()
                .map_err(|_| ParseError::new(0, 0, "invalid weight value"))?;
            entries.push(WeightEntry { term: term_part.to_string(), weight });
        }
        Ok(entries)
    }

    /// Convert formula list to clause list via Skolemization and CNF conversion
    pub fn to_clause_list_from_formulas(
        &self,
        arena: &mut ClauseArena,
        symbols: &SymbolTable,
    ) -> Result<ClauseList, ParseError> {
        if !matches!(self.kind, ListKind::Formula) {
            return Err(ParseError::new(
                0,
                0,
                format!("list `{}` is not a formula list", self.name),
            ));
        }

        let mut list = ClauseList::new(&self.name);
        for entry in &self.raw_entries {
            // Parse the formula
            let formula = crate::parser::parse_formula(entry, symbols)?;

            // Convert to clauses via Skolemization and CNF
            let clauses = formula.to_clauses(symbols).map_err(|e| ParseError::new(0, 0, e))?;

            // Add all generated clauses to the list
            for mut clause in clauses {
                clause.add_attribute(ClauseAttribute::new(
                    "list",
                    ClauseAttributeValue::Text(self.name.clone()),
                ));
                clause.add_attribute(ClauseAttribute::new(
                    "list_kind",
                    ClauseAttributeValue::Text(self.kind.to_string()),
                ));
                let id = arena.insert(clause);
                list.push(id);
            }
        }
        Ok(list)
    }
}

/// Parsed weight entry from a `weight_list` section.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WeightEntry {
    pub term: String,
    pub weight: i32,
}

/// Representation of commands that appear outside of list sections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OtterCommand {
    Set(String),
    Clear(String),
    Assign { name: String, value: String },
    Op { precedence: u16, fixity: String, symbol: String },
    Lex { symbols: Vec<String> },
    MakeEvaluable { operator: String, evaluator: String },
    ProofObject(String),
    Generic(String),
}

/// Top-level parse result containing list sections and commands.
#[derive(Clone, Debug, PartialEq)]
pub struct OtterFile {
    pub lists: Vec<ListSection>,
    pub commands: Vec<OtterCommand>,
    pub operators: crate::parser::OperatorTable,
}

impl Default for OtterFile {
    fn default() -> Self {
        Self {
            lists: Vec::new(),
            commands: Vec::new(),
            operators: crate::parser::OperatorTable::new(),
        }
    }
}

impl OtterFile {
    pub fn get_list(&self, name: &str) -> Option<&ListSection> {
        self.lists.iter().find(|section| section.name == name)
    }
}

#[derive(Clone, Debug)]
struct ListBuilder {
    name: String,
    kind: ListKind,
    entries: Vec<String>,
    buffer: String,
    paren_depth: i32,
    bracket_depth: i32,
}

impl ListBuilder {
    fn new(name: String, kind: ListKind) -> Self {
        Self {
            name,
            kind,
            entries: Vec::new(),
            buffer: String::new(),
            paren_depth: 0,
            bracket_depth: 0,
        }
    }

    fn push_line(&mut self, line: &str) {
        let stripped = strip_comment(line);
        let trimmed = stripped.trim();
        if trimmed.is_empty() {
            return;
        }

        // Add space separator if buffer has content and doesn't end with space
        if !self.buffer.is_empty() && !self.buffer.ends_with(' ') {
            self.buffer.push(' ');
        }

        // Process character by character to split on periods at depth 0
        for ch in trimmed.chars() {
            match ch {
                '(' => {
                    self.buffer.push(ch);
                    self.paren_depth += 1;
                }
                ')' => {
                    self.buffer.push(ch);
                    self.paren_depth -= 1;
                }
                '[' => {
                    self.buffer.push(ch);
                    self.bracket_depth += 1;
                }
                ']' => {
                    self.buffer.push(ch);
                    self.bracket_depth -= 1;
                }
                '.' if self.paren_depth == 0 && self.bracket_depth == 0 => {
                    // Found a period at depth 0 - split here
                    let entry = self.buffer.trim().to_string();
                    if !entry.is_empty() {
                        self.entries.push(entry);
                    }
                    self.buffer.clear();
                }
                _ => {
                    self.buffer.push(ch);
                }
            }
        }
    }

    fn finish(self) -> Result<ListSection, ParseError> {
        if !self.buffer.trim().is_empty() {
            return Err(ParseError::new(
                0,
                0,
                format!(
                    "unterminated entry in list `{}`: {}",
                    self.name, self.buffer
                ),
            ));
        }
        Ok(ListSection {
            name: self.name,
            kind: self.kind,
            raw_entries: self.entries,
        })
    }
}

/// Parser entry point.
#[derive(Clone, Debug, Default)]
pub struct Parser;

impl Parser {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn parse_str(&self, source: &str) -> Result<OtterFile, ParseError> {
        let mut file = OtterFile::default();
        let mut current: Option<ListBuilder> = None;
        let mut command_buffer: Option<String> = None;
        let mut proof_buffer: Option<(String, i32)> = None;  // (buffer, paren_depth)

        for (line_idx, raw_line) in source.lines().enumerate() {
            let line = strip_comment(raw_line).trim();
            if line.is_empty() {
                continue;
            }

            // If we're inside a list, handle list content
            if let Some(builder) = current.as_mut() {
                if is_end_of_list(line) {
                    let builder = current.take().unwrap();
                    file.lists.push(builder.finish()?);
                } else {
                    builder.push_line(line);
                }
                continue;
            }

            // If we're buffering a proof object, continue buffering
            if let Some((ref mut buffer, ref mut depth)) = proof_buffer {
                buffer.push(' ');
                buffer.push_str(line);
                // Update parenthesis depth
                for ch in line.chars() {
                    match ch {
                        '(' => *depth += 1,
                        ')' => *depth -= 1,
                        _ => {}
                    }
                }
                // Check if proof object is complete
                if *depth == 0 {
                    process_command(&mut file, OtterCommand::ProofObject(buffer.clone()));
                    proof_buffer = None;
                }
                continue;
            }

            // If we're buffering a multi-line command, continue buffering
            if let Some(ref mut buffer) = command_buffer {
                buffer.push(' ');
                buffer.push_str(line);
                if line.ends_with('.') {
                    // Command complete, parse it
                    let cmd_text = buffer.trim_end_matches('.').trim();
                    let command = parse_command(cmd_text);
                    process_command(&mut file, command);
                    command_buffer = None;
                }
                continue;
            }

            // Check for list header
            if let Some(builder) = parse_list_header(line) {
                current = Some(builder);
                continue;
            }

            // Check for stray end_of_list
            if is_end_of_list(line) {
                return Err(ParseError::new(
                    line_idx,
                    0,
                    "encountered end_of_list without a preceding list",
                ));
            }

            // Check if this is a proof object (Ivy format)
            if line.starts_with("((") {
                let mut depth = 0i32;
                for ch in line.chars() {
                    match ch {
                        '(' => depth += 1,
                        ')' => depth -= 1,
                        _ => {}
                    }
                }
                if depth == 0 {
                    // Complete proof object on one line
                    process_command(&mut file, OtterCommand::ProofObject(line.to_string()));
                } else {
                    // Multi-line proof object
                    proof_buffer = Some((line.to_string(), depth));
                }
                continue;
            }

            // Check if this is a complete or partial command
            if line.ends_with('.') {
                let command = parse_command(line.trim_end_matches('.').trim());
                process_command(&mut file, command);
                continue;
            }

            // This could be the start of a multi-line command
            command_buffer = Some(line.to_string());
        }

        if let Some(builder) = current {
            return Err(ParseError::new(
                source.lines().count().saturating_sub(1),
                0,
                format!("unterminated list `{}`", builder.name),
            ));
        }

        if command_buffer.is_some() {
            return Err(ParseError::new(
                source.lines().count().saturating_sub(1),
                0,
                "unterminated command (missing '.')".to_string(),
            ));
        }

        if proof_buffer.is_some() {
            return Err(ParseError::new(
                source.lines().count().saturating_sub(1),
                0,
                "unterminated proof object (unbalanced parentheses)".to_string(),
            ));
        }

        Ok(file)
    }
}

fn parse_clause(
    entry: &str,
    symbols: &SymbolTable,
    operators: &crate::parser::OperatorTable,
) -> Result<Clause, ParseError> {
    let entry = entry.trim();
    if entry.is_empty() {
        return Ok(Clause::new(vec![]));
    }

    let (core, mut attributes) = split_clause_annotations(entry)?;

    let mut literals = Vec::new();

    for literal_text in split_literals(&core) {
        let (literal, mut literal_attrs) =
            parse_literal(literal_text, symbols, operators)?;
        literals.push(literal);
        attributes.append(&mut literal_attrs);
    }

    let mut clause = Clause::new(literals);
    for attribute in attributes {
        clause.add_attribute(attribute);
    }
    Ok(clause)
}

/// Parse a literal from text (public for formula parser)
pub(crate) fn parse_literal_internal(
    text: &str,
    symbols: &SymbolTable,
) -> Result<(Literal, Vec<ClauseAttribute>), ParseError> {
    // Formula parser doesn't have operators yet, so use default table
    let operators = crate::parser::OperatorTable::new();
    parse_literal(text, symbols, &operators)
}

fn parse_literal(
    text: &str,
    symbols: &SymbolTable,
    operators: &crate::parser::OperatorTable,
) -> Result<(Literal, Vec<ClauseAttribute>), ParseError> {
    let mut trimmed = text.trim();
    let mut attributes = Vec::new();

    if let Some((core, attr_text)) = split_literal_attributes(trimmed)? {
        trimmed = core.trim();
        attributes = parse_attribute_list(attr_text)?;
    }

    let mut sign = true;
    if trimmed.starts_with('-') || trimmed.starts_with('~') {
        sign = false;
        trimmed = trimmed.trim_start_matches(|c| c == '-' || c == '~').trim();
    }

    // Check if the entire literal is wrapped in parentheses
    // e.g., "(x = y)" should be parsed as "x = y"
    if trimmed.starts_with('(') && trimmed.ends_with(')') {
        if let Some(close_idx) = matching_paren_index(trimmed, 0) {
            if close_idx == trimmed.len() - 1 {
                // The parentheses wrap the entire literal, so strip them
                let inner = &trimmed[1..trimmed.len() - 1];
                let (inner_lit, inner_attrs) = parse_literal(inner, symbols, operators)?;
                // Combine sign: if outer is negative and inner is negative, result is positive
                let combined_sign = if sign { inner_lit.sign } else { !inner_lit.sign };
                let mut combined_attrs = attributes;
                combined_attrs.extend(inner_attrs);
                return Ok((Literal::new(combined_sign, inner_lit.atom.clone()), combined_attrs));
            }
        }
    }

    // Check for != first (special case for disequality)
    if let Some(idx) = trimmed.find("!=") {
        let (lhs, rhs) = trimmed.split_at(idx);
        let rhs = &rhs[2..];
        let eq_symbol = intern_equality(symbols);
        let left_term = parse_term(lhs, symbols, operators)?;
        let right_term = parse_term(rhs, symbols, operators)?;
        let term = Term::application(eq_symbol, vec![left_term, right_term]);
        return Ok((Literal::new(false, term), attributes));
    }

    // Check for = (equality), but only if it's not part of <= or >=
    // We need to find '=' that's not preceded by '<' or '>' at the same position
    if let Some(idx) = find_equality_position(trimmed) {
        let (lhs, rhs) = trimmed.split_at(idx);
        let rhs = &rhs[1..];
        let eq_symbol = intern_equality(symbols);
        let left_term = parse_term(lhs, symbols, operators)?;
        let right_term = parse_term(rhs, symbols, operators)?;
        let term = Term::application(eq_symbol, vec![left_term, right_term]);
        return Ok((Literal::new(sign, term), attributes));
    }

    if let Some(open_paren) = trimmed.find('(') {
        let close_paren = matching_paren_index(trimmed, open_paren)
            .ok_or_else(|| ParseError::new(0, 0, "expected ')' in literal"))?;
        let name = &trimmed[..open_paren];
        let args_text = &trimmed[open_paren + 1..close_paren];
        let args = split_arguments(args_text)
            .into_iter()
            .map(|arg| parse_term(arg, symbols, operators))
            .collect::<Result<Vec<_>, _>>()?;
        let symbol_id = symbols.intern(
            name.trim(),
            args.len() as u8,
            SymbolKind::Predicate,
        );
        let term = Term::application(symbol_id, args);
        Ok((Literal::new(sign, term), attributes))
    } else {
        // Check for infix operators (==, <, <=, >, >=) used as predicates
        if let Some((left, op, right)) = find_infix_operator(trimmed, operators) {
            let left_term = parse_term(left, symbols, operators)?;
            let right_term = parse_term(right, symbols, operators)?;
            let symbol_id = symbols.intern(op, 2, SymbolKind::Predicate);
            let term = Term::application(symbol_id, vec![left_term, right_term]);
            return Ok((Literal::new(sign, term), attributes));
        }

        let symbol_id = symbols.intern(trimmed, 0, SymbolKind::Predicate);
        let term = Term::application(symbol_id, vec![]);
        Ok((Literal::new(sign, term), attributes))
    }
}

/// Check if a name is a variable in Otter's default mode.
/// In Otter, variables are names starting with 'u', 'v', 'w', 'x', 'y', or 'z'.
/// Examples: x, y, z, x1, y2, u, v, w are all variables.
/// Constants start with other letters (a-t) or are multi-char names like "abc".
fn is_otter_variable(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    let first_char = name.chars().next().unwrap();
    // In Otter default mode, variables start with u-z
    first_char >= 'u' && first_char <= 'z'
}

/// Compute a unique variable ID from a variable name.
/// Maps single-char variables directly: x=0, y=1, z=2, u=3, v=4, w=5
/// Multi-char variables get IDs starting from 6.
fn compute_variable_id(name: &str) -> u16 {
    if name.len() == 1 {
        let c = name.chars().next().unwrap();
        // Map x,y,z,u,v,w to 0-5
        match c {
            'x' => 0,
            'y' => 1,
            'z' => 2,
            'u' => 3,
            'v' => 4,
            'w' => 5,
            _ => 0, // Shouldn't happen if is_otter_variable is true
        }
    } else {
        // For multi-char variables (x1, x2, etc.), compute a hash-based ID
        // Start from 6 to avoid conflict with single-char vars
        let mut id: u16 = 6;
        for (i, c) in name.chars().enumerate() {
            id = id.wrapping_add((c as u16).wrapping_mul((i as u16).wrapping_add(1)));
        }
        id
    }
}

fn parse_term(
    text: &str,
    symbols: &SymbolTable,
    operators: &crate::parser::OperatorTable,
) -> Result<Term, ParseError> {
    let text = text.trim();
    if text.is_empty() {
        return Err(ParseError::new(0, 0, "empty term"));
    }

    if text.starts_with('$') {
        let id = symbols.intern(text, 0, SymbolKind::Evaluator);
        return Ok(Term::application(id, vec![]));
    }

    // In Otter (default mode), variables are names starting with u-z.
    // E.g., x, y, z, x1, y2, u, v, w are all variables.
    // In Prolog style (set(prolog_style_variables)), variables start with A-Z or _.
    // Here we implement the default Otter convention.
    if is_otter_variable(text) {
        // Map the first character to a variable ID
        // We use the full variable name hash for multi-character names
        let var_id = compute_variable_id(text);
        return Ok(Term::variable(VariableId::new(var_id)));
    }

    // Check for Prolog-style lists: [], [a,b,c], [H|T]
    if text.starts_with('[') && text.ends_with(']') {
        return parse_list(text, symbols, operators);
    }

    // Check for prefix operators (e.g., ~x, ~(A | B))
    // Must be checked before function application to handle prefix ops correctly
    if let Some((op, operand)) = find_prefix_operator(text, operators) {
        let operand_term = parse_term(operand, symbols, operators)?;
        let symbol_id = symbols.intern(op, 1, SymbolKind::Function);
        return Ok(Term::application(symbol_id, vec![operand_term]));
    }

    if let Some(open_paren) = text.find('(') {
        let close_paren = matching_paren_index(text, open_paren)
            .ok_or_else(|| ParseError::new(0, 0, "unterminated term"))?;
        let name = &text[..open_paren];
        let args_text = &text[open_paren + 1..close_paren];
        let args = split_arguments(args_text)
            .into_iter()
            .map(|arg| parse_term(arg, symbols, operators))
            .collect::<Result<Vec<_>, _>>()?;
        let symbol_id = symbols.intern(
            name.trim(),
            args.len() as u8,
            SymbolKind::Function,
        );
        return Ok(Term::application(symbol_id, args));
    }

    // Check for infix operators using the operator table
    if let Some((left, op, right)) = find_infix_operator(text, operators) {
        let left_term = parse_term(left, symbols, operators)?;
        let right_term = parse_term(right, symbols, operators)?;
        let symbol_id = symbols.intern(op, 2, SymbolKind::Function);
        return Ok(Term::application(symbol_id, vec![left_term, right_term]));
    }

    // Check for postfix operators (e.g., x^, a!)
    if let Some((operand, op)) = find_postfix_operator(text, operators) {
        let operand_term = parse_term(operand, symbols, operators)?;
        let symbol_id = symbols.intern(op, 1, SymbolKind::Function);
        return Ok(Term::application(symbol_id, vec![operand_term]));
    }

    if text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        let symbol_id = symbols.intern(text, 0, SymbolKind::Constant);
        return Ok(Term::application(symbol_id, vec![]));
    }

    Err(ParseError::new(0, 0, format!("unsupported token '{}'", text)))
}

/// Find an infix operator at the top level of a term.
/// Returns (left_operand, operator, right_operand) if found.
/// Uses the operator table to determine which operators to search for
/// and respects their precedence and associativity.
fn find_infix_operator<'a>(
    text: &'a str,
    operators: &crate::parser::OperatorTable,
) -> Option<(&'a str, &'a str, &'a str)> {
    // Get all infix operators sorted by precedence (highest first), then by length (longest first)
    // Higher precedence binds less tightly in Otter, so we check them first
    let infix_ops = operators.infix_operators();
    if infix_ops.is_empty() {
        return None;
    }

    let text_bytes = text.as_bytes();

    // Scan for operators by precedence (highest precedence first = binds less tightly)
    // This ensures we split at the lowest-binding operator
    for op_info in &infix_ops {
        let op_str = &op_info.symbol;
        let mut depth = 0;

        // For left-associative operators, scan right-to-left
        // For right-associative operators, scan left-to-right
        let scan_indices: Vec<usize> = if op_info.fixity.is_left_assoc() {
            (0..text.len()).rev().collect()
        } else {
            (0..text.len()).collect()
        };

        for i in scan_indices {
            let ch = text_bytes[i] as char;

            // Track parenthesis depth
            if ch == ')' {
                depth += 1;
            } else if ch == '(' {
                depth -= 1;
            }

            // Only consider operators at depth 0 (not inside parentheses)
            if depth == 0 && text[i..].starts_with(op_str) {
                let left = &text[..i];
                let right = &text[i + op_str.len()..];

                // Make sure we're not at the start (unary operator case)
                if !left.is_empty() && !right.is_empty() {
                    // Check if any longer operator at the same precedence could match at this position
                    // This prevents "=" from matching when "==" is actually present
                    let mut is_longest_match = true;
                    for other_op in &infix_ops {
                        if other_op.precedence == op_info.precedence
                            && other_op.symbol.len() > op_str.len()
                            && text[i..].starts_with(&other_op.symbol) {
                            is_longest_match = false;
                            break;
                        }
                    }

                    if !is_longest_match {
                        continue; // Skip this match, a longer operator will match
                    }

                    // This is the longest operator at this position and precedence
                    let op = &text[i..i + op_str.len()];
                    return Some((left.trim(), op, right.trim()));
                }
            }
        }
    }

    None
}

/// Parse a Prolog-style list into nested cons applications
/// [] -> $nil
/// [a,b,c] -> $cons(a, $cons(b, $cons(c, $nil)))
/// [H|T] -> $cons(H, T)
fn parse_list(
    text: &str,
    symbols: &SymbolTable,
    operators: &crate::parser::OperatorTable,
) -> Result<Term, ParseError> {
    let inner = text[1..text.len() - 1].trim();

    // Empty list: []
    if inner.is_empty() {
        let nil_id = symbols.intern("$nil", 0, SymbolKind::Constant);
        return Ok(Term::application(nil_id, vec![]));
    }

    // Check for cons notation: [H|T]
    if let Some(pipe_pos) = find_top_level_char(inner, '|') {
        let head_str = inner[..pipe_pos].trim();
        let tail_str = inner[pipe_pos + 1..].trim();

        let head = parse_term(head_str, symbols, operators)?;
        let tail = parse_term(tail_str, symbols, operators)?;

        let cons_id = symbols.intern("$cons", 2, SymbolKind::Function);
        return Ok(Term::application(cons_id, vec![head, tail]));
    }

    // Regular list: [a, b, c]
    let elements = split_arguments(inner);
    let mut result_term = {
        let nil_id = symbols.intern("$nil", 0, SymbolKind::Constant);
        Term::application(nil_id, vec![])
    };

    // Build the list from right to left
    for elem_str in elements.iter().rev() {
        let elem = parse_term(elem_str, symbols, operators)?;
        let cons_id = symbols.intern("$cons", 2, SymbolKind::Function);
        result_term = Term::application(cons_id, vec![elem, result_term]);
    }

    Ok(result_term)
}

/// Find a prefix operator at the start of a term.
/// Returns (operator, operand) if found.
/// For example, "~x" returns ("~", "x"), and "~(A | B)" returns ("~", "(A | B)")
fn find_prefix_operator<'a>(
    text: &'a str,
    operators: &crate::parser::OperatorTable,
) -> Option<(&'a str, &'a str)> {
    // Get all prefix operators
    let prefix_ops = operators.prefix_operators();
    if prefix_ops.is_empty() {
        return None;
    }

    // Try to match each prefix operator at the beginning of the text
    for op_info in prefix_ops {
        let op_str = &op_info.symbol;
        if text.starts_with(op_str.as_str()) {
            let op_len = op_str.len();
            let operand = text[op_len..].trim();
            if !operand.is_empty() {
                // Return substring from original text with proper lifetime
                let op_from_text = &text[..op_len];
                return Some((op_from_text, operand));
            }
        }
    }

    None
}

/// Find a postfix operator at the end of a term.
/// Returns (operand, operator) if found.
/// For example, "x^" returns ("x", "^"), and "(a + b)!" returns ("(a + b)", "!")
fn find_postfix_operator<'a>(
    text: &'a str,
    operators: &crate::parser::OperatorTable,
) -> Option<(&'a str, &'a str)> {
    // Get all postfix operators
    let postfix_ops = operators.postfix_operators();
    if postfix_ops.is_empty() {
        return None;
    }

    // Try to match each postfix operator at the end of the text
    for op_info in postfix_ops {
        let op_str = &op_info.symbol;
        if text.ends_with(op_str.as_str()) {
            let op_len = op_str.len();
            let operand = text[..text.len() - op_len].trim();
            if !operand.is_empty() {
                // Return substring from original text with proper lifetime
                let op_from_text = &text[text.len() - op_len..];
                return Some((operand, op_from_text));
            }
        }
    }

    None
}

fn split_literals(entry: &str) -> Vec<&str> {
    split_top_level(entry, |c| c == ',' || c == '|')
}

fn split_arguments(args: &str) -> Vec<&str> {
    split_top_level(args, |c| c == ',')
}

fn split_literal_attributes(
    text: &str,
) -> Result<Option<(&str, &str)>, ParseError> {
    if let Some(start) = find_top_level_char(text, '[') {
        let end = matching_bracket_index(text, start).ok_or_else(|| {
            ParseError::new(0, 0, "unterminated attribute list")
        })?;
        let core = &text[..start];
        let attrs = &text[start + 1..end];
        if text[end + 1..].trim().is_empty() {
            Ok(Some((core, attrs)))
        } else {
            Err(ParseError::new(
                0,
                0,
                "unexpected content after attribute list",
            ))
        }
    } else {
        Ok(None)
    }
}

fn parse_attribute_list(
    text: &str,
) -> Result<Vec<ClauseAttribute>, ParseError> {
    let mut attrs = Vec::new();
    for part in split_top_level(text, |c| c == ',') {
        let trimmed = part.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Some(eq) = find_top_level_char(trimmed, '=') {
            let name = trimmed[..eq].trim();
            let value_str = trimmed[eq + 1..].trim().trim_matches('"');
            let value = if let Ok(int_val) = value_str.parse::<i64>() {
                ClauseAttributeValue::Integer(int_val)
            } else if let Ok(float_val) = value_str.parse::<f64>() {
                ClauseAttributeValue::Float(float_val)
            } else if value_str.eq_ignore_ascii_case("true") {
                ClauseAttributeValue::Flag(true)
            } else if value_str.eq_ignore_ascii_case("false") {
                ClauseAttributeValue::Flag(false)
            } else {
                ClauseAttributeValue::Text(value_str.to_string())
            };
            attrs.push(ClauseAttribute::new(name, value));
        } else {
            attrs.push(ClauseAttribute::new(
                trimmed,
                ClauseAttributeValue::Flag(true),
            ));
        }
    }
    Ok(attrs)
}

/// Process a command and update the file's operator table if it's an op() command
fn process_command(file: &mut OtterFile, command: OtterCommand) {
    // If it's an op() command, update the operator table
    if let OtterCommand::Op { precedence, ref fixity, ref symbol } = command {
        if let Some(fixity_enum) = crate::parser::Fixity::from_str(fixity) {
            file.operators.add_operator(symbol, precedence, fixity_enum);
        }
    }

    // If it's a make_evaluable() command, extract and register the operator
    // e.g., make_evaluable(_<=_, $LE(_,_)) -> register "<=" as an infix operator
    if let OtterCommand::MakeEvaluable { ref operator, .. } = command {
        // Extract the operator symbol from _op_ format
        // Common patterns: _<=_, _+_, _>_, etc.
        if operator.starts_with('_') && operator.ends_with('_') && operator.len() > 2 {
            let op_symbol = &operator[1..operator.len() - 1];
            // Register as infix operator with default precedence
            // Common comparison/arithmetic operators
            let precedence = match op_symbol {
                "=" | "!=" | "<" | ">" | "<=" | ">=" => 700,
                "+" | "-" => 500,
                "*" | "/" | "%" => 400,
                _ => 600, // default precedence
            };
            file.operators.add_operator(op_symbol, precedence, crate::parser::Fixity::Infix);
        }
    }

    file.commands.push(command);
}

/// Find the position of '=' for equality checking, but skip it if it's part of <= or >=
/// Returns the index of a standalone '=' character at the top level (not in parens)
fn find_equality_position(text: &str) -> Option<usize> {
    let mut depth = 0;
    let bytes = text.as_bytes();

    for i in 0..text.len() {
        match bytes[i] as char {
            '(' => depth += 1,
            ')' => depth -= 1,
            '=' if depth == 0 => {
                // Check if this is part of !=, <=, >=, or ==
                let preceded_by_special = i > 0 && matches!(bytes[i - 1] as char, '!' | '<' | '>' | '=');
                let followed_by_equals = i + 1 < text.len() && bytes[i + 1] as char == '=';
                if !preceded_by_special && !followed_by_equals {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

fn parse_command(text: &str) -> OtterCommand {
    let lower = text.to_ascii_lowercase();
    if lower.starts_with("set(") && text.ends_with(')') {
        let inner = &text[4..text.len() - 1];
        return OtterCommand::Set(inner.trim().to_string());
    }
    if lower.starts_with("clear(") && text.ends_with(')') {
        let inner = &text[6..text.len() - 1];
        return OtterCommand::Clear(inner.trim().to_string());
    }
    if lower.starts_with("assign(") && text.ends_with(')') {
        let inner = &text[7..text.len() - 1];
        if let Some(comma) = find_top_level_char(inner, ',') {
            let name = inner[..comma].trim();
            let value = inner[comma + 1..].trim();
            return OtterCommand::Assign {
                name: name.to_string(),
                value: value.to_string(),
            };
        }
    }
    if lower.starts_with("op(") && text.ends_with(')') {
        // Parse op(precedence, fixity, symbol)
        let inner = &text[3..text.len() - 1];
        let parts: Vec<&str> = split_arguments(inner);
        if parts.len() == 3 {
            if let Ok(precedence) = parts[0].trim().parse::<u16>() {
                let fixity = parts[1].trim().to_string();
                let symbol = parts[2].trim().to_string();
                return OtterCommand::Op {
                    precedence,
                    fixity,
                    symbol,
                };
            }
        }
    }
    if lower.starts_with("lex(") && text.ends_with(')') {
        // Parse lex([sym1, sym2, ...])
        let inner = &text[4..text.len() - 1].trim();
        if inner.starts_with('[') && inner.ends_with(']') {
            let list_content = &inner[1..inner.len() - 1];
            let symbols: Vec<String> = split_arguments(list_content)
                .into_iter()
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            return OtterCommand::Lex { symbols };
        }
    }
    if lower.starts_with("make_evaluable(") && text.ends_with(')') {
        // Parse make_evaluable(_+_, $SUM(_,_))
        let inner = &text[15..text.len() - 1];
        if let Some(comma) = find_top_level_char(inner, ',') {
            let operator = inner[..comma].trim().to_string();
            let evaluator = inner[comma + 1..].trim().to_string();
            return OtterCommand::MakeEvaluable {
                operator,
                evaluator,
            };
        }
    }
    OtterCommand::Generic(text.to_string())
}

fn parse_list_header(line: &str) -> Option<ListBuilder> {
    if !line.ends_with('.') {
        return None;
    }
    let without_dot = line[..line.len() - 1].trim();
    let open_paren = without_dot.find('(')?;
    let close_paren = without_dot.rfind(')')?;
    if close_paren <= open_paren {
        return None;
    }
    let keyword = without_dot[..open_paren].trim().to_ascii_lowercase();
    let name = without_dot[open_paren + 1..close_paren].trim().to_string();

    // Validate that name is a simple identifier (not a complex expression like [])
    // List section names should be alphanumeric identifiers, not Prolog list syntax
    if name.is_empty() || name.contains(|c: char| !c.is_alphanumeric() && c != '_') {
        return None;
    }

    let kind = match keyword.as_str() {
        "list" => ListKind::Clause,
        "formula_list" => ListKind::Formula,
        "weight_list" => ListKind::Weight,
        _ => return None,
    };
    Some(ListBuilder::new(name, kind))
}

fn strip_comment(line: &str) -> &str {
    if let Some(idx) = line.find('%') { &line[..idx] } else { line }
}

fn split_top_level<'a, F>(text: &'a str, is_sep: F) -> Vec<&'a str>
where
    F: Fn(char) -> bool,
{
    let mut parts = Vec::new();
    let mut depth_paren = 0i32;
    let mut depth_bracket = 0i32;
    let mut start = 0usize;
    for (idx, ch) in text.char_indices() {
        match ch {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -= 1,
            _ if depth_paren == 0 && depth_bracket == 0 && is_sep(ch) => {
                if start <= idx {
                    parts.push(text[start..idx].trim());
                }
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }
    if start < text.len() {
        parts.push(text[start..].trim());
    }
    parts.into_iter().filter(|part| !part.is_empty()).collect()
}

fn matching_paren_index(text: &str, open_index: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (idx, ch) in text.char_indices().skip(open_index) {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

fn matching_bracket_index(text: &str, open_index: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (idx, ch) in text.char_indices().skip(open_index) {
        match ch {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

fn find_top_level_char(text: &str, target: char) -> Option<usize> {
    let mut depth_paren = 0i32;
    let mut depth_bracket = 0i32;
    for (idx, ch) in text.char_indices() {
        match ch {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -= 1,
            _ if depth_paren == 0 && depth_bracket == 0 && ch == target => {
                return Some(idx);
            }
            _ => {}
        }
    }
    None
}

fn intern_equality(symbols: &SymbolTable) -> SymbolId {
    symbols.intern("=", 2, SymbolKind::Predicate)
}

fn split_clause_annotations(
    entry: &str,
) -> Result<(String, Vec<ClauseAttribute>), ParseError> {
    let mut body = entry.trim().to_string();
    let mut attributes = Vec::new();

    loop {
        let Some(idx) = find_last_top_level_char(&body, '#') else {
            break;
        };
        let annotation_text = body[idx + 1..].trim();
        if annotation_text.is_empty() {
            break;
        }
        match parse_clause_annotation(annotation_text)? {
            Some(attribute) => {
                attributes.push(attribute);
                body = body[..idx].trim_end().to_string();
            }
            None => break,
        }
    }

    attributes.reverse();
    Ok((body, attributes))
}

fn parse_clause_annotation(
    text: &str,
) -> Result<Option<ClauseAttribute>, ParseError> {
    let trimmed = text.trim();
    if trimmed.is_empty() {
        return Ok(None);
    }
    let open = match trimmed.find('(') {
        Some(index) if index > 0 => index,
        _ => return Ok(None),
    };
    let close = matching_paren_index(trimmed, open)
        .ok_or_else(|| ParseError::new(0, 0, "unterminated annotation"))?;
    if close != trimmed.len() - 1 {
        return Ok(None);
    }
    let name = trimmed[..open].trim();
    if name.is_empty() {
        return Ok(None);
    }
    let value_text = trimmed[open + 1..close].trim();
    let value = if value_text.is_empty() {
        ClauseAttributeValue::Flag(true)
    } else if let Ok(int_val) = value_text.parse::<i64>() {
        ClauseAttributeValue::Integer(int_val)
    } else if let Ok(float_val) = value_text.parse::<f64>() {
        ClauseAttributeValue::Float(float_val)
    } else {
        ClauseAttributeValue::Text(value_text.to_string())
    };
    Ok(Some(ClauseAttribute::new(name, value)))
}

fn find_last_top_level_char(text: &str, target: char) -> Option<usize> {
    let mut depth_paren = 0i32;
    let mut depth_bracket = 0i32;
    let mut result = None;
    for (idx, ch) in text.char_indices() {
        match ch {
            '(' => depth_paren += 1,
            ')' => depth_paren -= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -= 1,
            _ if depth_paren == 0 && depth_bracket == 0 && ch == target => {
                result = Some(idx)
            }
            _ => {}
        }
    }
    result
}

/// Check if a line represents an end_of_list terminator.
/// Handles variations like "end_of_list.", "end_of_list .", "END_OF_LIST.", etc.
fn is_end_of_list(line: &str) -> bool {
    let trimmed = line.trim();
    if !trimmed.ends_with('.') {
        return false;
    }
    let without_period = trimmed[..trimmed.len() - 1].trim();
    without_period.eq_ignore_ascii_case("end_of_list")
}

/// Parser error information.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub column: usize,
    pub message: String,
}

impl ParseError {
    fn new(line: usize, column: usize, message: impl Into<String>) -> Self {
        Self { line, column, message: message.into() }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "parse error at {}:{}: {}",
            self.line + 1,
            self.column + 1,
            self.message
        )
    }
}

impl std::error::Error for ParseError {}

#[cfg(test)]
mod tests {
    use super::{ListKind, OtterCommand, Parser};
    use crate::data::{ClauseArena, SymbolTable};

    #[test]
    fn parse_simple_list() {
        let parser = Parser::new();
        let input = r#"
            set(auto).
            list(usable).
            P(a).
            -Q(A).
            end_of_list.
        "#;
        let file = parser.parse_str(input).expect("parse usable list");
        assert_eq!(file.commands.len(), 1);
        assert!(matches!(file.commands[0], OtterCommand::Set(_)));
        assert_eq!(file.lists.len(), 1);
        let section = &file.lists[0];
        assert_eq!(section.kind, ListKind::Clause);
        let mut arena = ClauseArena::new();
        let symbols = SymbolTable::new();
        let operators = crate::parser::OperatorTable::new();
        let list =
            section.to_clause_list(&mut arena, &symbols, &operators).expect("clause list");
        assert_eq!(list.len(), 2);
    }

    #[test]
    fn generic_command_is_parsed() {
        let parser = Parser::new();
        let input = "P(a).";
        let file = parser.parse_str(input).expect("generic command");
        assert_eq!(file.commands.len(), 1);
    }

    #[test]
    fn op_command_is_parsed() {
        let parser = Parser::new();
        let input = "op(450, xfy, &).";
        let file = parser.parse_str(input).expect("op command");
        assert_eq!(file.commands.len(), 1);
        match &file.commands[0] {
            OtterCommand::Op { precedence, fixity, symbol } => {
                assert_eq!(*precedence, 450);
                assert_eq!(fixity, "xfy");
                assert_eq!(symbol, "&");
            }
            _ => panic!("Expected Op command"),
        }
        // Verify operator was added to table
        assert!(file.operators.is_operator("&"));
        let ops = file.operators.get_operators("&").unwrap();
        assert_eq!(ops[0].precedence, 450);
    }

    #[test]
    fn reject_unterminated_list() {
        let parser = Parser::new();
        let input = "list(usable).";
        let err = parser.parse_str(input).expect_err("unterminated");
        assert!(err.message.contains("unterminated list"));
    }

    #[test]
    fn parse_clause_arguments() {
        let parser = Parser::new();
        let input = "list(sos).\n P(A,b,$sum).\n end_of_list.";
        let file = parser.parse_str(input).expect("parse");
        let section = &file.lists[0];
        let mut arena = ClauseArena::new();
        let symbols = SymbolTable::new();
        let operators = crate::parser::OperatorTable::new();
        let list =
            section.to_clause_list(&mut arena, &symbols, &operators).expect("clause list");
        assert_eq!(list.len(), 1);
    }

    #[test]
    fn parse_multi_literal_clause() {
        let parser = Parser::new();
        let input = "list(sos).\n P(a) | -Q(b).\n end_of_list.";
        let file = parser.parse_str(input).expect("parse");
        let section = &file.lists[0];
        let mut arena = ClauseArena::new();
        let symbols = SymbolTable::new();
        let operators = crate::parser::OperatorTable::new();
        section.to_clause_list(&mut arena, &symbols, &operators).expect("clause list");
        let clause = arena.iter().next().expect("clause present");
        assert_eq!(clause.literals.len(), 2);
        assert!(clause.literals[0].sign);
        assert!(!clause.literals[1].sign);
    }

    #[test]
    fn parse_equality_literal() {
        let parser = Parser::new();
        let input =
            "list(usable).\n f(x,y) = f(y,x).\n h(a,b) != e.\n end_of_list.";
        let file = parser.parse_str(input).expect("parse");
        let section = &file.lists[0];
        let mut arena = ClauseArena::new();
        let symbols = SymbolTable::new();
        let operators = crate::parser::OperatorTable::new();
        section.to_clause_list(&mut arena, &symbols, &operators).expect("clause list");
        let mut iter = arena.iter();
        let clause1 = iter.next().expect("first clause");
        assert!(clause1.literals[0].sign);
        let clause2 = iter.next().expect("second clause");
        assert!(!clause2.literals[0].sign);
    }

    #[test]
    fn parse_clause_with_label_annotation() {
        let parser = Parser::new();
        let input = "list(hints).\n p(x) = y # label(step_1).\n end_of_list.";
        let file = parser.parse_str(input).expect("parse");
        let section = &file.lists[0];
        let mut arena = ClauseArena::new();
        let symbols = SymbolTable::new();
        let operators = crate::parser::OperatorTable::new();
        section.to_clause_list(&mut arena, &symbols, &operators).expect("clause list");
        let clause = arena.iter().next().expect("clause present");
        let has_label =
            clause.attributes.iter().any(|attr| attr.name == "label");
        let has_list_attr = clause.attributes.iter().any(|attr| {
            attr.name == "list"
                && attr.value
                    == crate::data::ClauseAttributeValue::Text("hints".into())
        });
        assert!(has_label, "expected label attribute");
        assert!(has_list_attr, "expected list attribute");
    }

    #[test]
    fn parse_weight_list() {
        let parser = Parser::new();
        let input = r#"
            weight_list(pick).
            weight(f(x), -3).
            weight(g($(1)), 10).
            end_of_list.
        "#;
        let file = parser.parse_str(input).expect("parse weight list");
        let section = &file.lists[0];
        let weights = section.weight_entries().expect("weights");
        assert_eq!(weights.len(), 2);
        assert_eq!(weights[0].weight, -3);
    }
}
