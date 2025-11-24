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
            let mut clause = parse_clause(entry, symbols)?;
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
            let clauses = formula.to_clauses(symbols)
                .map_err(|e| ParseError::new(0, 0, format!("Formula conversion failed: {}", e)))?;

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
        if !self.buffer.is_empty() {
            self.buffer.push(' ');
        }
        self.buffer.push_str(trimmed);
        for ch in trimmed.chars() {
            match ch {
                '(' => self.paren_depth += 1,
                ')' => self.paren_depth -= 1,
                '[' => self.bracket_depth += 1,
                ']' => self.bracket_depth -= 1,
                _ => {}
            }
        }
        if self.paren_depth == 0
            && self.bracket_depth == 0
            && self.buffer.ends_with('.')
        {
            let entry = self.buffer.trim_end_matches('.').trim().to_string();
            if !entry.is_empty() {
                self.entries.push(entry);
            }
            self.buffer.clear();
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
) -> Result<Clause, ParseError> {
    let entry = entry.trim();
    if entry.is_empty() {
        return Ok(Clause::new(vec![]));
    }

    let (core, mut attributes) = split_clause_annotations(entry)?;

    let mut literals = Vec::new();

    for literal_text in split_literals(&core) {
        let (literal, mut literal_attrs) =
            parse_literal(literal_text, symbols)?;
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
    parse_literal(text, symbols)
}

fn parse_literal(
    text: &str,
    symbols: &SymbolTable,
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

    if let Some(idx) = trimmed.find("!=") {
        let (lhs, rhs) = trimmed.split_at(idx);
        let rhs = &rhs[2..];
        let eq_symbol = intern_equality(symbols);
        let left_term = parse_term(lhs, symbols)?;
        let right_term = parse_term(rhs, symbols)?;
        let term = Term::application(eq_symbol, vec![left_term, right_term]);
        return Ok((Literal::new(false, term), attributes));
    }

    if let Some(idx) = find_top_level_char(trimmed, '=') {
        let (lhs, rhs) = trimmed.split_at(idx);
        let rhs = &rhs[1..];
        let eq_symbol = intern_equality(symbols);
        let left_term = parse_term(lhs, symbols)?;
        let right_term = parse_term(rhs, symbols)?;
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
            .map(|arg| parse_term(arg, symbols))
            .collect::<Result<Vec<_>, _>>()?;
        let symbol_id = symbols.intern(
            name.trim(),
            args.len() as u8,
            SymbolKind::Predicate,
        );
        let term = Term::application(symbol_id, args);
        Ok((Literal::new(sign, term), attributes))
    } else {
        let symbol_id = symbols.intern(trimmed, 0, SymbolKind::Predicate);
        let term = Term::application(symbol_id, vec![]);
        Ok((Literal::new(sign, term), attributes))
    }
}

fn parse_term(text: &str, symbols: &SymbolTable) -> Result<Term, ParseError> {
    let text = text.trim();
    if text.is_empty() {
        return Err(ParseError::new(0, 0, "empty term"));
    }

    if text.starts_with('$') {
        let id = symbols.intern(text, 0, SymbolKind::Evaluator);
        return Ok(Term::application(id, vec![]));
    }

    // In Otter, variables are uppercase letters (A, B, X, Y, Z, etc.)
    if text.chars().all(|c| c.is_ascii_uppercase()) {
        let first_char = text.bytes().next().unwrap_or(b'A');
        return Ok(Term::variable(VariableId::new((first_char - b'A') as u16)));
    }

    if let Some(open_paren) = text.find('(') {
        let close_paren = matching_paren_index(text, open_paren)
            .ok_or_else(|| ParseError::new(0, 0, "unterminated term"))?;
        let name = &text[..open_paren];
        let args_text = &text[open_paren + 1..close_paren];
        let args = split_arguments(args_text)
            .into_iter()
            .map(|arg| parse_term(arg, symbols))
            .collect::<Result<Vec<_>, _>>()?;
        let symbol_id = symbols.intern(
            name.trim(),
            args.len() as u8,
            SymbolKind::Function,
        );
        return Ok(Term::application(symbol_id, args));
    }

    // Check for infix operators (+, *, etc.)
    // We need to find the operator at the top level (not inside parentheses)
    if let Some((left, op, right)) = find_infix_operator(text) {
        let left_term = parse_term(left, symbols)?;
        let right_term = parse_term(right, symbols)?;
        let symbol_id = symbols.intern(op, 2, SymbolKind::Function);
        return Ok(Term::application(symbol_id, vec![left_term, right_term]));
    }

    if text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        let symbol_id = symbols.intern(text, 0, SymbolKind::Constant);
        return Ok(Term::application(symbol_id, vec![]));
    }

    Err(ParseError::new(0, 0, format!("unsupported token '{}'", text)))
}

/// Find an infix operator at the top level of a term.
/// Returns (left_operand, operator, right_operand) if found.
/// Handles operator precedence: + and - are lower precedence than * and /
fn find_infix_operator(text: &str) -> Option<(&str, &str, &str)> {
    // Operators in order of increasing precedence (we scan for lowest precedence first)
    let operators = ["+", "-", "*", "/"];

    let mut depth = 0;
    let text_bytes = text.as_bytes();

    // Scan from right to left to get left-associativity for equal-precedence operators
    for op in &operators {
        for i in (0..text.len()).rev() {
            let ch = text_bytes[i] as char;

            // Track parenthesis depth
            if ch == ')' {
                depth += 1;
            } else if ch == '(' {
                depth -= 1;
            }

            // Only consider operators at depth 0 (not inside parentheses)
            if depth == 0 && text[i..].starts_with(op) {
                let left = &text[..i];
                let right = &text[i + op.len()..];

                // Make sure we're not at the start (unary operator case)
                if !left.is_empty() && !right.is_empty() {
                    return Some((left.trim(), op, right.trim()));
                }
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
    file.commands.push(command);
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
        let list =
            section.to_clause_list(&mut arena, &symbols).expect("clause list");
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
        let op = file.operators.get_operator("&").unwrap();
        assert_eq!(op.precedence, 450);
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
        let list =
            section.to_clause_list(&mut arena, &symbols).expect("clause list");
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
        section.to_clause_list(&mut arena, &symbols).expect("clause list");
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
        section.to_clause_list(&mut arena, &symbols).expect("clause list");
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
        section.to_clause_list(&mut arena, &symbols).expect("clause list");
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
