use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

pub const DEFAULT_BATCH_SPACE_IDENT: &str = "&self";

#[derive(Debug, Clone)]
pub struct ExpandedMettaLine {
    pub text: String,
    pub source_file: String,
    pub source_line: usize,
    pub default_space: String,
}

#[derive(Debug, Clone)]
pub struct ImportEdge {
    pub source_file: String,
    pub source_line: usize,
    pub import_path: String,
    pub source_space: String,
    pub effective_space: String,
    pub target_file: String,
    pub skipped_cycle: bool,
    pub cycle_chain: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchCaptureAssignment {
    pub name: String,
    pub rhs: String,
    pub index: usize,
}

#[derive(Debug, Clone, Default)]
pub struct ImportExpansionMeta {
    pub directives_seen: usize,
    pub imported_files: HashSet<String>,
    pub target_spaces: HashSet<String>,
    pub non_self_directives: usize,
    pub skipped_cycles: usize,
    pub expanded_lines: usize,
    pub import_edges: Vec<ImportEdge>,
}

fn parse_expected_surface_directive(comment: &str) -> Result<Option<Vec<String>>, String> {
    let trimmed = comment.trim();
    if trimmed.is_empty() {
        return Ok(None);
    }

    let payload = if let Some(rest) = trimmed.strip_prefix("=>") {
        Some(rest.trim())
    } else if let Some((head, tail)) = trimmed.split_once(':') {
        if head.trim().eq_ignore_ascii_case("expect") {
            Some(tail.trim())
        } else {
            None
        }
    } else {
        None
    };

    let Some(payload) = payload else {
        return Ok(None);
    };

    let parts: Vec<String> = payload
        .split('|')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(ToString::to_string)
        .collect();
    if parts.is_empty() {
        return Err(
            "empty expectation directive (use ';=> value' or '; expect: value')".to_string()
        );
    }
    Ok(Some(parts))
}

fn strip_inline_comment_outside_string(raw: &str) -> &str {
    let mut in_string = false;
    let mut escaped = false;
    let mut chars = raw.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            ';' => return &raw[..idx],
            '/' => {
                if let Some((_, '/')) = chars.peek() {
                    return &raw[..idx];
                }
            },
            _ => {},
        }
    }
    raw
}

fn comment_payload_outside_string(raw: &str) -> Option<&str> {
    let mut in_string = false;
    let mut escaped = false;
    let mut chars = raw.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            ';' => return Some(&raw[idx + 1..]),
            '/' => {
                if let Some((_, '/')) = chars.peek() {
                    return Some(&raw[idx + 2..]);
                }
            },
            _ => {},
        }
    }
    None
}

fn line_has_expectation_comment(raw: &str) -> bool {
    let Some(payload) = comment_payload_outside_string(raw) else {
        return false;
    };
    parse_expected_surface_directive(payload)
        .ok()
        .flatten()
        .is_some()
}

fn paren_delta_outside_string(raw: &str) -> i32 {
    let mut delta = 0i32;
    let mut in_string = false;
    let mut escaped = false;
    for ch in raw.chars() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '(' => delta += 1,
            ')' => delta -= 1,
            _ => {},
        }
    }
    delta
}

fn is_batch_binding_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_batch_binding_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn parse_batch_binding_lhs(lhs: &str) -> Option<(String, usize)> {
    let name_and_index = lhs.strip_prefix('$')?.trim();
    if name_and_index.is_empty() {
        return None;
    }
    if let Some((name_part, index_part_with_bracket)) = name_and_index.split_once('[') {
        let name = name_part.trim();
        if name.is_empty() {
            return None;
        }
        let mut chars = name.chars();
        let first = chars.next()?;
        if !is_batch_binding_ident_start(first) || !chars.all(is_batch_binding_ident_continue) {
            return None;
        }
        let index_part = index_part_with_bracket.trim();
        let index_str = index_part.strip_suffix(']')?.trim();
        if index_str.is_empty() || !index_str.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let index = index_str.parse::<usize>().ok()?;
        Some((name.to_string(), index))
    } else {
        let name = name_and_index.trim();
        let mut chars = name.chars();
        let first = chars.next()?;
        if !is_batch_binding_ident_start(first) || !chars.all(is_batch_binding_ident_continue) {
            return None;
        }
        Some((name.to_string(), 0))
    }
}

pub fn parse_batch_capture_assignment(line: &str) -> Option<BatchCaptureAssignment> {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return None;
    }

    let mut in_string = false;
    let mut escaped = false;
    let mut eq_at: Option<usize> = None;
    for (idx, ch) in trimmed.char_indices() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '=' => {
                eq_at = Some(idx);
                break;
            },
            _ => {},
        }
    }
    let eq_at = eq_at?;
    let left = trimmed[..eq_at].trim();
    let right = trimmed[eq_at + 1..].trim();
    if right.is_empty() {
        return None;
    }
    let (name, index) = parse_batch_binding_lhs(left)?;
    Some(BatchCaptureAssignment { name, rhs: right.to_string(), index })
}

pub fn substitute_batch_bindings(input: &str, bindings: &HashMap<String, String>) -> String {
    if bindings.is_empty() {
        return input.to_string();
    }
    let chars: Vec<char> = input.chars().collect();
    let mut out = String::with_capacity(input.len());
    let mut i = 0usize;
    let mut in_string = false;
    let mut escaped = false;

    while i < chars.len() {
        let ch = chars[i];
        if in_string {
            out.push(ch);
            if escaped {
                escaped = false;
            } else {
                match ch {
                    '\\' => escaped = true,
                    '"' => in_string = false,
                    _ => {},
                }
            }
            i += 1;
            continue;
        }

        if ch == '"' {
            in_string = true;
            out.push(ch);
            i += 1;
            continue;
        }

        if ch == '$' && i + 1 < chars.len() && is_batch_binding_ident_start(chars[i + 1]) {
            let mut j = i + 2;
            while j < chars.len() && is_batch_binding_ident_continue(chars[j]) {
                j += 1;
            }
            let name: String = chars[i + 1..j].iter().collect();
            if let Some(value) = bindings.get(&name) {
                out.push_str(value);
            } else {
                out.push('$');
                out.push_str(&name);
            }
            i = j;
            continue;
        }

        out.push(ch);
        i += 1;
    }

    out
}

pub fn split_top_level_forms(raw: &str) -> Vec<String> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Vec::new();
    }
    if parse_batch_capture_assignment(trimmed).is_some() {
        return vec![trimmed.to_string()];
    }
    if trimmed.starts_with('!') {
        return vec![trimmed.to_string()];
    }
    if !trimmed.contains('(') && !trimmed.contains(')') {
        return vec![trimmed.to_string()];
    }

    let mut out = Vec::new();
    let mut in_string = false;
    let mut escaped = false;
    let mut depth = 0i32;
    let mut start: Option<usize> = None;
    let chars: Vec<(usize, char)> = raw.char_indices().collect();
    let mut i = 0usize;

    while i < chars.len() {
        let (idx, ch) = chars[i];
        if start.is_none() {
            if ch.is_whitespace() {
                i += 1;
                continue;
            }
            start = Some(idx);
        }

        if in_string {
            if escaped {
                escaped = false;
                i += 1;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            i += 1;
            continue;
        }

        match ch {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {},
        }

        let is_last = i + 1 == chars.len();
        let should_close = if depth > 0 || in_string {
            false
        } else if ch == ')' {
            true
        } else if ch.is_whitespace() {
            true
        } else {
            is_last
        };

        if should_close {
            let end = if ch.is_whitespace() {
                idx
            } else {
                idx + ch.len_utf8()
            };
            if let Some(st) = start {
                let chunk = raw[st..end].trim();
                if !chunk.is_empty() {
                    out.push(chunk.to_string());
                }
            }
            start = None;
        }
        i += 1;
    }

    if let Some(st) = start {
        let chunk = raw[st..].trim();
        if !chunk.is_empty() {
            out.push(chunk.to_string());
        }
    }

    out
}

pub fn coalesce_source_forms(
    content: &str,
    source_file: &str,
    default_space: &str,
) -> Result<Vec<ExpandedMettaLine>, String> {
    let mut out = Vec::new();
    let mut acc = String::new();
    let mut acc_start_line = 0usize;
    let mut depth = 0i32;

    for (raw_idx, raw_line) in content.lines().enumerate() {
        let source_line = raw_idx + 1;
        let trimmed_no_comment = strip_inline_comment_outside_string(raw_line).trim();
        let has_code = !trimmed_no_comment.is_empty();
        let keep_inline_comment = line_has_expectation_comment(raw_line);
        let line_for_acc = if keep_inline_comment {
            raw_line.trim_end().to_string()
        } else {
            strip_inline_comment_outside_string(raw_line)
                .trim_end()
                .to_string()
        };

        if acc.is_empty() {
            if !has_code {
                out.push(ExpandedMettaLine {
                    text: raw_line.to_string(),
                    source_file: source_file.to_string(),
                    source_line,
                    default_space: default_space.to_string(),
                });
                continue;
            }
            acc = line_for_acc;
            acc_start_line = source_line;
            depth = paren_delta_outside_string(trimmed_no_comment);
        } else if has_code {
            acc.push('\n');
            acc.push_str(&line_for_acc);
            depth += paren_delta_outside_string(trimmed_no_comment);
        }

        if !acc.is_empty() && depth <= 0 {
            let combined = std::mem::take(&mut acc);
            let has_expectation = line_has_expectation_comment(&combined);
            if has_expectation {
                out.push(ExpandedMettaLine {
                    text: combined,
                    source_file: source_file.to_string(),
                    source_line: acc_start_line,
                    default_space: default_space.to_string(),
                });
            } else {
                let forms = split_top_level_forms(&combined);
                if forms.len() <= 1 {
                    out.push(ExpandedMettaLine {
                        text: combined,
                        source_file: source_file.to_string(),
                        source_line: acc_start_line,
                        default_space: default_space.to_string(),
                    });
                } else {
                    for form in forms {
                        out.push(ExpandedMettaLine {
                            text: form,
                            source_file: source_file.to_string(),
                            source_line: acc_start_line,
                            default_space: default_space.to_string(),
                        });
                    }
                }
            }
            acc_start_line = 0;
            depth = 0;
        }
    }

    if !acc.is_empty() {
        return Err(format!(
            "unterminated multiline statement in '{}' starting at line {}",
            source_file, acc_start_line
        ));
    }

    Ok(out)
}

pub fn split_run_metta_file_line(
    raw_line: &str,
) -> Result<Option<(String, Option<Vec<String>>)>, String> {
    let trimmed = raw_line.trim();
    if trimmed.is_empty() || trimmed.starts_with(';') || trimmed.starts_with("//") {
        return Ok(None);
    }

    let mut in_string = false;
    let mut escaped = false;
    let mut comment_at: Option<(usize, usize)> = None;
    let mut it = trimmed.char_indices().peekable();
    while let Some((idx, ch)) = it.next() {
        if in_string {
            if escaped {
                escaped = false;
                continue;
            }
            match ch {
                '\\' => escaped = true,
                '"' => in_string = false,
                _ => {},
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            ';' => {
                comment_at = Some((idx, 1));
                break;
            },
            '/' => {
                if let Some((_, '/')) = it.peek() {
                    comment_at = Some((idx, 2));
                    break;
                }
            },
            _ => {},
        }
    }

    let (cmd_part, expected_surface) = if let Some((idx, marker_len)) = comment_at {
        let cmd = trimmed[..idx].trim();
        if cmd.is_empty() {
            return Ok(None);
        }
        let comment = trimmed[idx + marker_len..].trim();
        let expected = parse_expected_surface_directive(comment)?;
        (cmd.to_string(), expected)
    } else {
        (trimmed.to_string(), None)
    };

    if cmd_part.is_empty() {
        return Ok(None);
    }
    Ok(Some((cmd_part, expected_surface)))
}

pub fn is_hyperon_compat_ignorable_prose_line(line: &str) -> bool {
    let trimmed = line.trim();
    if trimmed.is_empty()
        || trimmed.starts_with(';')
        || trimmed.starts_with("//")
        || trimmed.starts_with('!')
        || trimmed.starts_with('(')
        || trimmed.starts_with('$')
    {
        return false;
    }
    trimmed.chars().any(char::is_whitespace)
}

fn parse_library_alias_token(token: &str) -> Option<String> {
    let trimmed = token.trim();
    if !trimmed.starts_with('(') || !trimmed.ends_with(')') {
        return None;
    }
    let inner = trimmed[1..trimmed.len() - 1].trim();
    let mut parts = inner.split_whitespace();
    let head = parts.next()?;
    if head != "library" {
        return None;
    }
    let name = parts.next()?.trim();
    if name.is_empty() || parts.next().is_some() {
        return None;
    }
    Some(format!("library:{}", name))
}

fn unquote_import_path_token(token: &str) -> Option<String> {
    if let Some(alias) = parse_library_alias_token(token) {
        return Some(alias);
    }
    if token.len() < 2 || !token.starts_with('"') || !token.ends_with('"') {
        return Some(token.to_string());
    }
    let mut out = String::new();
    let mut chars = token[1..token.len() - 1].chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        let esc = chars.next()?;
        match esc {
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            'u' => {
                if chars.next()? != '{' {
                    return None;
                }
                let mut hex = String::new();
                loop {
                    let c = chars.next()?;
                    if c == '}' {
                        break;
                    }
                    hex.push(c);
                }
                let code = u32::from_str_radix(&hex, 16).ok()?;
                out.push(char::from_u32(code)?);
            },
            other => out.push(other),
        }
    }
    Some(out)
}

fn tokenize_import_inner(inner: &str) -> Option<Vec<String>> {
    let mut tokens = Vec::new();
    let mut cur = String::new();
    let mut chars = inner.chars();
    let mut paren_depth = 0usize;
    while let Some(ch) = chars.next() {
        match ch {
            '"' => {
                if !cur.trim().is_empty() {
                    tokens.push(cur.clone());
                    cur.clear();
                }
                let mut s = String::from("\"");
                let mut escaped = false;
                let mut closed = false;
                for c in chars.by_ref() {
                    s.push(c);
                    if escaped {
                        escaped = false;
                        continue;
                    }
                    if c == '\\' {
                        escaped = true;
                        continue;
                    }
                    if c == '"' {
                        closed = true;
                        break;
                    }
                }
                if !closed {
                    return None;
                }
                tokens.push(s);
            },
            '(' => {
                paren_depth = paren_depth.saturating_add(1);
                cur.push(ch);
            },
            ')' => {
                if paren_depth == 0 {
                    return None;
                }
                paren_depth -= 1;
                cur.push(ch);
            },
            c if c.is_whitespace() && paren_depth == 0 => {
                if !cur.trim().is_empty() {
                    tokens.push(cur.clone());
                    cur.clear();
                }
            },
            _ => cur.push(ch),
        }
    }
    if paren_depth != 0 {
        return None;
    }
    if !cur.trim().is_empty() {
        tokens.push(cur);
    }
    Some(tokens)
}

pub fn parse_import_directive(line: &str) -> Option<(String, String)> {
    let trimmed = line.trim();
    let body = trimmed.strip_prefix('!').unwrap_or(trimmed).trim();
    let inner = body.strip_prefix('(')?.strip_suffix(')')?.trim();
    let toks = tokenize_import_inner(inner)?;
    if toks.is_empty() {
        return None;
    }
    if toks[0] != "import!" && toks[0] != "import" {
        return None;
    }
    match toks.as_slice() {
        [_op, path] => {
            Some((DEFAULT_BATCH_SPACE_IDENT.to_string(), unquote_import_path_token(path)?))
        },
        [_op, space, path] if space.starts_with('&') => {
            Some(((*space).clone(), unquote_import_path_token(path)?))
        },
        _ => None,
    }
}

pub fn effective_import_target_space(space: &str, current_default_space: &str) -> String {
    if space == DEFAULT_BATCH_SPACE_IDENT {
        current_default_space.to_string()
    } else {
        space.to_string()
    }
}

fn cycle_chain_for_target(
    stack: &[(PathBuf, String)],
    target: &Path,
    target_space: &str,
) -> Vec<String> {
    let Some(idx) = stack
        .iter()
        .position(|(p, s)| p.as_path() == target && s == target_space)
    else {
        return Vec::new();
    };
    let mut chain: Vec<String> = stack[idx..]
        .iter()
        .map(|(p, _)| p.display().to_string())
        .collect();
    chain.push(target.display().to_string());
    chain
}

fn resolve_import_path_token(
    import_path: &str,
    library_aliases: &HashMap<String, String>,
) -> String {
    if let Some(lib_name) = import_path.strip_prefix("library:") {
        if let Some(path) = library_aliases.get(lib_name) {
            return path.clone();
        }
    }
    import_path.to_string()
}

pub fn resolve_import_file_path(
    base_dir: &Path,
    import_path: &str,
    library_aliases: &HashMap<String, String>,
) -> PathBuf {
    let import_path = resolve_import_path_token(import_path, library_aliases);
    if let Some(lib_name) = import_path.strip_prefix("library:") {
        let local_lib = base_dir.join("lib").join(format!("{lib_name}.metta"));
        if local_lib.exists() {
            return local_lib;
        }
        let local_plain = base_dir.join(format!("{lib_name}.metta"));
        if local_plain.exists() {
            return local_plain;
        }
        // Also check parent directory's lib/ (e.g. PeTTa/examples/ → PeTTa/lib/)
        if let Some(parent_dir) = base_dir.parent() {
            let parent_lib = parent_dir.join("lib").join(format!("{lib_name}.metta"));
            if parent_lib.exists() {
                return parent_lib;
            }
        }
        return base_dir.join(format!("{lib_name}.metta"));
    }

    if !Path::new(&import_path).is_absolute() {
        let cwd_candidate = PathBuf::from(&import_path);
        if cwd_candidate.exists() {
            return cwd_candidate;
        }
    }

    let candidate = if Path::new(&import_path).is_absolute() {
        PathBuf::from(&import_path)
    } else {
        base_dir.join(&import_path)
    };
    if candidate.exists() {
        return candidate;
    }
    if candidate.extension().is_none() {
        let with_metta = candidate.with_extension("metta");
        if with_metta.exists() {
            return with_metta;
        }
    }
    if !Path::new(&import_path).is_absolute() {
        if let Some(parent_dir) = base_dir.parent() {
            let parent_candidate = parent_dir.join(&import_path);
            if parent_candidate.exists() {
                return parent_candidate;
            }
            if parent_candidate.extension().is_none() {
                let with_metta = parent_candidate.with_extension("metta");
                if with_metta.exists() {
                    return with_metta;
                }
            }
        }
    }
    candidate
}

fn is_python_source_path(path: &Path) -> bool {
    path.extension()
        .and_then(|ext| ext.to_str())
        .is_some_and(|ext| ext.eq_ignore_ascii_case("py"))
}

fn expand_metta_file_with_imports_inner(
    file_path: &Path,
    seen: &mut HashSet<PathBuf>,
    stack: &mut Vec<(PathBuf, String)>,
    depth: usize,
    meta: &mut ImportExpansionMeta,
    current_default_space: &str,
    library_aliases: &HashMap<String, String>,
) -> Result<Vec<ExpandedMettaLine>, String> {
    if depth > 32 {
        return Err(format!("import depth exceeded while expanding '{}'", file_path.display()));
    }
    let canonical = std::fs::canonicalize(file_path).unwrap_or_else(|_| file_path.to_path_buf());
    if stack
        .iter()
        .any(|(p, s)| p == &canonical && s == current_default_space)
    {
        meta.skipped_cycles += 1;
        return Ok(Vec::new());
    }
    seen.insert(canonical.clone());
    stack.push((canonical.clone(), current_default_space.to_string()));
    meta.imported_files.insert(canonical.display().to_string());
    let content = std::fs::read_to_string(&canonical)
        .map_err(|e| format!("Failed to read '{}': {}", canonical.display(), e))?;
    let base_dir = canonical.parent().unwrap_or_else(|| Path::new("."));
    let mut expanded = Vec::new();

    let coalesced =
        coalesce_source_forms(&content, &canonical.display().to_string(), current_default_space)?;

    for coalesced_line in coalesced {
        let parsed = split_run_metta_file_line(&coalesced_line.text)?;
        if let Some((cmd, _)) = parsed {
            if let Some((space, import_path)) = parse_import_directive(&cmd) {
                meta.directives_seen += 1;
                meta.target_spaces.insert(space.clone());
                if space != DEFAULT_BATCH_SPACE_IDENT {
                    meta.non_self_directives += 1;
                }
                let effective_space = effective_import_target_space(&space, current_default_space);
                let import_file = resolve_import_file_path(base_dir, &import_path, library_aliases);
                let canonical_target =
                    std::fs::canonicalize(&import_file).unwrap_or_else(|_| import_file.clone());
                let is_python_import =
                    is_python_source_path(&canonical_target) || is_python_source_path(&import_file);
                let will_skip_cycle = stack
                    .iter()
                    .any(|(p, s)| p == &canonical_target && s == &effective_space);
                meta.import_edges.push(ImportEdge {
                    source_file: canonical.display().to_string(),
                    source_line: coalesced_line.source_line,
                    import_path: import_path.clone(),
                    source_space: space.clone(),
                    effective_space: effective_space.clone(),
                    target_file: canonical_target.display().to_string(),
                    skipped_cycle: will_skip_cycle,
                    cycle_chain: cycle_chain_for_target(stack, &canonical_target, &effective_space),
                });
                if is_python_import {
                    seen.insert(canonical_target.clone());
                    meta.imported_files
                        .insert(canonical_target.display().to_string());
                    continue;
                }
                let mut nested = expand_metta_file_with_imports_inner(
                    &import_file,
                    seen,
                    stack,
                    depth + 1,
                    meta,
                    &effective_space,
                    library_aliases,
                )?;
                expanded.append(&mut nested);
                continue;
            }
        }
        expanded.push(coalesced_line);
    }

    stack.pop();
    Ok(expanded)
}

pub fn expand_metta_file_with_imports(
    file_path: &Path,
    seen: &mut HashSet<PathBuf>,
    depth: usize,
    meta: &mut ImportExpansionMeta,
    current_default_space: &str,
    library_aliases: &HashMap<String, String>,
) -> Result<Vec<ExpandedMettaLine>, String> {
    let mut stack: Vec<(PathBuf, String)> = Vec::new();
    expand_metta_file_with_imports_inner(
        file_path,
        seen,
        &mut stack,
        depth,
        meta,
        current_default_space,
        library_aliases,
    )
}

pub fn expand_import_directive_from_source(
    source_file: &str,
    source_line: usize,
    source_space: &str,
    import_path: &str,
    current_default_space: &str,
    seen: &mut HashSet<PathBuf>,
    meta: &mut ImportExpansionMeta,
    library_aliases: &HashMap<String, String>,
) -> Result<Vec<ExpandedMettaLine>, String> {
    meta.directives_seen += 1;
    meta.target_spaces.insert(source_space.to_string());
    if source_space != DEFAULT_BATCH_SPACE_IDENT {
        meta.non_self_directives += 1;
    }

    let source_path = Path::new(source_file);
    let base_dir = source_path.parent().unwrap_or_else(|| Path::new("."));
    let import_file = resolve_import_file_path(base_dir, import_path, library_aliases);
    let canonical_target =
        std::fs::canonicalize(&import_file).unwrap_or_else(|_| import_file.clone());
    let is_python_import =
        is_python_source_path(&canonical_target) || is_python_source_path(&import_file);
    let effective_space = effective_import_target_space(source_space, current_default_space);
    meta.import_edges.push(ImportEdge {
        source_file: source_file.to_string(),
        source_line,
        import_path: import_path.to_string(),
        source_space: source_space.to_string(),
        effective_space: effective_space.clone(),
        target_file: canonical_target.display().to_string(),
        skipped_cycle: false,
        cycle_chain: Vec::new(),
    });
    if is_python_import {
        seen.insert(canonical_target.clone());
        meta.imported_files
            .insert(canonical_target.display().to_string());
        return Ok(Vec::new());
    }

    let mut nested = expand_metta_file_with_imports(
        &import_file,
        seen,
        0,
        meta,
        &effective_space,
        library_aliases,
    )?;
    meta.expanded_lines += nested.len();
    Ok(std::mem::take(&mut nested))
}
