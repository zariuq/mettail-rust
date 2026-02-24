/// Surface-syntax adapters for MeTTa-like input/output.
///
/// The Lean-exported MeTTaMinimal language currently uses canonical constructor
/// names (`C_State`, `C_Eval`, ...). This module adds cosmetic adapters so users
/// can write/read a closer MeTTa-like surface syntax.

#[derive(Debug, Clone)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

fn is_mettaminimal(language_name: &str) -> bool {
    language_name.eq_ignore_ascii_case("mettaminimalstate")
}

fn map_symbol_to_internal(sym: &str) -> &str {
    match sym {
        "State" => "C_State",
        "Eval" => "C_Eval",
        "Unify" => "C_Unify",
        "Chain" => "C_Chain",
        "CollapseBind" => "C_CollapseBind",
        "SuperposeBind" => "C_SuperposeBind",
        "Return" => "C_Return",
        "Done" => "C_Done",
        "ATrue" => "C_ATrue",
        "AFalse" => "C_AFalse",
        _ => sym,
    }
}

fn map_symbol_to_surface(sym: &str) -> &str {
    match sym {
        "C_State" => "State",
        "C_Eval" => "Eval",
        "C_Unify" => "Unify",
        "C_Chain" => "Chain",
        "C_CollapseBind" => "CollapseBind",
        "C_SuperposeBind" => "SuperposeBind",
        "C_Return" => "Return",
        "C_Done" => "Done",
        "C_ATrue" => "ATrue",
        "C_AFalse" => "AFalse",
        _ => sym,
    }
}

fn rewrite_identifiers(input: &str, mapper: fn(&str) -> &str) -> String {
    let mut out = String::with_capacity(input.len());
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            out.push_str(mapper(&ident));
        } else {
            out.push(c);
            i += 1;
        }
    }
    out
}

fn tokenize_sexpr(input: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for ch in input.chars() {
        match ch {
            '(' | ')' => {
                if !cur.trim().is_empty() {
                    toks.push(cur.trim().to_string());
                }
                cur.clear();
                toks.push(ch.to_string());
            },
            c if c.is_whitespace() => {
                if !cur.trim().is_empty() {
                    toks.push(cur.trim().to_string());
                }
                cur.clear();
            },
            _ => cur.push(ch),
        }
    }
    if !cur.trim().is_empty() {
        toks.push(cur.trim().to_string());
    }
    toks
}

fn parse_sexpr(tokens: &[String], i: &mut usize) -> Result<SExpr, String> {
    if *i >= tokens.len() {
        return Err("unexpected end of input".to_string());
    }
    let tok = &tokens[*i];
    if tok == "(" {
        *i += 1;
        let mut elems = Vec::new();
        while *i < tokens.len() && tokens[*i] != ")" {
            elems.push(parse_sexpr(tokens, i)?);
        }
        if *i >= tokens.len() || tokens[*i] != ")" {
            return Err("missing ')'".to_string());
        }
        *i += 1;
        Ok(SExpr::List(elems))
    } else if tok == ")" {
        Err("unexpected ')'".to_string())
    } else {
        *i += 1;
        Ok(SExpr::Atom(tok.clone()))
    }
}

fn sexpr_to_internal(expr: &SExpr) -> Result<String, String> {
    match expr {
        SExpr::Atom(a) => Ok(map_symbol_to_internal(a).to_string()),
        SExpr::List(xs) => {
            if xs.is_empty() {
                return Err("empty list is not a valid term".to_string());
            }
            let head = match &xs[0] {
                SExpr::Atom(h) => map_symbol_to_internal(h).to_string(),
                _ => return Err("list head must be a symbol".to_string()),
            };
            if xs.len() == 1 {
                return Ok(head);
            }
            let mut args = Vec::with_capacity(xs.len() - 1);
            for x in &xs[1..] {
                args.push(sexpr_to_internal(x)?);
            }
            Ok(format!("{head}({})", args.join(", ")))
        },
    }
}

fn try_sexpr_to_internal(input: &str) -> Option<String> {
    let trimmed = input.trim();
    if !trimmed.starts_with('(') {
        return None;
    }
    let toks = tokenize_sexpr(trimmed);
    let mut i = 0;
    let parsed = parse_sexpr(&toks, &mut i).ok()?;
    if i != toks.len() {
        return None;
    }
    sexpr_to_internal(&parsed).ok()
}

fn skip_ws(chars: &[char], i: &mut usize) {
    while *i < chars.len() && chars[*i].is_whitespace() {
        *i += 1;
    }
}

fn parse_ident(chars: &[char], i: &mut usize) -> Result<String, String> {
    skip_ws(chars, i);
    if *i >= chars.len() {
        return Err("unexpected end of input".to_string());
    }
    let c = chars[*i];
    if !(c.is_ascii_alphabetic() || c == '_') {
        return Err(format!("expected identifier at position {}", i));
    }
    let start = *i;
    *i += 1;
    while *i < chars.len() && (chars[*i].is_ascii_alphanumeric() || chars[*i] == '_') {
        *i += 1;
    }
    Ok(chars[start..*i].iter().collect())
}

fn parse_call_syntax(chars: &[char], i: &mut usize) -> Result<SExpr, String> {
    let head = parse_ident(chars, i)?;
    skip_ws(chars, i);
    if *i >= chars.len() || chars[*i] != '(' {
        return Ok(SExpr::Atom(head));
    }

    *i += 1; // consume '('
    let mut args = Vec::new();
    loop {
        skip_ws(chars, i);
        if *i >= chars.len() {
            return Err("missing ')'".to_string());
        }
        if chars[*i] == ')' {
            *i += 1; // consume ')'
            break;
        }
        args.push(parse_call_syntax(chars, i)?);
        skip_ws(chars, i);
        if *i >= chars.len() {
            return Err("missing ')'".to_string());
        }
        if chars[*i] == ',' {
            *i += 1; // consume ','
            continue;
        }
        if chars[*i] == ')' {
            *i += 1; // consume ')'
            break;
        }
        return Err(format!("expected ',' or ')' at position {}", i));
    }

    let mut elems = Vec::with_capacity(args.len() + 1);
    elems.push(SExpr::Atom(head));
    elems.extend(args);
    Ok(SExpr::List(elems))
}

fn sexpr_to_surface(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(a) => map_symbol_to_surface(a).to_string(),
        SExpr::List(xs) => {
            let parts: Vec<String> = xs.iter().map(sexpr_to_surface).collect();
            format!("({})", parts.join(" "))
        },
    }
}

fn try_call_to_surface(input: &str) -> Option<String> {
    let chars: Vec<char> = input.chars().collect();
    let mut i = 0;
    let parsed = parse_call_syntax(&chars, &mut i).ok()?;
    skip_ws(&chars, &mut i);
    if i != chars.len() {
        return None;
    }
    Some(sexpr_to_surface(&parsed))
}

/// Normalize user input into canonical constructor syntax for the selected language.
pub fn normalize_input_for_language(language_name: &str, input: &str) -> String {
    if !is_mettaminimal(language_name) {
        return input.to_string();
    }
    if input.contains("C_") {
        return input.to_string();
    }
    if let Some(s) = try_sexpr_to_internal(input) {
        return s;
    }
    rewrite_identifiers(input, map_symbol_to_internal)
}

/// Render canonical output into a friendlier MeTTa-like surface.
pub fn prettify_output_for_language(language_name: &str, output: &str) -> String {
    if !is_mettaminimal(language_name) {
        return output.to_string();
    }
    if let Some(s) = try_call_to_surface(output) {
        return s;
    }
    rewrite_identifiers(output, map_symbol_to_surface)
}
