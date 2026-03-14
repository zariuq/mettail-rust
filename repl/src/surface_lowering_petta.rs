//! PeTTa `SurfaceLowering` implementation.
//!
//! PeTTa is fundamentally simpler than HE — no C_ prefixes, no State wrapping.
//! Surface expressions are bare S-expressions; results are identity-decoded.

use anyhow::Result;

use crate::metta_surface::{SExpr, SurfaceSpaceState};
use crate::surface_lowering::SurfaceLowering;
use crate::syntax_spec::{AtomEncodingSpec, DisplayProfile};

pub struct PeTTaSurfaceLowering;

impl SurfaceLowering for PeTTaSurfaceLowering {
    fn dialect_key(&self) -> &str {
        "petta"
    }

    fn bypasses_surface_rewriter(&self) -> bool {
        true
    }

    fn encode_expr(&self, expr: &SExpr, _enc: Option<&AtomEncodingSpec>) -> Result<String> {
        Ok(render_sexpr(expr))
    }

    fn lower_eval(
        &self,
        expr: &SExpr,
        space: &SurfaceSpaceState,
        _enc: Option<&AtomEncodingSpec>,
    ) -> Result<Vec<String>> {
        // PeTTa lowering: encode the query expression and space entries as a
        // single term that PeTTaLanguage::parse_term can consume.
        let query = render_sexpr(expr);

        // Build space entries from both exact and pattern equation rules.
        let mut space_lines = Vec::new();
        for (lhs, rhs) in &space.eq_entries {
            space_lines.push(format!("(= {lhs} {rhs})"));
        }
        for (lhs, rhs) in &space.pattern_eq_entries {
            space_lines.push(format!("(= {lhs} {rhs})"));
        }

        // Combine into a term: space entries newline-separated, then the query
        let mut term_text = space_lines.join("\n");
        if !term_text.is_empty() {
            term_text.push('\n');
        }
        term_text.push_str(&query);

        Ok(vec![term_text])
    }

    fn decode_atom(
        &self,
        core: &str,
        _enc: Option<&AtomEncodingSpec>,
        _disp: Option<&DisplayProfile>,
    ) -> String {
        decode_petta_display_to_surface(core).unwrap_or_else(|| core.to_string())
    }

    fn extract_result(&self, nf_display: &str) -> Option<String> {
        // For PeTTa, the whole normal form IS the result
        let trimmed = nf_display.trim();
        if trimmed.is_empty() {
            None
        } else {
            Some(trimmed.to_string())
        }
    }

    fn format_alloc_space(&self, encoded_handle: &str) -> String {
        // PeTTa doesn't use C_State wrapping
        encoded_handle.to_string()
    }

    fn requires_syntax_spec(&self) -> bool {
        false
    }

    fn requires_lookup_plan(&self) -> bool {
        true
    }
}

/// Render a surface SExpr as a bare S-expression string.
fn render_sexpr(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(s) => s.clone(),
        SExpr::List(items) => {
            if items.is_empty() {
                "()".to_string()
            } else {
                let parts: Vec<String> = items.iter().map(render_sexpr).collect();
                format!("({})", parts.join(" "))
            }
        }
    }
}

fn decode_petta_display_to_surface(core: &str) -> Option<String> {
    let tokens = tokenize_petta_display(core).ok()?;
    let (expr, rest) = parse_petta_display_expr(&tokens).ok()?;
    if !rest.is_empty() {
        return None;
    }
    Some(render_surface_expr(&expr))
}

fn render_surface_expr(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(s) => s.clone(),
        SExpr::List(items) => {
            let rendered: Vec<String> = items.iter().map(render_surface_expr).collect();
            format!("({})", rendered.join(" "))
        }
    }
}

fn tokenize_petta_display(input: &str) -> Result<Vec<String>> {
    let mut out = Vec::new();
    let mut chars = input.trim().chars().peekable();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
            continue;
        }
        match c {
            '(' | ')' | '[' | ']' | ',' => {
                out.push(c.to_string());
                chars.next();
            }
            '"' => {
                let mut s = String::new();
                s.push(chars.next().expect("opening quote already peeked"));
                let mut escaped = false;
                for ch in chars.by_ref() {
                    s.push(ch);
                    if escaped {
                        escaped = false;
                        continue;
                    }
                    if ch == '\\' {
                        escaped = true;
                    } else if ch == '"' {
                        break;
                    }
                }
                out.push(s);
            }
            _ => {
                let mut atom = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_whitespace() || matches!(ch, '(' | ')' | '[' | ']' | ',') {
                        break;
                    }
                    atom.push(ch);
                    chars.next();
                }
                out.push(atom);
            }
        }
    }
    Ok(out)
}

fn parse_petta_display_expr<'a>(tokens: &'a [String]) -> Result<(SExpr, &'a [String])> {
    if tokens.is_empty() {
        anyhow::bail!("unexpected end of PeTTa display input");
    }
    if tokens[0] == "[" {
        let mut rest = &tokens[1..];
        let mut items = Vec::new();
        while !rest.is_empty() && rest[0] != "]" {
            let (item, next) = parse_petta_display_expr(rest)?;
            items.push(item);
            rest = next;
            if !rest.is_empty() && rest[0] == "," {
                rest = &rest[1..];
            }
        }
        if rest.is_empty() || rest[0] != "]" {
            anyhow::bail!("unterminated PeTTa list display");
        }
        return Ok((SExpr::List(items), &rest[1..]));
    }

    let head = tokens[0].clone();
    let mut rest = &tokens[1..];
    if !rest.is_empty() && rest[0] == "(" {
        rest = &rest[1..];
        let mut args = Vec::new();
        while !rest.is_empty() && rest[0] != ")" {
            let (arg, next) = parse_petta_display_expr(rest)?;
            args.push(arg);
            rest = next;
            if !rest.is_empty() && rest[0] == "," {
                rest = &rest[1..];
            }
        }
        if rest.is_empty() || rest[0] != ")" {
            anyhow::bail!("unterminated PeTTa application display");
        }
        rest = &rest[1..];
        let mut items = Vec::with_capacity(args.len() + 1);
        items.push(SExpr::Atom(head));
        items.extend(args);
        Ok((SExpr::List(items), rest))
    } else {
        Ok((SExpr::Atom(head), rest))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_petta_display_atom() {
        assert_eq!(
            decode_petta_display_to_surface("hello").as_deref(),
            Some("hello")
        );
    }

    #[test]
    fn decode_petta_display_application() {
        assert_eq!(
            decode_petta_display_to_surface("foo(a, b)").as_deref(),
            Some("(foo a b)")
        );
    }

    #[test]
    fn decode_petta_display_nested_application() {
        assert_eq!(
            decode_petta_display_to_surface("foo(bar(a), b)").as_deref(),
            Some("(foo (bar a) b)")
        );
    }

    #[test]
    fn decode_petta_display_list() {
        assert_eq!(
            decode_petta_display_to_surface("[a, b]").as_deref(),
            Some("(a b)")
        );
    }
}
