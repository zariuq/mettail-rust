//! Shared S-expression type for surface `.metta` parsing.
//!
//! `SExpr` is the output of the tree-sitter grammar pipeline and the shared
//! intermediate representation between surface syntax and per-language evaluation.
//! All `.metta` surface parsing must flow through this type.

use crate::artifact_contract::PatternNode;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl SExpr {
    pub fn atom(s: impl Into<String>) -> Self {
        SExpr::Atom(s.into())
    }

    pub fn list(items: Vec<SExpr>) -> Self {
        SExpr::List(items)
    }
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", render_sexpr(self))
    }
}

/// Render an S-expression back to its surface text form.
pub fn render_sexpr(expr: &SExpr) -> String {
    match expr {
        SExpr::Atom(s) => s.clone(),
        SExpr::List(items) => {
            let inner: Vec<String> = items.iter().map(render_sexpr).collect();
            format!("({})", inner.join(" "))
        },
    }
}

/// Convert a tree-sitter `SExpr` to the `PatternNode` representation used by
/// the rewrite/evaluation engine.
///
/// Conversion rules (matching existing PeTTa semantics):
/// - `$x` atoms → `PatternNode::Fvar { name: "x" }`
/// - Other atoms → `PatternNode::Apply { ctor: atom, args: [] }` (0-arity symbol)
/// - Empty list `()` → `PatternNode::Apply { ctor: "()", args: [] }`
/// - List with atom head `(f a b)` → `PatternNode::Apply { ctor: "f", args: [a', b'] }`
/// - List with complex head `((f x) a)` → `PatternNode::Apply { ctor: "expr", args: [(f x)', a'] }`
pub fn sexpr_to_pattern(sexpr: &SExpr) -> Result<PatternNode, String> {
    match sexpr {
        SExpr::Atom(s) => {
            if let Some(var) = s.strip_prefix('$') {
                Ok(PatternNode::Fvar { name: var.to_string() })
            } else {
                Ok(PatternNode::Apply { ctor: s.clone(), args: vec![] })
            }
        },
        SExpr::List(items) => {
            if items.is_empty() {
                Ok(PatternNode::Apply { ctor: "()".to_string(), args: vec![] })
            } else {
                let head = &items[0];
                let rest: Result<Vec<_>, _> = items[1..].iter().map(sexpr_to_pattern).collect();
                let rest = rest?;
                match head {
                    SExpr::Atom(name) if !name.starts_with('$') => {
                        Ok(PatternNode::Apply { ctor: name.clone(), args: rest })
                    },
                    _ => {
                        // Head is complex or a variable — wrap with synthetic "expr" head
                        let mut args = vec![sexpr_to_pattern(head)?];
                        args.extend(rest);
                        Ok(PatternNode::Apply { ctor: "expr".to_string(), args })
                    },
                }
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atom_to_pattern() {
        let s = SExpr::atom("foo");
        let p = sexpr_to_pattern(&s).unwrap();
        assert_eq!(p, PatternNode::Apply { ctor: "foo".into(), args: vec![] });
    }

    #[test]
    fn variable_to_pattern() {
        let s = SExpr::atom("$x");
        let p = sexpr_to_pattern(&s).unwrap();
        assert_eq!(p, PatternNode::Fvar { name: "x".into() });
    }

    #[test]
    fn empty_list_to_pattern() {
        let s = SExpr::list(vec![]);
        let p = sexpr_to_pattern(&s).unwrap();
        assert_eq!(p, PatternNode::Apply { ctor: "()".into(), args: vec![] });
    }

    #[test]
    fn simple_list_to_pattern() {
        let s = SExpr::list(vec![SExpr::atom("+"), SExpr::atom("1"), SExpr::atom("2")]);
        let p = sexpr_to_pattern(&s).unwrap();
        assert_eq!(
            p,
            PatternNode::Apply {
                ctor: "+".into(),
                args: vec![
                    PatternNode::Apply { ctor: "1".into(), args: vec![] },
                    PatternNode::Apply { ctor: "2".into(), args: vec![] },
                ],
            }
        );
    }

    #[test]
    fn complex_head_to_pattern() {
        // ((f x) a) → Apply { ctor: "expr", args: [Apply{f,[x]}, Apply{a,[]}] }
        let s = SExpr::list(vec![
            SExpr::list(vec![SExpr::atom("f"), SExpr::atom("x")]),
            SExpr::atom("a"),
        ]);
        let p = sexpr_to_pattern(&s).unwrap();
        assert_eq!(
            p,
            PatternNode::Apply {
                ctor: "expr".into(),
                args: vec![
                    PatternNode::Apply {
                        ctor: "f".into(),
                        args: vec![PatternNode::Apply { ctor: "x".into(), args: vec![] }],
                    },
                    PatternNode::Apply { ctor: "a".into(), args: vec![] },
                ],
            }
        );
    }

    #[test]
    fn variable_head_to_pattern() {
        // ($f a) → Apply { ctor: "expr", args: [Fvar("f"), Apply{a,[]}] }
        let s = SExpr::list(vec![SExpr::atom("$f"), SExpr::atom("a")]);
        let p = sexpr_to_pattern(&s).unwrap();
        assert_eq!(
            p,
            PatternNode::Apply {
                ctor: "expr".into(),
                args: vec![
                    PatternNode::Fvar { name: "f".into() },
                    PatternNode::Apply { ctor: "a".into(), args: vec![] },
                ],
            }
        );
    }

    #[test]
    fn render_roundtrip() {
        assert_eq!(render_sexpr(&SExpr::atom("foo")), "foo");
        assert_eq!(
            render_sexpr(&SExpr::list(vec![SExpr::atom("+"), SExpr::atom("1"), SExpr::atom("2"),])),
            "(+ 1 2)"
        );
    }
}
