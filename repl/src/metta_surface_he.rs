//! HE MeTTa surface profile: lowering + decoding for the MeTTaHE backend.
//!
//! This module implements the HE-specific translation between surface MeTTa
//! syntax (SExpr) and HE core terms.  It is intentionally thin — no evaluation,
//! no rewriting, just structural mapping.
//!
//! Lowering:  surface SExpr  →  HE core term string
//! Decoding:  HE core result →  surface display string

use super::metta_surface::{SExpr, SurfaceSpaceState};
use super::syntax_spec::{
    AtomEncodingSpec, DisplayProfile, DisplaySegment, IntEncoding, StringEncoding,
};

// ═══════════════════════════════════════════════════════════════════════
//  Spec-driven encoding: surface SExpr → core term string
// ═══════════════════════════════════════════════════════════════════════

/// Encode a surface SExpr as a core term string using the encoding spec.
pub fn spec_encode_sexpr(spec: &AtomEncodingSpec, expr: &SExpr) -> Result<String, String> {
    match expr {
        SExpr::Atom(s) => spec_encode_atom(spec, s),
        SExpr::List(items) => {
            if items.is_empty() {
                return Ok(format!("C_{}", spec.expr_nil));
            }
            // Check sugar forms
            if items.len() >= 2 {
                if let SExpr::Atom(head) = &items[0] {
                    for sf in &spec.sugar_forms {
                        if head == &sf.head && items.len() == (sf.arity as usize) + 1 {
                            let mut args = Vec::new();
                            for item in &items[1..] {
                                args.push(spec_encode_sexpr(spec, item)?);
                            }
                            return Ok(format!("C_{}({})", sf.constructor_label, args.join(",")));
                        }
                    }
                }
            }
            // General expression: fold into ExprCons chain
            spec_encode_expr_list(spec, items)
        }
    }
}

fn spec_encode_atom(spec: &AtomEncodingSpec, s: &str) -> Result<String, String> {
    // Boolean literals
    for alias in &spec.boolean_literals {
        if s == alias.surface_symbol {
            return Ok(format!("C_{}", alias.constructor_label));
        }
    }

    // Integer literal
    if let Some(n) = s.parse::<i64>().ok() {
        let tok = match &spec.int_encoding {
            IntEncoding::Prefixed { prefix, neg_marker } => {
                if n < 0 {
                    format!("{prefix}{neg_marker}{}", -n)
                } else {
                    format!("{prefix}{n}")
                }
            }
        };
        return Ok(format!("C_{}({tok})", spec.int_wrapper));
    }

    // String literal
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        let inner = &s[1..s.len() - 1];
        let tok = match &spec.string_encoding {
            StringEncoding::Prefixed { prefix } => format!("{prefix}{inner}"),
            StringEncoding::HexPrefixed { prefix } => {
                format!("{prefix}{}", encode_hex_bytes(inner))
            }
        };
        return Ok(format!("C_{}({tok})", spec.string_wrapper));
    }

    // Variable
    if s.starts_with('$') && s.len() > 1 {
        let name = &s[1..];
        let name_enc = spec_encode_symbol_name(spec, name);
        if spec.variable_wraps_name {
            return Ok(format!(
                "C_{}(C_{}({name_enc}))",
                spec.variable_wrapper, spec.symbol_wrapper
            ));
        } else {
            return Ok(format!("C_{}({name_enc})", spec.variable_wrapper));
        }
    }

    // Type keywords
    for alias in &spec.type_keywords {
        if s == alias.surface_symbol {
            return Ok(format!("C_{}", alias.constructor_label));
        }
    }

    // Operator aliases
    for alias in &spec.operator_aliases {
        if s == alias.surface_symbol {
            return Ok(format!("C_{}", alias.constructor_label));
        }
    }

    // Regular symbol
    let name_enc = spec_encode_symbol_name(spec, s);
    Ok(format!("C_{}({name_enc})", spec.symbol_wrapper))
}

fn spec_encode_symbol_name(spec: &AtomEncodingSpec, s: &str) -> String {
    if is_safe_ident(s) {
        s.to_string()
    } else {
        format!("{}{}", spec.symbol_escaping.escape_prefix, encode_hex_bytes(s))
    }
}

fn spec_encode_expr_list(spec: &AtomEncodingSpec, items: &[SExpr]) -> Result<String, String> {
    let mut acc = format!("C_{}", spec.expr_nil);
    for item in items.iter().rev() {
        let encoded = spec_encode_sexpr(spec, item)?;
        acc = format!("C_{}({encoded},{acc})", spec.expr_cons);
    }
    Ok(acc)
}

// ═══════════════════════════════════════════════════════════════════════
//  Spec-driven decoding: core term string → surface display
// ═══════════════════════════════════════════════════════════════════════

/// Decode a core atom using the encoding spec and display profile.
pub fn spec_decode_atom(
    spec: &AtomEncodingSpec,
    display: &DisplayProfile,
    core_atom: &str,
) -> String {
    let atom = core_atom.trim();

    // Check nullary: ExprNil
    if atom == format!("C_{}", spec.expr_nil) {
        return "()".to_string();
    }

    // Nullary operator aliases (reverse lookup)
    for alias in &spec.operator_aliases {
        if atom == format!("C_{}", alias.constructor_label) {
            return alias.surface_symbol.clone();
        }
    }

    // Nullary type keywords (reverse lookup)
    for alias in &spec.type_keywords {
        if atom == format!("C_{}", alias.constructor_label) {
            return alias.surface_symbol.clone();
        }
    }

    // Nullary boolean literals (reverse lookup, take first match)
    for alias in &spec.boolean_literals {
        if atom == format!("C_{}", alias.constructor_label) {
            return alias.surface_symbol.clone();
        }
    }

    // SymAtom(name) → name
    if let Some(inner) = strip_wrapper(atom, &format!("C_{}", spec.symbol_wrapper)) {
        return spec_decode_symbol_name(spec, inner);
    }

    // VarAtom(...) → $name
    if let Some(inner) = strip_wrapper(atom, &format!("C_{}", spec.variable_wrapper)) {
        if spec.variable_wraps_name {
            if let Some(name) = strip_wrapper(inner, &format!("C_{}", spec.symbol_wrapper)) {
                return format!("${}", spec_decode_symbol_name(spec, name));
            }
        }
        return format!("${}", spec_decode_symbol_name(spec, inner));
    }

    // GInt(token) → integer
    if let Some(inner) = strip_wrapper(atom, &format!("C_{}", spec.int_wrapper)) {
        return spec_decode_int_token(spec, inner);
    }

    // GString(token) → "string"
    if let Some(inner) = strip_wrapper(atom, &format!("C_{}", spec.string_wrapper)) {
        return spec_decode_string_token(spec, inner);
    }

    // Sugar forms (reverse): C_ArrowType(a, b) → (-> a b)
    for sf in &spec.sugar_forms {
        if let Some(inner) = strip_wrapper(atom, &format!("C_{}", sf.constructor_label)) {
            let args = split_top_level_args(inner);
            if args.len() == sf.arity as usize {
                let decoded: Vec<String> = args
                    .iter()
                    .map(|a| spec_decode_atom(spec, display, a))
                    .collect();
                return format!("({} {})", sf.head, decoded.join(" "));
            }
        }
    }

    // DisplayProfile entries (compound forms like ErrorAtom, BadType, etc.)
    for entry in &display.entries {
        if let Some(inner) = strip_wrapper(atom, &format!("C_{}", entry.constructor_label)) {
            let args = split_top_level_args(inner);
            // Build positional param name → index mapping
            let param_names: Vec<&str> = entry
                .segments
                .iter()
                .filter_map(|seg| match seg {
                    DisplaySegment::Param { name } => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            let mut result = String::new();
            for seg in &entry.segments {
                match seg {
                    DisplaySegment::Lit { text } => result.push_str(text),
                    DisplaySegment::Param { name } => {
                        // Map param name to positional index
                        let idx = param_names
                            .iter()
                            .position(|n| n == &name.as_str())
                            .unwrap_or(usize::MAX);
                        if idx < args.len() {
                            result.push_str(&spec_decode_atom(spec, display, args[idx]));
                        }
                    }
                }
            }
            return result;
        }
    }

    // ExprCons chain → list
    if let Some(list) = spec_try_decode_cons_list(spec, display, atom) {
        return list;
    }

    // Fallback: return as-is
    atom.to_string()
}

fn spec_decode_symbol_name(spec: &AtomEncodingSpec, tok: &str) -> String {
    if let Some(hex) = tok.strip_prefix(&spec.symbol_escaping.escape_prefix) {
        decode_hex_bytes(hex).unwrap_or_else(|| tok.to_string())
    } else {
        tok.to_string()
    }
}

fn spec_decode_int_token(spec: &AtomEncodingSpec, tok: &str) -> String {
    match &spec.int_encoding {
        IntEncoding::Prefixed { prefix, neg_marker } => {
            if let Some(rest) = tok.strip_prefix(prefix.as_str()) {
                if let Some(num) = rest.strip_prefix(neg_marker.as_str()) {
                    return format!("-{num}");
                }
                return rest.to_string();
            }
            tok.to_string()
        }
    }
}

fn spec_decode_string_token(spec: &AtomEncodingSpec, tok: &str) -> String {
    match &spec.string_encoding {
        StringEncoding::Prefixed { prefix } => {
            if let Some(rest) = tok.strip_prefix(prefix.as_str()) {
                return format!("\"{rest}\"");
            }
        }
        StringEncoding::HexPrefixed { prefix } => {
            if let Some(hex) = tok.strip_prefix(prefix.as_str()) {
                if let Some(decoded) = decode_hex_bytes(hex) {
                    return format!("\"{decoded}\"");
                }
            }
        }
    }
    format!("\"{tok}\"")
}

fn spec_try_decode_cons_list(
    spec: &AtomEncodingSpec,
    display: &DisplayProfile,
    atom: &str,
) -> Option<String> {
    let mut items = Vec::new();
    let mut cur = atom.trim();
    let cons_prefix = format!("C_{}", spec.expr_cons);
    let nil_tag = format!("C_{}", spec.expr_nil);

    loop {
        if cur == nil_tag {
            break;
        }
        let inner = strip_wrapper(cur, &cons_prefix)?;
        let args = split_top_level_args(inner);
        if args.len() != 2 {
            return None;
        }
        items.push(spec_decode_atom(spec, display, args[0]));
        cur = args[1].trim();
    }

    if items.is_empty() {
        Some("()".to_string())
    } else {
        Some(format!("({})", items.join(" ")))
    }
}

// ═══════════════════════════════════════════════════════════════════════
//  Lowering: surface → HE core
// ═══════════════════════════════════════════════════════════════════════

/// Lower a surface `!expr` into the HE initial state term.
///
/// Returns a single core term string (HE is deterministic at lowering time).
/// The surface rewriter is NOT invoked — all semantics come from Ascent.
pub fn he_lower_eval(expr: &SExpr, space_state: &SurfaceSpaceState) -> Result<String, String> {
    let atom = he_encode_sexpr(expr)?;
    let space = he_build_space(space_state);
    Ok(format!("C_State(C_Metta({atom},C_UndefinedType),{space},C_Empty)"))
}

/// Encode a surface SExpr as an HE Atom term string.
pub fn he_encode_sexpr(expr: &SExpr) -> Result<String, String> {
    match expr {
        SExpr::Atom(s) => he_encode_atom(s),
        SExpr::List(items) => {
            if items.is_empty() {
                return Ok("C_ExprNil".to_string());
            }
            he_encode_expr_list(items)
        },
    }
}

fn he_encode_atom(s: &str) -> Result<String, String> {
    // Booleans
    if s == "True" || s == "true" {
        return Ok("C_True".to_string());
    }
    if s == "False" || s == "false" {
        return Ok("C_False".to_string());
    }

    // Integer literal — encode with C_ prefix so parse_int_token can strip it.
    // Token goes directly in C_GInt (not wrapped in C_SymAtom) because
    // parse_int_token calls token_name_from_atom which expects AVar, not C_SymAtom.
    if let Some(n) = try_parse_int(s) {
        let tok = if n < 0 {
            format!("C_neg_{}", -n)
        } else {
            format!("C_{n}")
        };
        return Ok(format!("C_GInt({tok})"));
    }

    // String literal (quoted) — encode with s_ prefix for parser compatibility
    // Token goes directly in C_GString (not wrapped in C_SymAtom).
    // Use hex escaping so arbitrary characters remain parser-safe.
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        let inner = &s[1..s.len() - 1];
        let tok = encode_string_token(inner);
        return Ok(format!("C_GString({tok})"));
    }

    // Variable
    if s.starts_with('$') && s.len() > 1 {
        return Ok(format!("C_VarAtom(C_SymAtom({}))", encode_symbol_token(&s[1..])));
    }

    // Type keywords
    match s {
        "Atom" => return Ok("C_AtomType".to_string()),
        "Symbol" => return Ok("C_SymbolType".to_string()),
        "Variable" => return Ok("C_VariableType".to_string()),
        "Expression" => return Ok("C_ExpressionType".to_string()),
        "Grounded" => return Ok("C_GroundedType".to_string()),
        "%Undefined%" => return Ok("C_UndefinedType".to_string()),
        _ => {},
    }

    // Grounded operators
    match s {
        "+" => return Ok("C_OpAdd".to_string()),
        "-" => return Ok("C_OpSub".to_string()),
        "*" => return Ok("C_OpMul".to_string()),
        "/" => return Ok("C_OpDiv".to_string()),
        "%" => return Ok("C_OpMod".to_string()),
        "<" => return Ok("C_OpLt".to_string()),
        ">" => return Ok("C_OpGt".to_string()),
        "==" => return Ok("C_OpEq".to_string()),
        _ => {},
    }

    // Regular symbol. Escape names that include parser-hostile characters
    // (e.g. '&self', 'find-equal').
    Ok(format!("C_SymAtom({})", encode_symbol_token(s)))
}

fn he_encode_expr_list(items: &[SExpr]) -> Result<String, String> {
    // Special forms
    if let Some(SExpr::Atom(head)) = items.first() {
        // (-> argType retType) → C_ArrowType(argType, retType)
        if items.len() == 3 && (head == "->" || head == "→") {
            let arg = he_encode_sexpr(&items[1])?;
            let ret = he_encode_sexpr(&items[2])?;
            return Ok(format!("C_ArrowType({arg},{ret})"));
        }

        // (let pattern expr body) → (case expr ((pattern body)))
        if items.len() == 4 && head == "let" {
            let case_expr = SExpr::List(vec![
                SExpr::Atom("case".into()),
                items[2].clone(),
                SExpr::List(vec![SExpr::List(vec![items[1].clone(), items[3].clone()])]),
            ]);
            return he_encode_sexpr(&case_expr);
        }

        // (let* ((v1 e1) (v2 e2) ...) body) → nested (let v1 e1 (let v2 e2 ... body))
        if items.len() == 3 && (head == "let*" || head == "let\\*") {
            if let SExpr::List(bindings) = &items[1] {
                let body = &items[2];
                return he_encode_let_star(bindings, body);
            }
        }
    }

    // General expression: fold into C_ExprCons chain
    let mut acc = "C_ExprNil".to_string();
    for item in items.iter().rev() {
        let encoded = he_encode_sexpr(item)?;
        acc = format!("C_ExprCons({encoded},{acc})");
    }
    Ok(acc)
}

/// Desugar let* bindings to nested let/case expressions.
fn he_encode_let_star(bindings: &[SExpr], body: &SExpr) -> Result<String, String> {
    if bindings.is_empty() {
        return he_encode_sexpr(body);
    }
    // Extract first binding (pattern expr)
    let first = &bindings[0];
    let SExpr::List(pair) = first else {
        return Err(format!("let* binding must be a list, got: {:?}", first));
    };
    if pair.len() != 2 {
        return Err(format!("let* binding must have 2 elements, got {}", pair.len()));
    }
    let pattern = &pair[0];
    let expr = &pair[1];

    // Build inner body: if more bindings, recurse; otherwise use body directly
    let inner_body = if bindings.len() == 1 {
        body.clone()
    } else {
        SExpr::List(vec![
            SExpr::Atom("let*".into()),
            SExpr::List(bindings[1..].to_vec()),
            body.clone(),
        ])
    };

    // Desugar to (let pattern expr inner_body) → (case expr ((pattern inner_body)))
    let case_expr = SExpr::List(vec![
        SExpr::Atom("case".into()),
        expr.clone(),
        SExpr::List(vec![SExpr::List(vec![pattern.clone(), inner_body])]),
    ]);
    he_encode_sexpr(&case_expr)
}

fn try_parse_int(s: &str) -> Option<i64> {
    s.parse::<i64>().ok()
}

// ═══════════════════════════════════════════════════════════════════════
//  Space building
// ═══════════════════════════════════════════════════════════════════════

/// Build the HE Space term from the session's space state.
///
/// Space contains equation entries and type entries as a list of atoms.
pub fn he_build_space(space_state: &SurfaceSpaceState) -> String {
    let mut atoms = Vec::new();

    // Add equation entries: (= lhs rhs) → C_EqAtom(lhs, rhs)
    for (lhs, rhs) in &space_state.eq_entries {
        atoms.push(format!("C_EqAtom({lhs},{rhs})"));
    }
    // Add pattern equation entries too
    for (lhs, rhs) in &space_state.pattern_eq_entries {
        atoms.push(format!("C_EqAtom({lhs},{rhs})"));
    }

    // Add type entries: (: atom ty) → C_TypeAnnotation(atom, ty)
    for (atom, ty) in &space_state.type_entries {
        atoms.push(format!("C_TypeAnnotation({atom},{ty})"));
    }

    // Bootstrap `if` as equation-defined function (HE spec):
    //   (= (if True  $then $else) $then)
    //   (= (if False $then $else) $else)
    //   (: if (-> Bool Atom Atom $t))
    // The Atom-typed branch positions prevent eager evaluation of $then/$else.
    atoms.push(
        "C_EqAtom(\
         C_ExprCons(C_SymAtom(if),C_ExprCons(C_True,C_ExprCons(C_VarAtom(C_SymAtom(then)),\
         C_ExprCons(C_VarAtom(C_SymAtom(else)),C_ExprNil)))),\
         C_VarAtom(C_SymAtom(then)))"
            .to_string(),
    );
    atoms.push(
        "C_EqAtom(\
         C_ExprCons(C_SymAtom(if),C_ExprCons(C_False,C_ExprCons(C_VarAtom(C_SymAtom(then)),\
         C_ExprCons(C_VarAtom(C_SymAtom(else)),C_ExprNil)))),\
         C_VarAtom(C_SymAtom(else)))"
            .to_string(),
    );
    // Type annotation: (: if (-> Bool Atom Atom $t))
    atoms.push(
        "C_TypeAnnotation(C_SymAtom(if),\
         C_ArrowType(C_GroundedType,\
         C_ArrowType(C_AtomType,\
         C_ArrowType(C_AtomType,\
         C_VarAtom(C_SymAtom(t))))))"
            .to_string(),
    );

    // Control flow type annotations.
    // These ensure applicableFuncType succeeds so expressions enter the
    // InterpFunc → InterpArgs → MettaCall pipeline (contract-driven dispatch).

    // (: superpose (-> Expression $t))
    atoms.push(
        "C_TypeAnnotation(C_SymAtom(superpose),\
         C_ArrowType(C_ExpressionType,\
         C_VarAtom(C_SymAtom(t))))"
            .to_string(),
    );

    // (: case (-> Atom Expression $t))
    atoms.push(
        "C_TypeAnnotation(C_SymAtom(case),\
         C_ArrowType(C_AtomType,\
         C_ArrowType(C_ExpressionType,\
         C_VarAtom(C_SymAtom(t)))))"
            .to_string(),
    );

    // (: match (-> Atom Atom Atom $t))
    atoms.push(
        "C_TypeAnnotation(C_SymAtom(match),\
         C_ArrowType(C_AtomType,\
         C_ArrowType(C_AtomType,\
         C_ArrowType(C_AtomType,\
         C_VarAtom(C_SymAtom(t))))))"
            .to_string(),
    );

    // (: unify (-> Atom Atom Atom Atom $t))
    atoms.push(
        "C_TypeAnnotation(C_SymAtom(unify),\
         C_ArrowType(C_AtomType,\
         C_ArrowType(C_AtomType,\
         C_ArrowType(C_AtomType,\
         C_ArrowType(C_AtomType,\
         C_VarAtom(C_SymAtom(t)))))))"
            .to_string(),
    );

    // (: collapse (-> Atom Expression))
    atoms.push(
        "C_TypeAnnotation(C_SymAtom(collapse),\
         C_ArrowType(C_AtomType,\
         C_ExpressionType))"
            .to_string(),
    );

    // Fold into ExprCons list
    let mut list = "C_ExprNil".to_string();
    for atom in atoms.iter().rev() {
        list = format!("C_ExprCons({atom},{list})");
    }

    format!("C_Space({list})")
}

/// Bootstrap type annotations for HE grounded operators.
///
/// Returns (atom_encoded, type_encoded) pairs ready for space_state.type_entries.
pub fn he_bootstrap_type_entries() -> Vec<(String, String)> {
    let arith_type = "C_ArrowType(C_GroundedType,C_GroundedType)".to_string();
    vec![
        ("C_OpAdd".to_string(), arith_type.clone()),
        ("C_OpSub".to_string(), arith_type.clone()),
        ("C_OpMul".to_string(), arith_type.clone()),
        ("C_OpDiv".to_string(), arith_type.clone()),
        ("C_OpMod".to_string(), arith_type.clone()),
        ("C_OpLt".to_string(), arith_type.clone()),
        ("C_OpGt".to_string(), arith_type.clone()),
        ("C_OpEq".to_string(), arith_type),
    ]
}

// ═══════════════════════════════════════════════════════════════════════
//  Decoding: HE core result → surface display
// ═══════════════════════════════════════════════════════════════════════

/// Decode an HE core atom (extracted from C_State's out field) to surface syntax.
pub fn he_decode_atom(core_atom: &str) -> String {
    let atom = core_atom.trim();

    // Nullary constants
    match atom {
        "C_Empty" => return "()".to_string(),
        "C_True" => return "True".to_string(),
        "C_False" => return "False".to_string(),
        "C_AtomType" => return "Atom".to_string(),
        "C_SymbolType" => return "Symbol".to_string(),
        "C_VariableType" => return "Variable".to_string(),
        "C_ExpressionType" => return "Expression".to_string(),
        "C_GroundedType" => return "Grounded".to_string(),
        "C_UndefinedType" => return "%Undefined%".to_string(),
        "C_StackOverflow" => return "(Error StackOverflow)".to_string(),
        "C_NoReturn" => return "(Error NoReturn)".to_string(),
        "C_IncorrectNumberOfArguments" => return "(Error IncorrectNumberOfArguments)".to_string(),
        "C_ExprNil" => return "()".to_string(),
        "C_OpAdd" => return "+".to_string(),
        "C_OpSub" => return "-".to_string(),
        "C_OpMul" => return "*".to_string(),
        "C_OpDiv" => return "/".to_string(),
        "C_OpMod" => return "%".to_string(),
        "C_OpLt" => return "<".to_string(),
        "C_OpGt" => return ">".to_string(),
        "C_OpEq" => return "==".to_string(),
        "C_Done" => return "Done".to_string(),
        _ => {},
    }

    // C_SymAtom(name) → name
    if let Some(inner) = strip_wrapper(atom, "C_SymAtom") {
        return decode_symbol_token(inner);
    }

    // C_VarAtom(C_SymAtom(name)) → $name
    if let Some(inner) = strip_wrapper(atom, "C_VarAtom") {
        if let Some(name) = strip_wrapper(inner, "C_SymAtom") {
            return format!("${}", decode_symbol_token(name));
        }
        return format!("${}", decode_symbol_token(inner));
    }

    // C_GInt(C_42) → 42, C_GInt(C_neg_42) → -42
    // The inner token is a bare AVar (not wrapped in C_SymAtom)
    if let Some(inner) = strip_wrapper(atom, "C_GInt") {
        return decode_var_display(inner);
    }

    // C_GString(s_hello) → "hello"
    if let Some(inner) = strip_wrapper(atom, "C_GString") {
        let decoded = decode_var_display(inner);
        if let Some(rest) = decoded.strip_prefix("strhex_") {
            return format!("\"{}\"", decode_hex_bytes(rest).unwrap_or_else(|| rest.to_string()));
        }
        if let Some(rest) = decoded.strip_prefix("s_") {
            return format!("\"{rest}\"");
        }
        return format!("\"{decoded}\"");
    }

    // C_GBool(C_SymAtom(b)) or C_GBool(C_True/C_False) → boolean surface token
    if let Some(inner) = strip_wrapper(atom, "C_GBool") {
        if let Some(b) = strip_wrapper(inner, "C_SymAtom") {
            return b.to_string();
        }
        if inner == "C_True" {
            return "True".to_string();
        }
        if inner == "C_False" {
            return "False".to_string();
        }
        return inner.to_string();
    }

    // C_ErrorAtom(src, code) → (Error decoded_src decoded_code)
    if let Some(inner) = strip_wrapper(atom, "C_ErrorAtom") {
        let args = split_top_level_args(inner);
        if args.len() == 2 {
            let src = he_decode_atom(args[0]);
            let code = he_decode_atom(args[1]);
            return format!("(Error {src} {code})");
        }
    }

    // C_BadType(expected, actual) → (BadType ...)
    if let Some(inner) = strip_wrapper(atom, "C_BadType") {
        let args = split_top_level_args(inner);
        if args.len() == 2 {
            let expected = he_decode_atom(args[0]);
            let actual = he_decode_atom(args[1]);
            return format!("(BadType {expected} {actual})");
        }
    }

    // C_ArrowType(args, ret) → (-> args ret)
    if let Some(inner) = strip_wrapper(atom, "C_ArrowType") {
        let args = split_top_level_args(inner);
        if args.len() == 2 {
            let a = he_decode_atom(args[0]);
            let r = he_decode_atom(args[1]);
            return format!("(-> {a} {r})");
        }
    }

    // C_TypeAnnotation(atom, ty) → (: atom ty)
    if let Some(inner) = strip_wrapper(atom, "C_TypeAnnotation") {
        let args = split_top_level_args(inner);
        if args.len() == 2 {
            let a = he_decode_atom(args[0]);
            let t = he_decode_atom(args[1]);
            return format!("(: {a} {t})");
        }
    }

    // C_EqAtom(lhs, rhs) → (= lhs rhs)
    if let Some(inner) = strip_wrapper(atom, "C_EqAtom") {
        let args = split_top_level_args(inner);
        if args.len() == 2 {
            let l = he_decode_atom(args[0]);
            let r = he_decode_atom(args[1]);
            return format!("(= {l} {r})");
        }
    }

    // C_ExprCons(head, tail) → decode as list
    if let Some(list) = try_decode_he_cons_list(atom) {
        return list;
    }

    // Fallback: return as-is
    atom.to_string()
}

// ═══════════════════════════════════════════════════════════════════════
//  Helpers
// ═══════════════════════════════════════════════════════════════════════

/// Try to decode a display string that came from a free variable (AVar).
/// The runtime renders these as just the pretty_name, so we extract it.
fn decode_var_display(s: &str) -> String {
    let trimmed = s.trim();
    // If it's a C_ encoded token, decode it
    if let Some(rest) = trimmed.strip_prefix("C_neg_") {
        return format!("-{rest}");
    }
    if let Some(rest) = trimmed.strip_prefix("C_") {
        return rest.to_string();
    }
    trimmed.to_string()
}

fn is_safe_ident(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }
    chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

fn encode_hex_bytes(s: &str) -> String {
    let mut out = String::with_capacity(s.len() * 2);
    for b in s.as_bytes() {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

fn decode_hex_bytes(hex: &str) -> Option<String> {
    if !hex.len().is_multiple_of(2) {
        return None;
    }
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    let mut i = 0;
    while i < hex.len() {
        let byte = u8::from_str_radix(&hex[i..i + 2], 16).ok()?;
        bytes.push(byte);
        i += 2;
    }
    String::from_utf8(bytes).ok()
}

fn encode_symbol_token(s: &str) -> String {
    if is_safe_ident(s) {
        s.to_string()
    } else {
        format!("symhex_{}", encode_hex_bytes(s))
    }
}

fn decode_symbol_token(tok: &str) -> String {
    if let Some(hex) = tok.strip_prefix("symhex_") {
        decode_hex_bytes(hex).unwrap_or_else(|| tok.to_string())
    } else {
        tok.to_string()
    }
}

fn encode_string_token(s: &str) -> String {
    format!("strhex_{}", encode_hex_bytes(s))
}

/// Strip `Prefix(...)` wrapper, returning the inner content.
fn strip_wrapper<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    let with_paren = format!("{prefix}(");
    let inner = s.strip_prefix(&with_paren)?.strip_suffix(')')?;
    Some(inner.trim())
}

/// Split comma-separated args at the top level (respecting nested parens).
fn split_top_level_args(s: &str) -> Vec<&str> {
    let mut args = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                args.push(s[start..i].trim());
                start = i + 1;
            },
            _ => {},
        }
    }
    let last = s[start..].trim();
    if !last.is_empty() {
        args.push(last);
    }
    args
}

/// Decode a C_ExprCons chain into surface list notation.
fn try_decode_he_cons_list(atom: &str) -> Option<String> {
    let mut items = Vec::new();
    let mut cur = atom.trim();

    loop {
        if cur == "C_ExprNil" {
            break;
        }
        let inner = strip_wrapper(cur, "C_ExprCons")?;
        let args = split_top_level_args(inner);
        if args.len() != 2 {
            return None;
        }
        items.push(he_decode_atom(args[0]));
        cur = args[1].trim();
    }

    if items.is_empty() {
        Some("()".to_string())
    } else {
        Some(format!("({})", items.join(" ")))
    }
}

// ═══════════════════════════════════════════════════════════════════════
//  HE-specific state extraction
// ═══════════════════════════════════════════════════════════════════════

/// Extract the output atom from an HE C_State term.
/// Same structure as legacy: C_State(instr, space, OUT) — third field.
pub fn he_extract_state_out_atom(core_state_term: &str) -> Option<String> {
    let trimmed = core_state_term.trim();
    // Trim possible leading/trailing whitespace in the Display format
    let trimmed = trimmed.strip_prefix("C_State(")?.strip_suffix(')')?;
    let args = split_top_level_args(trimmed);
    if args.len() == 3 {
        Some(args[2].trim().to_string())
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_symbol() {
        assert_eq!(
            he_encode_sexpr(&SExpr::Atom("foo".into())).unwrap(),
            "C_SymAtom(foo)"
        );
    }

    #[test]
    fn encode_symbol_with_hyphen() {
        assert_eq!(
            he_encode_sexpr(&SExpr::Atom("find-equal".into())).unwrap(),
            "C_SymAtom(symhex_66696e642d657175616c)"
        );
    }

    #[test]
    fn encode_symbol_with_ampersand() {
        assert_eq!(
            he_encode_sexpr(&SExpr::Atom("&self".into())).unwrap(),
            "C_SymAtom(symhex_2673656c66)"
        );
    }

    #[test]
    fn encode_integer() {
        assert_eq!(he_encode_sexpr(&SExpr::Atom("42".into())).unwrap(), "C_GInt(C_42)");
    }

    #[test]
    fn encode_negative_integer() {
        assert_eq!(he_encode_sexpr(&SExpr::Atom("-7".into())).unwrap(), "C_GInt(C_neg_7)");
    }

    #[test]
    fn encode_variable() {
        assert_eq!(he_encode_sexpr(&SExpr::Atom("$x".into())).unwrap(), "C_VarAtom(C_SymAtom(x))");
    }

    #[test]
    fn encode_expression() {
        let expr = SExpr::List(vec![
            SExpr::Atom("+".into()),
            SExpr::Atom("1".into()),
            SExpr::Atom("2".into()),
        ]);
        assert_eq!(
            he_encode_sexpr(&expr).unwrap(),
            "C_ExprCons(C_OpAdd,C_ExprCons(C_GInt(C_1),C_ExprCons(C_GInt(C_2),C_ExprNil)))"
        );
    }

    #[test]
    fn decode_symbol() {
        assert_eq!(he_decode_atom("C_SymAtom(foo)"), "foo");
    }

    #[test]
    fn decode_escaped_symbol() {
        assert_eq!(
            he_decode_atom("C_SymAtom(symhex_66696e642d657175616c)"),
            "find-equal"
        );
    }

    #[test]
    fn decode_integer() {
        assert_eq!(he_decode_atom("C_GInt(C_42)"), "42");
    }

    #[test]
    fn decode_negative_integer() {
        assert_eq!(he_decode_atom("C_GInt(C_neg_7)"), "-7");
    }

    #[test]
    fn decode_expr_cons_list() {
        assert_eq!(
            he_decode_atom(
                "C_ExprCons(C_SymAtom(a),C_ExprCons(C_SymAtom(b),C_ExprNil))"
            ),
            "(a b)"
        );
    }

    #[test]
    fn decode_error() {
        assert_eq!(
            he_decode_atom(
                "C_ErrorAtom(C_SymAtom(x),C_BadType(C_AtomType,C_SymbolType))"
            ),
            "(Error x (BadType Atom Symbol))"
        );
    }

    #[test]
    fn roundtrip_simple() {
        let expr = SExpr::Atom("42".into());
        let encoded = he_encode_sexpr(&expr).unwrap();
        assert_eq!(encoded, "C_GInt(C_42)");
        assert_eq!(he_decode_atom(&encoded), "42");
    }

    // ═══════════════════════════════════════════════════════════════════
    //  Spec-driven encoder/decoder parity tests
    // ═══════════════════════════════════════════════════════════════════

    fn test_spec() -> AtomEncodingSpec {
        crate::syntax_spec::try_load_atom_encoding("he")
            .expect("load should succeed")
            .expect("he atom encoding should be found")
            .spec
    }

    fn test_display() -> DisplayProfile {
        crate::syntax_spec::try_load_display_profile("he")
            .expect("load should succeed")
            .expect("he display profile should be found")
            .profile
    }

    #[test]
    fn spec_encode_parity_symbol() {
        let spec = test_spec();
        let expr = SExpr::Atom("foo".into());
        assert_eq!(
            spec_encode_sexpr(&spec, &expr).unwrap(),
            he_encode_sexpr(&expr).unwrap()
        );
    }

    #[test]
    fn spec_encode_parity_escaped_symbol() {
        let spec = test_spec();
        let expr = SExpr::Atom("find-equal".into());
        assert_eq!(
            spec_encode_sexpr(&spec, &expr).unwrap(),
            he_encode_sexpr(&expr).unwrap()
        );
    }

    #[test]
    fn spec_encode_parity_variable() {
        let spec = test_spec();
        let expr = SExpr::Atom("$x".into());
        assert_eq!(
            spec_encode_sexpr(&spec, &expr).unwrap(),
            he_encode_sexpr(&expr).unwrap()
        );
    }

    #[test]
    fn spec_encode_parity_integer() {
        let spec = test_spec();
        for val in &["42", "-7", "0"] {
            let expr = SExpr::Atom(val.to_string());
            assert_eq!(
                spec_encode_sexpr(&spec, &expr).unwrap(),
                he_encode_sexpr(&expr).unwrap(),
                "mismatch for integer {val}"
            );
        }
    }

    #[test]
    fn spec_encode_parity_string() {
        let spec = test_spec();
        let expr = SExpr::Atom("\"hello\"".into());
        assert_eq!(
            spec_encode_sexpr(&spec, &expr).unwrap(),
            he_encode_sexpr(&expr).unwrap()
        );
    }

    #[test]
    fn spec_encode_parity_boolean() {
        let spec = test_spec();
        for val in &["True", "true", "False", "false"] {
            let expr = SExpr::Atom(val.to_string());
            assert_eq!(
                spec_encode_sexpr(&spec, &expr).unwrap(),
                he_encode_sexpr(&expr).unwrap(),
                "mismatch for boolean {val}"
            );
        }
    }

    #[test]
    fn spec_encode_parity_operators() {
        let spec = test_spec();
        for op in &["+", "-", "*", "/", "%", "<", ">", "=="] {
            let expr = SExpr::Atom(op.to_string());
            assert_eq!(
                spec_encode_sexpr(&spec, &expr).unwrap(),
                he_encode_sexpr(&expr).unwrap(),
                "mismatch for operator {op}"
            );
        }
    }

    #[test]
    fn spec_encode_parity_type_keywords() {
        let spec = test_spec();
        for kw in &[
            "Atom",
            "Symbol",
            "Variable",
            "Expression",
            "Grounded",
            "%Undefined%",
        ] {
            let expr = SExpr::Atom(kw.to_string());
            assert_eq!(
                spec_encode_sexpr(&spec, &expr).unwrap(),
                he_encode_sexpr(&expr).unwrap(),
                "mismatch for type keyword {kw}"
            );
        }
    }

    #[test]
    fn spec_encode_parity_expression() {
        let spec = test_spec();
        let expr = SExpr::List(vec![
            SExpr::Atom("+".into()),
            SExpr::Atom("1".into()),
            SExpr::Atom("2".into()),
        ]);
        assert_eq!(
            spec_encode_sexpr(&spec, &expr).unwrap(),
            he_encode_sexpr(&expr).unwrap()
        );
    }

    #[test]
    fn spec_encode_parity_arrow_type() {
        let spec = test_spec();
        let expr = SExpr::List(vec![
            SExpr::Atom("->".into()),
            SExpr::Atom("Atom".into()),
            SExpr::Atom("Symbol".into()),
        ]);
        assert_eq!(
            spec_encode_sexpr(&spec, &expr).unwrap(),
            he_encode_sexpr(&expr).unwrap()
        );
    }

    #[test]
    fn spec_decode_parity() {
        let spec = test_spec();
        let display = test_display();
        let cases = vec![
            "C_SymAtom(foo)",
            "C_SymAtom(symhex_66696e642d657175616c)",
            "C_VarAtom(C_SymAtom(x))",
            "C_GInt(C_42)",
            "C_GInt(C_neg_7)",
            "C_True",
            "C_False",
            "C_OpAdd",
            "C_AtomType",
            "C_ExprNil",
            "C_ArrowType(C_AtomType,C_SymbolType)",
            "C_ExprCons(C_SymAtom(a),C_ExprCons(C_SymAtom(b),C_ExprNil))",
            "C_ErrorAtom(C_SymAtom(x),C_BadType(C_AtomType,C_SymbolType))",
        ];
        for case in cases {
            assert_eq!(
                spec_decode_atom(&spec, &display, case),
                he_decode_atom(case),
                "decode mismatch for: {case}"
            );
        }
    }

    #[test]
    fn spec_roundtrip() {
        let spec = test_spec();
        let display = test_display();
        let exprs = vec![
            SExpr::Atom("42".into()),
            SExpr::Atom("foo".into()),
            SExpr::Atom("$x".into()),
            SExpr::Atom("\"hello\"".into()),
            SExpr::Atom("True".into()),
            SExpr::Atom("+".into()),
            SExpr::List(vec![
                SExpr::Atom("->".into()),
                SExpr::Atom("Atom".into()),
                SExpr::Atom("Symbol".into()),
            ]),
        ];
        for expr in exprs {
            let encoded = spec_encode_sexpr(&spec, &expr).unwrap();
            let decoded = spec_decode_atom(&spec, &display, &encoded);
            let expected = match &expr {
                SExpr::Atom(s) => s.clone(),
                SExpr::List(_) => {
                    // For arrow type, expected display is "(-> Atom Symbol)"
                    he_decode_atom(&he_encode_sexpr(&expr).unwrap())
                }
            };
            assert_eq!(decoded, expected, "roundtrip failed for: {:?}", expr);
        }
    }
}
