language! {
    name: MeTTaHE,

    types {
        State
        Instr
        Atom
        Space
    },

    terms {
        C_State . instr:Instr, space:Space, out:Atom |- "C_State" "(" instr "," space "," out ")" : State;
        C_Metta . atom:Atom, ty:Atom |- "C_Metta" "(" atom "," ty ")" : Instr;
        C_InterpExpr . atom:Atom, ty:Atom |- "C_InterpExpr" "(" atom "," ty ")" : Instr;
        C_InterpFunc . atom:Atom, opType:Atom, retType:Atom |- "C_InterpFunc" "(" atom "," opType "," retType ")" : Instr;
        C_InterpArgs . head:Atom, rest:Atom, types:Atom |- "C_InterpArgs" "(" head "," rest "," types ")" : Instr;
        C_InterpTuple . atom:Atom |- "C_InterpTuple" "(" atom ")" : Instr;
        C_MettaCall . atom:Atom, ty:Atom |- "C_MettaCall" "(" atom "," ty ")" : Instr;
        C_TypeCast . atom:Atom, ty:Atom |- "C_TypeCast" "(" atom "," ty ")" : Instr;
        C_Return . result:Atom |- "C_Return" "(" result ")" : Instr;
        C_Done . |- "C_Done" : Instr;
        C_Empty . |- "C_Empty" : Atom;
        C_ErrorAtom . source:Atom, code:Atom |- "C_ErrorAtom" "(" source "," code ")" : Atom;
        C_BadArgType . argpos:Atom, expected:Atom, actual:Atom |- "C_BadArgType" "(" argpos "," expected "," actual ")" : Atom;
        C_BadType . expected:Atom, actual:Atom |- "C_BadType" "(" expected "," actual ")" : Atom;
        C_StackOverflow . |- "C_StackOverflow" : Atom;
        C_NoReturn . |- "C_NoReturn" : Atom;
        C_IncorrectNumberOfArguments . |- "C_IncorrectNumberOfArguments" : Atom;
        C_True . |- "C_True" : Atom;
        C_False . |- "C_False" : Atom;
        C_SymbolType . |- "C_SymbolType" : Atom;
        C_VariableType . |- "C_VariableType" : Atom;
        C_ExpressionType . |- "C_ExpressionType" : Atom;
        C_GroundedType . |- "C_GroundedType" : Atom;
        C_AtomType . |- "C_AtomType" : Atom;
        C_UndefinedType . |- "C_UndefinedType" : Atom;
        C_ArrowType . args:Atom, ret:Atom |- "C_ArrowType" "(" args "," ret ")" : Atom;
        C_GInt . intTok:Atom |- "C_GInt" "(" intTok ")" : Atom;
        C_GString . strTok:Atom |- "C_GString" "(" strTok ")" : Atom;
        C_GBool . boolTok:Atom |- "C_GBool" "(" boolTok ")" : Atom;
        C_SymAtom . name:Atom |- "C_SymAtom" "(" name ")" : Atom;
        C_VarAtom . name:Atom |- "C_VarAtom" "(" name ")" : Atom;
        C_ExprCons . head:Atom, tail:Atom |- "C_ExprCons" "(" head "," tail ")" : Atom;
        C_ExprNil . |- "C_ExprNil" : Atom;
        C_OpAdd . |- "C_OpAdd" : Atom;
        C_OpSub . |- "C_OpSub" : Atom;
        C_OpMul . |- "C_OpMul" : Atom;
        C_OpDiv . |- "C_OpDiv" : Atom;
        C_OpMod . |- "C_OpMod" : Atom;
        C_OpLt . |- "C_OpLt" : Atom;
        C_OpGt . |- "C_OpGt" : Atom;
        C_OpEq . |- "C_OpEq" : Atom;
        C_EqAtom . left:Atom, right:Atom |- "C_EqAtom" "(" left "," right ")" : Atom;
        C_TypeAnnotation . atom:Atom, ty:Atom |- "C_TypeAnnotation" "(" atom "," ty ")" : Atom;
        C_Space . atoms:Atom |- "C_Space" "(" atoms ")" : Space;
    },

    equations {    },

    rewrites {
        R0 . | isEmpty(atom) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_Return atom) space atom);
        R1 . | isError(atom) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_Return atom) space atom);
        R2 . | typeMatchesMetaOrAtom(atom, ty) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_Return atom) space atom);
        R3 . | needsTypeCast(atom, ty) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_TypeCast atom ty) space out);
        R4 . | needsInterpExpr(atom, ty) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_InterpExpr atom ty) space out);
        R5 . | applicableFuncType(space, atom, ty, opType, retType) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_InterpFunc atom opType retType) space out);
        R6 . | needsTupleInterp(space, atom, ty) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_InterpTuple atom) space out);
        R7 . | notExpression(atom) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_Return atom) space atom);
        R8 . | interpFuncResult(space, atom, opType, retType, result) |- (C_State (C_InterpFunc atom opType retType) space out) ~> (C_State (C_MettaCall result retType) space out);
        R9 . | interpTupleResult(space, atom, result) |- (C_State (C_InterpTuple atom) space out) ~> (C_State (C_Return result) space result);
        R10 . | isError(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return atom) space atom);
        R11 . | groundedCallResult(space, atom, result) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta result ty) space out);
        R12 . | eqQueryResult(space, atom, rhs), notExecutable(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta rhs ty) space out);
        R13 . | noEqQuery(space, atom), notExecutable(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return atom) space atom);
        R14 . | typeOf(space, atom, ty) |- (C_State (C_TypeCast atom ty) space out) ~> (C_State (C_Return atom) space atom);
        R15 . | typeMismatch(space, atom, ty, actual) |- (C_State (C_TypeCast atom ty) space out) ~> (C_State (C_Return (C_ErrorAtom atom (C_BadType ty actual))) space (C_ErrorAtom atom (C_BadType ty actual)));
        R16 . |- (C_State (C_Return result) space out) ~> (C_State C_Done space result);
    },

    logic {
        // ═══ Domain extraction (auto-generated from LanguageDef.terms) ═══
        relation space(Space);
        relation atom(Atom);

        space(sp) <--
            state(st),
            if let State::C_State(_, ref f0, _) = st,
            let sp = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(_, _, ref f0) = st,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Metta(ref f0, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Metta(_, ref f0) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpExpr(ref f0, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpExpr(_, ref f0) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpFunc(ref f0, _, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpFunc(_, ref f0, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpFunc(_, _, ref f0) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpArgs(ref f0, _, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpArgs(_, ref f0, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpArgs(_, _, ref f0) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_InterpTuple(ref f0) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_MettaCall(ref f0, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_MettaCall(_, ref f0) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_TypeCast(ref f0, _) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_TypeCast(_, ref f0) = &**instr,
            let a = (**f0).clone();

        atom(a) <--
            state(st),
            if let State::C_State(ref instr, _, _) = st,
            if let Instr::C_Return(ref f0) = &**instr,
            let a = (**f0).clone();

        // ═══ Premise relation declarations ═══
        relation isEmpty(Atom);
        relation isError(Atom);
        relation metaType(Atom, Atom);
        relation typeMatchesMetaOrAtom(Atom, Atom);
        relation typeNotMatchesMetaOrAtom(Atom, Atom);
        relation needsTypeCast(Atom, Atom);
        relation needsInterpExpr(Atom, Atom);
        relation notExpression(Atom);
        relation isExecutable(Atom);
        relation notExecutable(Atom);
        relation typeOf(Space, Atom, Atom);
        relation typeMismatch(Space, Atom, Atom, Atom);
        relation eqQueryResult(Space, Atom, Atom);
        relation noEqQuery(Space, Atom);
        relation groundedCallResult(Space, Atom, Atom);
        relation applicableFuncType(Space, Atom, Atom, Atom, Atom);
        relation needsTupleInterp(Space, Atom, Atom);
        relation interpFuncResult(Space, Atom, Atom, Atom, Atom);
        relation interpTupleResult(Space, Atom, Atom);

        // ═══ Premise rules ═══

        // Atom-only rules: join against atom domain
        isEmpty(a) <--
            atom(a),
            if *a == Atom::C_Empty;

        isError(a) <--
            atom(a),
            if let Atom::C_ErrorAtom(_, _) = a;

        metaType(a, Atom::C_SymbolType) <--
            atom(a),
            if let Atom::C_SymAtom(_) = a;

        metaType(a, Atom::C_VariableType) <--
            atom(a),
            if let Atom::C_VarAtom(_) = a;

        metaType(a, Atom::C_ExpressionType) <--
            atom(a),
            if let Atom::C_ExprCons(_, _) = a;

        metaType(a, Atom::C_ExpressionType) <--
            atom(a),
            if *a == Atom::C_ExprNil;

        metaType(a, Atom::C_GroundedType) <--
            atom(a),
            if let Atom::C_GInt(_) = a;

        metaType(a, Atom::C_GroundedType) <--
            atom(a),
            if let Atom::C_GString(_) = a;

        metaType(a, Atom::C_GroundedType) <--
            atom(a),
            if let Atom::C_GBool(_) = a;

        // typeMatchesMetaOrAtom: atom matches AtomType (everything matches)
        typeMatchesMetaOrAtom(a, t) <--
            atom(a),
            atom(t),
            if *t == Atom::C_AtomType;

        // typeMatchesMetaOrAtom: meta-type of atom matches the requested type
        typeMatchesMetaOrAtom(a, t) <--
            metaType(a, t);

        // typeMatchesMetaOrAtom: variables match any type
        typeMatchesMetaOrAtom(a, t) <--
            atom(t),
            metaType(a, Atom::C_VariableType);

        // typeNotMatchesMetaOrAtom: explicit positive complement
        typeNotMatchesMetaOrAtom(a, t) <--
            atom(t),
            metaType(a, mt),
            if *t != Atom::C_AtomType,
            if *mt != Atom::C_VariableType,
            if *mt != *t;

        // needsTypeCast: symbol that doesn't match the type
        needsTypeCast(a, t) <--
            atom(t),
            metaType(a, Atom::C_SymbolType),
            typeNotMatchesMetaOrAtom(a, t),
            if !matches!(a, Atom::C_Empty),
            if !matches!(a, Atom::C_ErrorAtom(_, _));

        // needsTypeCast: grounded that doesn't match the type
        needsTypeCast(a, t) <--
            atom(t),
            metaType(a, Atom::C_GroundedType),
            typeNotMatchesMetaOrAtom(a, t),
            if !matches!(a, Atom::C_Empty),
            if !matches!(a, Atom::C_ErrorAtom(_, _));

        // needsTypeCast: unit expression that doesn't match the type
        needsTypeCast(a, t) <--
            atom(a),
            atom(t),
            if *a == Atom::C_ExprNil,
            typeNotMatchesMetaOrAtom(a, t),
            if !matches!(a, Atom::C_Empty),
            if !matches!(a, Atom::C_ErrorAtom(_, _));

        // needsInterpExpr: expression that doesn't match
        needsInterpExpr(a, t) <--
            atom(t),
            metaType(a, Atom::C_ExpressionType),
            typeNotMatchesMetaOrAtom(a, t),
            if !matches!(a, Atom::C_Empty),
            if !matches!(a, Atom::C_ErrorAtom(_, _));

        // notExpression: atom whose meta-type isn't ExpressionType
        notExpression(a) <--
            metaType(a, mt),
            if *mt != Atom::C_ExpressionType;

        // isExecutable: grounded builtin operator
        isExecutable(a) <--
            atom(a),
            if let Some(_) = is_executable_grounded(&a);

        // notExecutable: positive check
        notExecutable(a) <--
            atom(a),
            if is_executable_grounded(&a).is_none();

        // typeOf: find type annotation in space
        typeOf(sp, a, ty) <--
            space(sp),
            atom(a),
            if let Space::C_Space(ref atoms0) = sp,
            let atoms = (**atoms0).clone(),
            if let Some(ty) = find_type_annotation(atoms, a.clone());

        // typeMismatch: type annotation exists but doesn't match
        typeMismatch(sp, a, expected, actual) <--
            atom(expected),
            typeOf(sp, a, actual),
            if *actual != *expected;

        // eqQueryResult: equation match in space (nondeterministic — all matches)
        eqQueryResult(sp, a, rhs) <--
            space(sp),
            atom(a),
            if let Space::C_Space(ref atoms0) = sp,
            let atoms = (**atoms0).clone(),
            for rhs in query_equations_all(atoms, a.clone()).into_iter();

        // noEqQuery: no equation matches (cheap existence check)
        noEqQuery(sp, a) <--
            space(sp),
            atom(a),
            if let Space::C_Space(ref atoms0) = sp,
            if !has_equation_match(atoms0.as_ref(), &a);

        // groundedCallResult: dispatch grounded call
        groundedCallResult(sp, a, result) <--
            space(sp),
            atom(a),
            if let Some(result) = try_grounded_dispatch(&a);

        // applicableFuncType: find applicable function type from space
        applicableFuncType(sp, a, t, opType, retType) <--
            space(sp),
            atom(a),
            atom(t),
            if let Some((opType, retType)) = find_applicable_func_type_pair(sp.clone(), a.clone(), t.clone());

        // needsTupleInterp: no func type, but has non-func types
        needsTupleInterp(sp, a, t) <--
            space(sp),
            atom(a),
            atom(t),
            if find_applicable_func_type(sp.clone(), a.clone(), t.clone()).is_none(),
            if let Some(_) = has_non_func_types(sp.clone(), a.clone());

        // interpFuncResult: evaluate function application
        interpFuncResult(sp, a, opType, retType, result) <--
            applicableFuncType(sp, a, _, opType, retType),
            if let Some(result) = eval_interp_func(sp.clone(), a.clone(), opType.clone(), retType.clone());

        // interpTupleResult: evaluate tuple
        interpTupleResult(sp, a, result) <--
            space(sp),
            atom(a),
            if let Some(result) = eval_interp_tuple(sp.clone(), a.clone());
    }
}

#[cfg(test)]
mod pattern_tests {
    use super::*;

    #[test]
    fn var_matches_any_atom_and_captures() {
        let pat = Atom::C_VarAtom(Box::new(make_token_atom("x".into())));
        let concrete = make_int_atom(5);
        let bindings = he_match(&pat, &concrete).expect("should match");
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].0, "x");
        assert_eq!(bindings[0].1, concrete);
    }

    #[test]
    fn expr_pattern_matches_with_var() {
        // (double $x) vs (double 5)
        let pat = encode_expr_list(&[
            Atom::C_SymAtom(Box::new(make_token_atom("double".into()))),
            Atom::C_VarAtom(Box::new(make_token_atom("x".into()))),
        ]);
        let concrete = encode_expr_list(&[
            Atom::C_SymAtom(Box::new(make_token_atom("double".into()))),
            make_int_atom(5),
        ]);
        let bindings = he_match(&pat, &concrete).expect("should match");
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].0, "x");
        assert_eq!(bindings[0].1, make_int_atom(5));
    }

    #[test]
    fn subst_replaces_vars_in_rhs() {
        // rhs = (+ $x $x), bindings = {x -> 5}
        let rhs = encode_expr_list(&[
            Atom::C_OpAdd,
            Atom::C_VarAtom(Box::new(make_token_atom("x".into()))),
            Atom::C_VarAtom(Box::new(make_token_atom("x".into()))),
        ]);
        let bindings = vec![("x".to_string(), make_int_atom(5))];
        let result = he_subst(&rhs, &bindings);
        let items = decode_expr_list(&result).expect("should decode");
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], Atom::C_OpAdd);
        assert_eq!(items[1], make_int_atom(5));
        assert_eq!(items[2], make_int_atom(5));
    }

    #[test]
    fn mismatched_symbol_fails() {
        let pat = Atom::C_SymAtom(Box::new(make_token_atom("foo".into())));
        let concrete = Atom::C_SymAtom(Box::new(make_token_atom("bar".into())));
        assert!(he_match(&pat, &concrete).is_none());
    }

    #[test]
    fn same_var_twice_requires_consistent_binding() {
        // ($x $x) vs (5 5) -> should match
        let pat = encode_expr_list(&[
            Atom::C_VarAtom(Box::new(make_token_atom("x".into()))),
            Atom::C_VarAtom(Box::new(make_token_atom("x".into()))),
        ]);
        let good = encode_expr_list(&[make_int_atom(5), make_int_atom(5)]);
        assert!(he_match(&pat, &good).is_some());

        // ($x $x) vs (5 6) -> should fail
        let bad = encode_expr_list(&[make_int_atom(5), make_int_atom(6)]);
        assert!(he_match(&pat, &bad).is_none());
    }
}
