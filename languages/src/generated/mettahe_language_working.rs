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
        C_KAfterOp . argsTail:Atom, opType:Atom, retType:Atom, kont:Atom |- "C_KAfterOp" "(" argsTail "," opType "," retType "," kont ")" : Atom;
        C_KAfterArgs . head:Atom, retType:Atom, kont:Atom |- "C_KAfterArgs" "(" head "," retType "," kont ")" : Atom;
        C_KTupleTail . tail:Atom, kont:Atom |- "C_KTupleTail" "(" tail "," kont ")" : Atom;
        C_KTupleCons . head:Atom, kont:Atom |- "C_KTupleCons" "(" head "," kont ")" : Atom;
        C_KArgTail . origHead:Atom, rest:Atom, types:Atom, kont:Atom |- "C_KArgTail" "(" origHead "," rest "," types "," kont ")" : Atom;
        C_KArgCons . head:Atom, kont:Atom |- "C_KArgCons" "(" head "," kont ")" : Atom;
        C_KSwitch . rawCases:Atom, ty:Atom, kont:Atom |- "C_KSwitch" "(" rawCases "," ty "," kont ")" : Atom;
        C_KAssert . asserted:Atom, kont:Atom |- "C_KAssert" "(" asserted "," kont ")" : Atom;
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
        R0 . | isEmpty(atom) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_Return atom) space out);
        R1 . | isError(atom) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_Return atom) space out);
        R2 . | typeMatchesMetaOrAtom(atom, ty) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_Return atom) space out);
        R3 . | needsTypeCast(atom, ty) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_TypeCast atom ty) space out);
        R4 . | needsInterpExpr(atom, ty) |- (C_State (C_Metta atom ty) space out) ~> (C_State (C_InterpExpr atom ty) space out);
        R5 . | applicableFuncType(space, atom, ty, opType, retType) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_InterpFunc atom opType retType) space out);
        R6 . | needsTupleInterp(space, atom, ty) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_InterpTuple atom) space out);
        R7 . | noTypeAtAll(space, atom) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_MettaCall atom ty) space out);
        R8 . | notExpression(atom) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_Return atom) space out);
        R9 . |- (C_State (C_InterpFunc (C_ExprCons op argsTail) opType retType) space out) ~> (C_State (C_Metta op opType) space (C_KAfterOp argsTail opType retType out));
        R10 . |- (C_State (C_InterpFunc C_ExprNil opType retType) space out) ~> (C_State (C_Return C_ExprNil) space out);
        R11 . | notExpression(atom) |- (C_State (C_InterpFunc atom opType retType) space out) ~> (C_State (C_Return atom) space out);
        R12 . | isEmpty(h) |- (C_State (C_Return h) space (C_KAfterOp argsTail opType retType k)) ~> (C_State (C_Return h) space k);
        R13 . | isError(h) |- (C_State (C_Return h) space (C_KAfterOp argsTail opType retType k)) ~> (C_State (C_Return h) space k);
        R14 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KAfterOp C_ExprNil opType retType k)) ~> (C_State (C_MettaCall (C_ExprCons h C_ExprNil) retType) space k);
        R15 . | metaType(h, mt), funcArgTypes(opType, argTypes) |- (C_State (C_Return h) space (C_KAfterOp (C_ExprCons argHead argRest) opType retType k)) ~> (C_State (C_InterpArgs argHead argRest argTypes) space (C_KAfterArgs h retType k));
        R16 . | isEmpty(argsEval) |- (C_State (C_Return argsEval) space (C_KAfterArgs h retType k)) ~> (C_State (C_Return argsEval) space k);
        R17 . | isError(argsEval) |- (C_State (C_Return argsEval) space (C_KAfterArgs h retType k)) ~> (C_State (C_Return argsEval) space k);
        R18 . | metaType(argsEval, mt) |- (C_State (C_Return argsEval) space (C_KAfterArgs h retType k)) ~> (C_State (C_MettaCall (C_ExprCons h argsEval) retType) space k);
        R19 . |- (C_State (C_InterpArgs head rest (C_ExprCons ty typeRest)) space out) ~> (C_State (C_Metta head ty) space (C_KArgTail head rest typeRest out));
        R20 . |- (C_State (C_InterpArgs head rest C_ExprNil) space out) ~> (C_State (C_Metta head C_UndefinedType) space (C_KArgTail head rest C_ExprNil out));
        R21 . | changedToEmpty(origHead, h) |- (C_State (C_Return h) space (C_KArgTail origHead rest types k)) ~> (C_State (C_Return h) space k);
        R22 . | changedToError(origHead, h) |- (C_State (C_Return h) space (C_KArgTail origHead rest types k)) ~> (C_State (C_Return h) space k);
        R23 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KArgTail origHead C_ExprNil types k)) ~> (C_State (C_Return (C_ExprCons h C_ExprNil)) space k);
        R24 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KArgTail origHead (C_ExprCons nextArg nextRest) types k)) ~> (C_State (C_InterpArgs nextArg nextRest types) space (C_KArgCons h k));
        R25 . | isEmpty(t) |- (C_State (C_Return t) space (C_KArgCons h k)) ~> (C_State (C_Return t) space k);
        R26 . | isError(t) |- (C_State (C_Return t) space (C_KArgCons h k)) ~> (C_State (C_Return t) space k);
        R27 . | metaType(t, mt) |- (C_State (C_Return t) space (C_KArgCons h k)) ~> (C_State (C_Return (C_ExprCons h t)) space k);
        R28 . |- (C_State (C_InterpTuple C_ExprNil) space out) ~> (C_State (C_Return C_ExprNil) space out);
        R29 . |- (C_State (C_InterpTuple (C_ExprCons head tail)) space out) ~> (C_State (C_Metta head C_UndefinedType) space (C_KTupleTail tail out));
        R30 . | isEmpty(h) |- (C_State (C_Return h) space (C_KTupleTail tail k)) ~> (C_State (C_Return h) space k);
        R31 . | isError(h) |- (C_State (C_Return h) space (C_KTupleTail tail k)) ~> (C_State (C_Return h) space k);
        R32 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KTupleTail C_ExprNil k)) ~> (C_State (C_Return (C_ExprCons h C_ExprNil)) space k);
        R33 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KTupleTail (C_ExprCons tHead tTail) k)) ~> (C_State (C_InterpTuple (C_ExprCons tHead tTail)) space (C_KTupleCons h k));
        R34 . | isEmpty(t) |- (C_State (C_Return t) space (C_KTupleCons h k)) ~> (C_State (C_Return t) space k);
        R35 . | isError(t) |- (C_State (C_Return t) space (C_KTupleCons h k)) ~> (C_State (C_Return t) space k);
        R36 . | metaType(t, mt) |- (C_State (C_Return t) space (C_KTupleCons h k)) ~> (C_State (C_Return (C_ExprCons h t)) space k);
        R37 . | isError(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return atom) space out);
        R38 . | groundedCallResult(space, atom, result) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta result ty) space out);
        R39 . | notExecutable(atom), parseSwitchMinimalCall(atom, scrutinee, rawCases) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta scrutinee C_UndefinedType) space (C_KSwitch rawCases ty out));
        R40 . | selectSwitchResult(scrutineeVal, rawCases, template), isReducible(template) |- (C_State (C_Return scrutineeVal) space (C_KSwitch rawCases ty k)) ~> (C_State (C_Metta template ty) space k);
        R41 . | selectSwitchResult(scrutineeVal, rawCases, template), isNotReducible(template) |- (C_State (C_Return scrutineeVal) space (C_KSwitch rawCases ty k)) ~> (C_State (C_Return C_Empty) space k);
        R42 . | notExecutable(atom), parseAssertCall(atom, asserted) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta asserted C_UndefinedType) space (C_KAssert asserted out));
        R43 . | assertMatchesTrue(assertedVal) |- (C_State (C_Return assertedVal) space (C_KAssert asserted k)) ~> (C_State (C_Return C_ExprNil) space k);
        R44 . | assertNotTrue(assertedVal), mkAssertError(asserted, assertedVal, errAtom) |- (C_State (C_Return assertedVal) space (C_KAssert asserted k)) ~> (C_State (C_Return errAtom) space k);
        R45 . | notExecutable(atom), parseCaseCall(atom, scrutinee, rawCases) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta scrutinee C_UndefinedType) space (C_KSwitch rawCases ty out));
        R46 . | notExecutable(atom), parseSuperpose(atom, elem) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta elem ty) space out);
        R47 . | notExecutable(atom), isSuperpose_empty(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return C_Empty) space out);
        R48 . | notExecutable(atom), parseMatchCall(atom, pattern, template), spaceQueryMatch(pattern, template, result) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta result ty) space out);
        R49 . | notExecutable(atom), parseMatchCall(atom, pattern, template), spaceQueryNoMatch(pattern) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return C_Empty) space out);
        R50 . | notExecutable(atom), parseUnifyCall(atom, target, pattern, success, failure), localMatch(target, pattern, success, result) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta result ty) space out);
        R51 . | notExecutable(atom), parseUnifyCall(atom, target, pattern, success, failure), localNoMatch(target, pattern) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta failure ty) space out);
        R52 . | notExecutable(atom), parseCollapseCall(atom, expr), collapseBind(expr, ty, packed) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return packed) space out);
        R53 . | eqQueryResult(space, atom, rhs), notExecutable(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta rhs ty) space out);
        R54 . | noEqQuery(space, atom), notExecutable(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return atom) space out);
        R55 . | typeOf(space, atom, ty) |- (C_State (C_TypeCast atom ty) space out) ~> (C_State (C_Return atom) space out);
        R56 . | typeMismatch(space, atom, ty, actual) |- (C_State (C_TypeCast atom ty) space out) ~> (C_State (C_Return (C_ErrorAtom atom (C_BadType ty actual))) space out);
        R57 . | isEmpty(out) |- (C_State (C_Return result) space out) ~> (C_State C_Done space result);
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

        // ═══ Query scoping (auto-generated from rewrite premises) ═══
        relation isEmptyQuery1(Space);
        relation isErrorQuery1(Space);
        relation typeMatchesMetaOrAtomQuery2(Space, Atom);
        relation needsTypeCastQuery2(Space, Atom);
        relation needsInterpExprQuery2(Space, Atom);
        relation applicableFuncTypeQuery3(Space, Atom, Atom);
        relation needsTupleInterpQuery3(Space, Atom, Atom);
        relation noTypeAtAllQuery2(Space, Atom);
        relation notExpressionQuery1(Space);
        relation metaTypeQuery2(Space, Atom);
        relation funcArgTypesQuery2(Space, Atom);
        relation changedToEmptyQuery2(Space, Atom);
        relation changedToErrorQuery2(Space, Atom);
        relation groundedCallResultQuery3(Space, Atom, Atom);
        relation notExecutableQuery1(Space);
        relation parseSwitchMinimalCallQuery3(Space, Atom, Atom);
        relation selectSwitchResultQuery2(Space, Atom);
        relation isReducibleQuery1(Space);
        relation isNotReducibleQuery1(Space);
        relation parseAssertCallQuery2(Space, Atom);
        relation assertMatchesTrueQuery1(Space);
        relation assertNotTrueQuery1(Space);
        relation mkAssertErrorQuery2(Space, Atom);
        relation parseCaseCallQuery3(Space, Atom, Atom);
        relation parseSuperposeQuery2(Space, Atom);
        relation isSuperpose_emptyQuery1(Space);
        relation parseMatchCallQuery3(Space, Atom, Atom);
        relation spaceQueryMatchQuery3(Space, Atom, Atom);
        relation spaceQueryNoMatchQuery1(Space);
        relation parseUnifyCallQuery3(Space, Atom, Atom);
        relation localMatchQuery3(Space, Atom, Atom);
        relation localNoMatchQuery2(Space, Atom);
        relation parseCollapseCallQuery2(Space, Atom);
        relation collapseBindQuery3(Space, Atom, Atom);
        relation eqQueryResultQuery3(Space, Atom, Atom);
        relation noEqQueryQuery2(Space, Atom);
        relation typeOfQuery3(Space, Atom, Atom);
        relation typeMismatchQuery3(Space, Atom, Atom);

        isEmptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Metta(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        isErrorQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Metta(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        typeMatchesMetaOrAtomQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Metta(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        needsTypeCastQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Metta(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        needsInterpExprQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Metta(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        applicableFuncTypeQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_InterpExpr(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        needsTupleInterpQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_InterpExpr(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        noTypeAtAllQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_InterpExpr(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExpressionQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_InterpExpr(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExpressionQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_InterpFunc(ref arg00, ref arg10, ref arg20) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone(),
            let arg2 = (**arg20).clone();

        isEmptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isErrorQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        funcArgTypesQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isEmptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isErrorQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        changedToEmptyQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        changedToErrorQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isEmptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isErrorQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isEmptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isErrorQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isEmptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isErrorQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        metaTypeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isErrorQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        groundedCallResultQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseSwitchMinimalCallQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        selectSwitchResultQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isReducibleQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        selectSwitchResultQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        isNotReducibleQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseAssertCallQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        assertMatchesTrueQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        assertNotTrueQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        mkAssertErrorQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseCaseCallQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseSuperposeQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        isSuperpose_emptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseMatchCallQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        spaceQueryMatchQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseMatchCallQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        spaceQueryNoMatchQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseUnifyCallQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        localMatchQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseUnifyCallQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        localNoMatchQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        parseCollapseCallQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        collapseBindQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        eqQueryResultQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        noEqQueryQuery2(sp, arg0) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        notExecutableQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_MettaCall(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        typeOfQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_TypeCast(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        typeMismatchQuery3(sp, arg0, arg1) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_TypeCast(ref arg00, ref arg10) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone(),
            let arg1 = (**arg10).clone();

        isEmptyQuery1(sp) <--
            state(st),
            if let State::C_State(ref instr, ref sp0, _) = st,
            if let Instr::C_Return(ref arg00) = &**instr,
            let sp = (**sp0).clone(),
            let arg0 = (**arg00).clone();

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
        relation typeOfRaw(Space, Atom, Atom);
        relation typeOf(Space, Atom, Atom);
        relation typeMismatch(Space, Atom, Atom, Atom);
        relation funcArgTypes(Atom, Atom);
        relation changedToEmpty(Atom, Atom);
        relation changedToError(Atom, Atom);
        relation eqQueryRaw(Space, Atom, Atom);
        relation eqQueryResult(Space, Atom, Atom);
        relation eqQueryHas(Space, Atom);
        relation noEqQuery(Space, Atom);
        relation groundedCallResult(Space, Atom, Atom);
        relation applicableFuncTypeRaw(Space, Atom, Atom, Atom);
        relation applicableFuncType(Space, Atom, Atom, Atom, Atom);
        relation applicableFuncTypeHas(Space, Atom, Atom);
        relation needsTupleInterp(Space, Atom, Atom);
        relation noTypeAtAll(Space, Atom);
        relation parseSwitchMinimalCall(Atom, Atom, Atom);
        relation parseCaseCall(Atom, Atom, Atom);
        relation parseAssertCall(Atom, Atom);
        relation selectSwitchResult(Atom, Atom, Atom);
        relation isNotReducible(Atom);
        relation isReducible(Atom);
        relation assertMatchesTrue(Atom);
        relation assertNotTrue(Atom);
        relation mkAssertError(Atom, Atom, Atom);
        relation parseSuperpose(Atom, Atom);
        relation isSuperpose_empty(Atom);
        relation parseMatchCall(Atom, Atom, Atom);
        relation spaceQueryMatch(Atom, Atom, Atom);
        relation spaceQueryNoMatch(Atom);
        relation parseUnifyCall(Atom, Atom, Atom, Atom, Atom);
        relation localMatch(Atom, Atom, Atom, Atom);
        relation localNoMatch(Atom, Atom);
        relation parseCollapseCall(Atom, Atom);
        relation collapseBind(Atom, Atom, Atom);

        // ═══ Premise rules (generated from PremiseProgram IR) ═══
        // isEmpty_check
        isEmpty(atom) <--
            atom(atom),
            if atom == Atom::C_Empty;

        // isError_check
        isError(atom) <--
            atom(atom),
            if let Atom::C_ErrorAtom(_, _) = atom;

        // changedToEmpty_guard
        changedToEmpty(orig, new) <--
            atom(orig),
            isEmpty(new),
            if new != orig;

        // changedToError_guard
        changedToError(orig, new) <--
            atom(orig),
            isError(new),
            if new != orig;

        // metaType_symbol
        metaType(atom, Atom::C_SymbolType) <--
            atom(atom),
            if let Atom::C_SymAtom(_) = atom;

        // metaType_variable
        metaType(atom, Atom::C_VariableType) <--
            atom(atom),
            if let Atom::C_VarAtom(_) = atom;

        // metaType_expression_cons
        metaType(atom, Atom::C_ExpressionType) <--
            atom(atom),
            if let Atom::C_ExprCons(_, _) = atom;

        // metaType_expression_nil
        metaType(atom, Atom::C_ExpressionType) <--
            atom(atom),
            if atom == Atom::C_ExprNil;

        // metaType_grounded_int
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if let Atom::C_GInt(_) = atom;

        // metaType_grounded_string
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if let Atom::C_GString(_) = atom;

        // metaType_grounded_bool
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if let Atom::C_GBool(_) = atom;

        // metaType_grounded_op_add
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpAdd;

        // metaType_grounded_op_sub
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpSub;

        // metaType_grounded_op_mul
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpMul;

        // metaType_grounded_op_div
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpDiv;

        // metaType_grounded_op_mod
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpMod;

        // metaType_grounded_op_lt
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpLt;

        // metaType_grounded_op_gt
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpGt;

        // metaType_grounded_op_eq
        metaType(atom, Atom::C_GroundedType) <--
            atom(atom),
            if atom == Atom::C_OpEq;

        // typeMatch_atomType
        typeMatchesMetaOrAtom(atom, ty) <--
            atom(ty),
            atom(atom),
            if ty == Atom::C_AtomType;

        // typeMatch_sameMetaType
        typeMatchesMetaOrAtom(atom, ty) <--
            metaType(atom, ty);

        // typeMatch_variable
        typeMatchesMetaOrAtom(atom, ty) <--
            atom(ty),
            metaType(atom, Atom::C_VariableType);

        // typeNotMatch_explicit
        typeNotMatchesMetaOrAtom(atom, ty) <--
            atom(ty),
            metaType(atom, mt),
            if ty != Atom::C_AtomType,
            if mt != Atom::C_VariableType,
            if mt != ty;

        // needsTypeCast_symbol
        needsTypeCast(atom, ty) <--
            metaType(atom, Atom::C_SymbolType),
            typeNotMatchesMetaOrAtom(atom, ty);

        // needsTypeCast_grounded
        needsTypeCast(atom, ty) <--
            metaType(atom, Atom::C_GroundedType),
            typeNotMatchesMetaOrAtom(atom, ty);

        // needsTypeCast_unit
        needsTypeCast(atom, ty) <--
            atom(atom),
            if atom == Atom::C_ExprNil,
            typeNotMatchesMetaOrAtom(atom, ty);

        // needsInterpExpr_expression
        needsInterpExpr(atom, ty) <--
            metaType(atom, Atom::C_ExpressionType),
            typeNotMatchesMetaOrAtom(atom, ty);

        // notExpression_check
        notExpression(atom) <--
            metaType(atom, mt),
            if mt != Atom::C_ExpressionType;

        // isExecutable_grounded
        isExecutable(op) <--
            atom(op),
            if let Some(_) = is_executable_grounded(op);

        // notExecutable_check
        notExecutable(op) <--
            atom(op),
            if let Some(_) = is_not_executable_grounded(op);

        // typeOfRaw_annotation
        typeOfRaw(sp, atom, ty) <--
            space(sp),
            atom(atom),
            if let Space::C_Space(ref atoms0) = sp,
            let atoms = (**atoms0).clone(),
            if let Some(ty) = find_type_annotation(atoms, atom);

        // typeOf_from_raw
        typeOf(sp, atom, ty) <--
            typeOfRaw(sp, atom, ty);

        // typeMismatch_check
        typeMismatch(sp, atom, expected, actual) <--
            atom(expected),
            typeOf(sp, atom, actual),
            if actual != expected;

        // funcArgTypes_arrow
        funcArgTypes(opType, argTypes) <--
            atom(opType),
            if let Atom::C_ArrowType(ref argTypes0, _) = opType,
            let argTypes = (**argTypes0).clone();

        // eqQueryRaw_match
        eqQueryRaw(sp, atom, rhs) <--
            space(sp),
            atom(atom),
            for rhs in query_equations_in_space(sp, atom).into_iter();

        // eqQueryResult_from_raw
        eqQueryResult(sp, atom, rhs) <--
            eqQueryRaw(sp, atom, rhs);

        // eqQueryHas_witness
        eqQueryHas(sp, atom) <--
            eqQueryRaw(sp, atom, _);

        // noEqQuery_notIn_has
        noEqQuery(sp, atom) <--
            space(sp),
            atom(atom),
            if query_equations_in_space(sp, atom).into_iter().next().is_none();

        // groundedCallResult_dispatch
        groundedCallResult(sp, atom, result) <--
            atom(atom),
            space(sp),
            if let Atom::C_ExprCons(ref op0, ref argsTail0) = atom,
            let op = (**op0).clone(),
            let argsTail = (**argsTail0).clone(),
            isExecutable(op),
            if let Some(result) = eval_grounded_dispatch(op.clone(), argsTail.clone());

        // applicableFuncTypeRaw_check
        applicableFuncTypeRaw(sp, atom, ty, opType_retType) <--
            space(sp),
            atom(atom),
            atom(ty),
            if let Some(opType_retType) = find_applicable_func_type(sp, atom, &ty);

        // applicableFuncType_from_raw
        applicableFuncType(sp, atom, ty, opType, retType) <--
            applicableFuncTypeRaw(sp, atom, ty, opType_retType),
            if let Atom::C_ExprCons(ref opType0, ref retType0) = opType_retType,
            let opType = (**opType0).clone(),
            let retType = (**retType0).clone();

        // applicableFuncTypeHas_witness
        applicableFuncTypeHas(sp, atom, ty) <--
            applicableFuncTypeRaw(sp, atom, ty, _);

        // needsTupleInterp_check
        needsTupleInterp(sp, atom, ty) <--
            space(sp),
            atom(atom),
            if let Some(ty) = has_non_func_types(sp, atom),
            if find_applicable_func_type(sp, atom, &ty).is_none();

        // noTypeAtAll_missing_head_type
        noTypeAtAll(sp, atom) <--
            space(sp),
            atom(atom),
            if let Some(_) = check_no_type_at_all(sp, atom);

        // parseSwitchMinimalCall_check
        parseSwitchMinimalCall(atom, scrutinee, rawCases) <--
            atom(atom),
            if let Some(packed) = parseSwitchMinimalCallArgs(atom),
            if let Atom::C_ExprCons(ref scrutinee0, ref rawCases0) = packed,
            let scrutinee = (**scrutinee0).clone(),
            let rawCases = (**rawCases0).clone();

        // parseCaseCall_check
        parseCaseCall(atom, scrutinee, rawCases) <--
            atom(atom),
            if let Some(packed) = parseCaseCallArgs(atom),
            if let Atom::C_ExprCons(ref scrutinee0, ref rawCases0) = packed,
            let scrutinee = (**scrutinee0).clone(),
            let rawCases = (**rawCases0).clone();

        // parseAssertCall_check
        parseAssertCall(atom, asserted) <--
            atom(atom),
            if let Some(asserted) = parseAssertCallArg(atom);

        // selectSwitchResult_match
        selectSwitchResult(scrutinee, rawCases, template) <--
            atom(scrutinee),
            atom(rawCases),
            for template in selectSwitchTemplate(scrutinee, rawCases).into_iter();

        // isNotReducible_check
        isNotReducible(atom) <--
            atom(atom),
            if let Some(_) = checkIsNotReducible(atom);

        // isReducible_check
        isReducible(atom) <--
            atom(atom),
            if let Some(_) = checkIsReducible(atom);

        // assertMatchesTrue_check
        assertMatchesTrue(atom) <--
            atom(atom),
            if atom == Atom::C_True;

        // assertNotTrue_check
        assertNotTrue(atom) <--
            atom(atom),
            if atom != Atom::C_True;

        // mkAssertError_build
        mkAssertError(asserted, assertedVal, errAtom) <--
            atom(asserted),
            atom(assertedVal),
            if let Some(errAtom) = buildAssertError(asserted, assertedVal);

        // parseSuperpose_elements
        parseSuperpose(atom, elem) <--
            atom(atom),
            for elem in parseSuperposElements(atom).into_iter();

        // isSuperpose_empty_check
        isSuperpose_empty(atom) <--
            atom(atom),
            if let Some(_) = checkSuperposeEmpty(atom);

        // parseMatchCall_check
        parseMatchCall(atom, pattern, template) <--
            atom(atom),
            if let Some(packed) = parseMatchCallArgs(atom),
            if let Atom::C_ExprCons(ref pattern0, ref template0) = packed,
            let pattern = (**pattern0).clone(),
            let template = (**template0).clone();

        // spaceQueryMatch_query
        spaceQueryMatch(pattern, template, result) <--
            atom(pattern),
            atom(template),
            for result in spacePatternQuery(pattern, template).into_iter();

        // spaceQueryNoMatch_check
        spaceQueryNoMatch(pattern) <--
            atom(pattern),
            if let Some(_) = checkSpaceNoMatch(pattern);

        // parseUnifyCall_check
        parseUnifyCall(atom, target, pattern, success, failure) <--
            atom(atom),
            if let Some(packed) = parseUnifyCallArgs(atom),
            if let Atom::C_ExprCons(ref target0, ref rest10) = packed,
            let target = (**target0).clone(),
            let rest1 = (**rest10).clone(),
            if let Atom::C_ExprCons(ref pattern0, ref rest20) = rest1,
            let pattern = (**pattern0).clone(),
            let rest2 = (**rest20).clone(),
            if let Atom::C_ExprCons(ref success0, ref failure0) = rest2,
            let success = (**success0).clone(),
            let failure = (**failure0).clone();

        // localMatch_compute
        localMatch(target, pattern, success, result) <--
            atom(target),
            atom(pattern),
            atom(success),
            if let Some(result) = localPatternMatch(target, pattern, success);

        // localNoMatch_check
        localNoMatch(target, pattern) <--
            atom(target),
            atom(pattern),
            if let Some(_) = checkLocalNoMatch(target, pattern);

        // parseCollapseCall_check
        parseCollapseCall(atom, expr) <--
            atom(atom),
            if let Some(expr) = parseCollapseCallArg(atom);

        // collapseBind_oracle
        collapseBind(expr, ty, packed) <--
            atom(expr),
            atom(ty),
            if let Some(packed) = evalCollapseBind(expr, ty);
    }
}
