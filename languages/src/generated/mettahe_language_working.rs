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
        R7 . | notExpression(atom) |- (C_State (C_InterpExpr atom ty) space out) ~> (C_State (C_Return atom) space out);
        R8 . |- (C_State (C_InterpFunc (C_ExprCons op argsTail) opType retType) space out) ~> (C_State (C_Metta op opType) space (C_KAfterOp argsTail opType retType out));
        R9 . |- (C_State (C_InterpFunc C_ExprNil opType retType) space out) ~> (C_State (C_Return C_ExprNil) space out);
        R10 . | notExpression(atom) |- (C_State (C_InterpFunc atom opType retType) space out) ~> (C_State (C_Return atom) space out);
        R11 . | isEmpty(h) |- (C_State (C_Return h) space (C_KAfterOp argsTail opType retType k)) ~> (C_State (C_Return h) space k);
        R12 . | isError(h) |- (C_State (C_Return h) space (C_KAfterOp argsTail opType retType k)) ~> (C_State (C_Return h) space k);
        R13 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KAfterOp C_ExprNil opType retType k)) ~> (C_State (C_MettaCall (C_ExprCons h C_ExprNil) retType) space k);
        R14 . | metaType(h, mt), funcArgTypes(opType, argTypes) |- (C_State (C_Return h) space (C_KAfterOp (C_ExprCons argHead argRest) opType retType k)) ~> (C_State (C_InterpArgs argHead argRest argTypes) space (C_KAfterArgs h retType k));
        R15 . | isEmpty(argsEval) |- (C_State (C_Return argsEval) space (C_KAfterArgs h retType k)) ~> (C_State (C_Return argsEval) space k);
        R16 . | isError(argsEval) |- (C_State (C_Return argsEval) space (C_KAfterArgs h retType k)) ~> (C_State (C_Return argsEval) space k);
        R17 . | metaType(argsEval, mt) |- (C_State (C_Return argsEval) space (C_KAfterArgs h retType k)) ~> (C_State (C_MettaCall (C_ExprCons h argsEval) retType) space k);
        R18 . |- (C_State (C_InterpArgs head rest (C_ExprCons ty typeRest)) space out) ~> (C_State (C_Metta head ty) space (C_KArgTail head rest typeRest out));
        R19 . |- (C_State (C_InterpArgs head rest C_ExprNil) space out) ~> (C_State (C_Metta head C_UndefinedType) space (C_KArgTail head rest C_ExprNil out));
        R20 . | changedToEmpty(origHead, h) |- (C_State (C_Return h) space (C_KArgTail origHead rest types k)) ~> (C_State (C_Return h) space k);
        R21 . | changedToError(origHead, h) |- (C_State (C_Return h) space (C_KArgTail origHead rest types k)) ~> (C_State (C_Return h) space k);
        R22 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KArgTail origHead C_ExprNil types k)) ~> (C_State (C_Return (C_ExprCons h C_ExprNil)) space k);
        R23 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KArgTail origHead (C_ExprCons nextArg nextRest) types k)) ~> (C_State (C_InterpArgs nextArg nextRest types) space (C_KArgCons h k));
        R24 . | isEmpty(t) |- (C_State (C_Return t) space (C_KArgCons h k)) ~> (C_State (C_Return t) space k);
        R25 . | isError(t) |- (C_State (C_Return t) space (C_KArgCons h k)) ~> (C_State (C_Return t) space k);
        R26 . | metaType(t, mt) |- (C_State (C_Return t) space (C_KArgCons h k)) ~> (C_State (C_Return (C_ExprCons h t)) space k);
        R27 . |- (C_State (C_InterpTuple C_ExprNil) space out) ~> (C_State (C_Return C_ExprNil) space out);
        R28 . |- (C_State (C_InterpTuple (C_ExprCons head tail)) space out) ~> (C_State (C_Metta head C_UndefinedType) space (C_KTupleTail tail out));
        R29 . | isEmpty(h) |- (C_State (C_Return h) space (C_KTupleTail tail k)) ~> (C_State (C_Return h) space k);
        R30 . | isError(h) |- (C_State (C_Return h) space (C_KTupleTail tail k)) ~> (C_State (C_Return h) space k);
        R31 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KTupleTail C_ExprNil k)) ~> (C_State (C_Return (C_ExprCons h C_ExprNil)) space k);
        R32 . | metaType(h, mt) |- (C_State (C_Return h) space (C_KTupleTail (C_ExprCons tHead tTail) k)) ~> (C_State (C_InterpTuple (C_ExprCons tHead tTail)) space (C_KTupleCons h k));
        R33 . | isEmpty(t) |- (C_State (C_Return t) space (C_KTupleCons h k)) ~> (C_State (C_Return t) space k);
        R34 . | isError(t) |- (C_State (C_Return t) space (C_KTupleCons h k)) ~> (C_State (C_Return t) space k);
        R35 . | metaType(t, mt) |- (C_State (C_Return t) space (C_KTupleCons h k)) ~> (C_State (C_Return (C_ExprCons h t)) space k);
        R36 . | isError(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return atom) space out);
        R37 . | groundedCallResult(space, atom, result) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta result ty) space out);
        R38 . | eqQueryResult(space, atom, rhs), notExecutable(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Metta rhs ty) space out);
        R39 . | noEqQuery(space, atom), notExecutable(atom) |- (C_State (C_MettaCall atom ty) space out) ~> (C_State (C_Return atom) space out);
        R40 . | typeOf(space, atom, ty) |- (C_State (C_TypeCast atom ty) space out) ~> (C_State (C_Return atom) space out);
        R41 . | typeMismatch(space, atom, ty, actual) |- (C_State (C_TypeCast atom ty) space out) ~> (C_State (C_Return (C_ErrorAtom atom (C_BadType ty actual))) space out);
        R42 . | isEmpty(out) |- (C_State (C_Return result) space out) ~> (C_State C_Done space result);
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
        relation notExpressionQuery1(Space);
        relation metaTypeQuery2(Space, Atom);
        relation funcArgTypesQuery2(Space, Atom);
        relation changedToEmptyQuery2(Space, Atom);
        relation changedToErrorQuery2(Space, Atom);
        relation groundedCallResultQuery3(Space, Atom, Atom);
        relation eqQueryResultQuery3(Space, Atom, Atom);
        relation notExecutableQuery1(Space);
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

        // typeOf_annotation
        typeOf(sp, atom, ty) <--
            space(sp),
            atom(atom),
            if let Space::C_Space(ref atoms0) = sp,
            let atoms = (**atoms0).clone(),
            if let Some(ty) = find_type_annotation(atoms, atom);

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
    }
}
