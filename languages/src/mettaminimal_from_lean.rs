#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;
language! {
    name: MeTTaMinimalState,

    types {
        State
        Instr
        Atom
    },

    terms {
        C_State . instr:Instr, x:Atom, y:Atom |- "C_State" "(" instr "," x "," y ")" : State;
        C_Eval . a:Atom |- "C_Eval" "(" a ")" : Instr;
        C_Unify . lhs:Atom, rhs:Atom |- "C_Unify" "(" lhs "," rhs ")" : Instr;
        C_Chain . src:Atom, tmpl:Atom |- "C_Chain" "(" src "," tmpl ")" : Instr;
        C_CollapseBind . src:Atom |- "C_CollapseBind" "(" src ")" : Instr;
        C_SuperposeBind . packed:Atom |- "C_SuperposeBind" "(" packed ")" : Instr;
        C_Return . a:Atom |- "C_Return" "(" a ")" : Instr;
        C_Done . |- "C_Done" : Instr;
        C_ATrue . |- "C_ATrue" : Atom;
        C_AFalse . |- "C_AFalse" : Atom;
    },

    equations {    },

    rewrites {
        R0 . |- (C_State (C_Eval a) x y) ~> (C_State (C_Return a) x y);
        R1 . |- (C_State (C_Return a) x y) ~> (C_State C_Done x a);
    },
}

