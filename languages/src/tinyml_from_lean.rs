#![allow(
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: TinyMLSmoke,

    types {
        Expr
        Val
    },

    terms {
        C_Inject . v:Val |- "C_Inject" "(" v ")" : Expr;
        C_BoolT . |- "C_BoolT" : Val;
        C_BoolF . |- "C_BoolF" : Val;
        C_Thunk . e:Expr |- "C_Thunk" "(" e ")" : Val;
    },

    equations {    },

    rewrites {
        R0 . |- (C_Inject (C_Thunk e)) ~> e;
    },
}

