language! {
    name: MM0Lite,

    types {
        Formula
        Instr
        Program
        Stack
        ProofResult
        ProofState
        Thm
    },

    terms {
        C_AtomP . |- "P" : Formula;
        C_AtomQ . |- "Q" : Formula;
        C_AtomR . |- "R" : Formula;
        C_Implies . a:Formula, b:Formula |- "(" a "->" b ")" : Formula;
        C_ThmImpPQ . |- "thm_imp_p_q" : Thm;
        C_ThmImpQR . |- "thm_imp_q_r" : Thm;
        C_IPush . formula:Formula |- "push" formula : Instr;
        C_IUse . th:Thm |- "use" th : Instr;
        C_IMP . |- "mp" : Instr;
        C_INil . |- "[]" : Program;
        C_ICons . i:Instr, tail:Program |- "[" i "::" tail "]" : Program;
        C_SNil . |- "{}" : Stack;
        C_SCons . formula:Formula, tail:Stack |- "{" formula ";" tail "}" : Stack;
        C_Pending . |- "pending" : ProofResult;
        C_Verified . |- "verified" : ProofResult;
        C_Error . |- "error" : ProofResult;
        C_MMState . prog:Program, goal:Formula, stack:Stack, out:ProofResult |- "state" prog goal stack out : ProofState;
    },

    equations {    },

    rewrites {
        R0 . |- (C_MMState (C_ICons (C_IPush f) prog) goal st C_Pending) ~> (C_MMState prog goal (C_SCons f st) C_Pending);
        R1 . | thmConcl(th, concl) |- (C_MMState (C_ICons (C_IUse th) prog) goal st C_Pending) ~> (C_MMState prog goal (C_SCons concl st) C_Pending);
        R2 . |- (C_MMState (C_ICons C_IMP prog) goal (C_SCons (C_Implies a b) (C_SCons a st)) C_Pending) ~> (C_MMState prog goal (C_SCons b st) C_Pending);
        R3 . |- (C_MMState C_INil goal (C_SCons goal C_SNil) C_Pending) ~> (C_MMState C_INil goal (C_SCons goal C_SNil) C_Verified);
    },


    logic {
        relation thmConcl(Thm, Formula);
    },
}
