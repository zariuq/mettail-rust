language! {
    name: IMP,

    types {
        Nat
        ImpVar
        Bool
        AAtom
        AMul
        AExp
        BAtom
        BNeg
        BConj
        BExp
        StmtAtom
        Stmt
        Control
        Kont
        Store
        Status
        State
    },

    terms {
        C_Zero . |- "C_Zero" : Nat;
        C_Succ . n:Nat |- "C_Succ" "(" n ")" : Nat;
        C_VarX . |- "C_VarX" : ImpVar;
        C_VarY . |- "C_VarY" : ImpVar;
        C_VarZ . |- "C_VarZ" : ImpVar;
        C_BoolTrue . |- "C_BoolTrue" : Bool;
        C_BoolFalse . |- "C_BoolFalse" : Bool;
        C_ANat . n:Nat |- "C_ANat" "(" n ")" : AAtom;
        C_AVar . x:ImpVar |- "C_AVar" "(" x ")" : AAtom;
        C_AParen . e:AExp |- "C_AParen" "(" e ")" : AAtom;
        C_AMulAtom . a:AAtom |- "C_AMulAtom" "(" a ")" : AMul;
        C_AMulTimes . lhs:AMul, rhs:AAtom |- "C_AMulTimes" "(" lhs "," rhs ")" : AMul;
        C_AExpMul . m:AMul |- "C_AExpMul" "(" m ")" : AExp;
        C_AExpPlus . lhs:AExp, rhs:AMul |- "C_AExpPlus" "(" lhs "," rhs ")" : AExp;
        C_BTrueAtom . |- "C_BTrueAtom" : BAtom;
        C_BFalseAtom . |- "C_BFalseAtom" : BAtom;
        C_BLe . lhs:AExp, rhs:AExp |- "C_BLe" "(" lhs "," rhs ")" : BAtom;
        C_BEq . lhs:AExp, rhs:AExp |- "C_BEq" "(" lhs "," rhs ")" : BAtom;
        C_BParen . b:BExp |- "C_BParen" "(" b ")" : BAtom;
        C_BNegAtom . b:BAtom |- "C_BNegAtom" "(" b ")" : BNeg;
        C_BNot . b:BNeg |- "C_BNot" "(" b ")" : BNeg;
        C_BConjNeg . b:BNeg |- "C_BConjNeg" "(" b ")" : BConj;
        C_BAnd . lhs:BConj, rhs:BNeg |- "C_BAnd" "(" lhs "," rhs ")" : BConj;
        C_BExpConj . b:BConj |- "C_BExpConj" "(" b ")" : BExp;
        C_Skip . |- "C_Skip" : StmtAtom;
        C_Assign . x:ImpVar, e:AExp |- "C_Assign" "(" x "," e ")" : StmtAtom;
        C_If . b:BExp, t:Stmt, els:Stmt |- "C_If" "(" b "," t "," els ")" : StmtAtom;
        C_While . b:BExp, body:Stmt |- "C_While" "(" b "," body ")" : StmtAtom;
        C_StmtParen . s:Stmt |- "C_StmtParen" "(" s ")" : StmtAtom;
        C_StmtAtomPromote . s:StmtAtom |- "C_StmtAtomPromote" "(" s ")" : Stmt;
        C_Seq . s1:Stmt, s2:StmtAtom |- "C_Seq" "(" s1 "," s2 ")" : Stmt;
        C_Store . x:Nat, y:Nat, z:Nat |- "C_Store" "(" x "," y "," z ")" : Store;
        C_Running . |- "C_Running" : Status;
        C_Done . |- "C_Done" : Status;
        C_Stuck . |- "C_Stuck" : Status;
        C_Start . stmt:Stmt, store:Store |- "C_Start" "(" stmt "," store ")" : State;
        C_RunStmt . stmt:Stmt |- "C_RunStmt" "(" stmt ")" : Control;
        C_RunA . expr:AExp |- "C_RunA" "(" expr ")" : Control;
        C_RunB . expr:BExp |- "C_RunB" "(" expr ")" : Control;
        C_RetNat . n:Nat |- "C_RetNat" "(" n ")" : Control;
        C_RetBool . b:Bool |- "C_RetBool" "(" b ")" : Control;
        C_RetUnit . |- "C_RetUnit" : Control;
        C_KDone . |- "C_KDone" : Kont;
        C_KSeq . stmt:Stmt, k:Kont |- "C_KSeq" "(" stmt "," k ")" : Kont;
        C_KAssign . x:ImpVar, k:Kont |- "C_KAssign" "(" x "," k ")" : Kont;
        C_KIf . t:Stmt, els:Stmt, k:Kont |- "C_KIf" "(" t "," els "," k ")" : Kont;
        C_KWhile . b:BExp, body:Stmt, k:Kont |- "C_KWhile" "(" b "," body "," k ")" : Kont;
        C_KPlusL . rhs:AMul, k:Kont |- "C_KPlusL" "(" rhs "," k ")" : Kont;
        C_KPlusR . lhs:Nat, k:Kont |- "C_KPlusR" "(" lhs "," k ")" : Kont;
        C_KTimesL . rhs:AAtom, k:Kont |- "C_KTimesL" "(" rhs "," k ")" : Kont;
        C_KTimesR . lhs:Nat, k:Kont |- "C_KTimesR" "(" lhs "," k ")" : Kont;
        C_KLeL . rhs:AExp, k:Kont |- "C_KLeL" "(" rhs "," k ")" : Kont;
        C_KLeR . lhs:Nat, k:Kont |- "C_KLeR" "(" lhs "," k ")" : Kont;
        C_KEqL . rhs:AExp, k:Kont |- "C_KEqL" "(" rhs "," k ")" : Kont;
        C_KEqR . lhs:Nat, k:Kont |- "C_KEqR" "(" lhs "," k ")" : Kont;
        C_KNot . k:Kont |- "C_KNot" "(" k ")" : Kont;
        C_KAndL . rhs:BNeg, k:Kont |- "C_KAndL" "(" rhs "," k ")" : Kont;
        C_ImpState . control:Control, store:Store, kont:Kont, status:Status |- "C_ImpState" "(" control "," store "," kont "," status ")" : State;
    },

    equations {    },

    rewrites {
        R0 . |- (C_Start stmt store) ~> (C_ImpState (C_RunStmt stmt) store C_KDone C_Running);
        R1 . |- (C_ImpState (C_RunStmt (C_StmtAtomPromote C_Skip)) store k C_Running) ~> (C_ImpState C_RetUnit store k C_Running);
        R2 . |- (C_ImpState (C_RunStmt (C_StmtAtomPromote (C_Assign x e))) store k C_Running) ~> (C_ImpState (C_RunA e) store (C_KAssign x k) C_Running);
        R3 . |- (C_ImpState (C_RunStmt (C_Seq s1 s2)) store k C_Running) ~> (C_ImpState (C_RunStmt s1) store (C_KSeq (C_StmtAtomPromote s2) k) C_Running);
        R4 . |- (C_ImpState (C_RunStmt (C_StmtAtomPromote (C_If b t els))) store k C_Running) ~> (C_ImpState (C_RunB b) store (C_KIf t els k) C_Running);
        R5 . |- (C_ImpState (C_RunStmt (C_StmtAtomPromote (C_While b body))) store k C_Running) ~> (C_ImpState (C_RunB b) store (C_KWhile b body k) C_Running);
        R6 . |- (C_ImpState (C_RunA (C_AExpMul (C_AMulAtom (C_ANat n)))) store k C_Running) ~> (C_ImpState (C_RetNat n) store k C_Running);
        R7 . | storeGet(store, x, n) |- (C_ImpState (C_RunA (C_AExpMul (C_AMulAtom (C_AVar x)))) store k C_Running) ~> (C_ImpState (C_RetNat n) store k C_Running);
        R8 . |- (C_ImpState (C_RunA (C_AExpMul (C_AMulAtom (C_AParen e)))) store k C_Running) ~> (C_ImpState (C_RunA e) store k C_Running);
        R9 . |- (C_ImpState (C_RunA (C_AExpMul (C_AMulTimes lhs rhs))) store k C_Running) ~> (C_ImpState (C_RunA (C_AExpMul lhs)) store (C_KTimesL rhs k) C_Running);
        R10 . |- (C_ImpState (C_RunA (C_AExpPlus lhs rhs)) store k C_Running) ~> (C_ImpState (C_RunA lhs) store (C_KPlusL rhs k) C_Running);
        R11 . |- (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg (C_BNegAtom C_BTrueAtom)))) store k C_Running) ~> (C_ImpState (C_RetBool C_BoolTrue) store k C_Running);
        R12 . |- (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg (C_BNegAtom C_BFalseAtom)))) store k C_Running) ~> (C_ImpState (C_RetBool C_BoolFalse) store k C_Running);
        R13 . |- (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg (C_BNegAtom (C_BParen b))))) store k C_Running) ~> (C_ImpState (C_RunB b) store k C_Running);
        R14 . |- (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg (C_BNegAtom (C_BLe lhs rhs))))) store k C_Running) ~> (C_ImpState (C_RunA lhs) store (C_KLeL rhs k) C_Running);
        R15 . |- (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg (C_BNegAtom (C_BEq lhs rhs))))) store k C_Running) ~> (C_ImpState (C_RunA lhs) store (C_KEqL rhs k) C_Running);
        R16 . |- (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg (C_BNot b)))) store k C_Running) ~> (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg b))) store (C_KNot k) C_Running);
        R17 . |- (C_ImpState (C_RunB (C_BExpConj (C_BAnd lhs rhs))) store k C_Running) ~> (C_ImpState (C_RunB (C_BExpConj lhs)) store (C_KAndL rhs k) C_Running);
        R18 . |- (C_ImpState C_RetUnit store (C_KSeq stmt k) C_Running) ~> (C_ImpState (C_RunStmt stmt) store k C_Running);
        R19 . | storeSet(store, x, n, store2) |- (C_ImpState (C_RetNat n) store (C_KAssign x k) C_Running) ~> (C_ImpState C_RetUnit store2 k C_Running);
        R20 . |- (C_ImpState (C_RetBool C_BoolTrue) store (C_KIf t els k) C_Running) ~> (C_ImpState (C_RunStmt t) store k C_Running);
        R21 . |- (C_ImpState (C_RetBool C_BoolFalse) store (C_KIf t els k) C_Running) ~> (C_ImpState (C_RunStmt els) store k C_Running);
        R22 . |- (C_ImpState (C_RetBool C_BoolTrue) store (C_KWhile b body k) C_Running) ~> (C_ImpState (C_RunStmt body) store (C_KSeq (C_StmtAtomPromote (C_While b body)) k) C_Running);
        R23 . |- (C_ImpState (C_RetBool C_BoolFalse) store (C_KWhile b body k) C_Running) ~> (C_ImpState C_RetUnit store k C_Running);
        R24 . |- (C_ImpState (C_RetNat n) store (C_KPlusL rhs k) C_Running) ~> (C_ImpState (C_RunA (C_AExpMul rhs)) store (C_KPlusR n k) C_Running);
        R25 . | natAdd(lhs, rhs, sum) |- (C_ImpState (C_RetNat rhs) store (C_KPlusR lhs k) C_Running) ~> (C_ImpState (C_RetNat sum) store k C_Running);
        R26 . |- (C_ImpState (C_RetNat n) store (C_KTimesL rhs k) C_Running) ~> (C_ImpState (C_RunA (C_AExpMul (C_AMulAtom rhs))) store (C_KTimesR n k) C_Running);
        R27 . | natMul(lhs, rhs, prod) |- (C_ImpState (C_RetNat rhs) store (C_KTimesR lhs k) C_Running) ~> (C_ImpState (C_RetNat prod) store k C_Running);
        R28 . |- (C_ImpState (C_RetNat lhs) store (C_KLeL rhs k) C_Running) ~> (C_ImpState (C_RunA rhs) store (C_KLeR lhs k) C_Running);
        R29 . | natLe(lhs, rhs, out) |- (C_ImpState (C_RetNat rhs) store (C_KLeR lhs k) C_Running) ~> (C_ImpState (C_RetBool out) store k C_Running);
        R30 . |- (C_ImpState (C_RetNat lhs) store (C_KEqL rhs k) C_Running) ~> (C_ImpState (C_RunA rhs) store (C_KEqR lhs k) C_Running);
        R31 . | natEq(lhs, rhs, out) |- (C_ImpState (C_RetNat rhs) store (C_KEqR lhs k) C_Running) ~> (C_ImpState (C_RetBool out) store k C_Running);
        R32 . |- (C_ImpState (C_RetBool C_BoolTrue) store (C_KNot k) C_Running) ~> (C_ImpState (C_RetBool C_BoolFalse) store k C_Running);
        R33 . |- (C_ImpState (C_RetBool C_BoolFalse) store (C_KNot k) C_Running) ~> (C_ImpState (C_RetBool C_BoolTrue) store k C_Running);
        R34 . |- (C_ImpState (C_RetBool C_BoolTrue) store (C_KAndL rhs k) C_Running) ~> (C_ImpState (C_RunB (C_BExpConj (C_BConjNeg rhs))) store k C_Running);
        R35 . |- (C_ImpState (C_RetBool C_BoolFalse) store (C_KAndL rhs k) C_Running) ~> (C_ImpState (C_RetBool C_BoolFalse) store k C_Running);
        R36 . |- (C_ImpState C_RetUnit store C_KDone C_Running) ~> (C_ImpState C_RetUnit store C_KDone C_Done);
    },


    logic {
        relation storeGet(Store, ImpVar, Nat);
        relation storeSet(Store, ImpVar, Nat, Store);
        relation natAdd(Nat, Nat, Nat);
        relation natMul(Nat, Nat, Nat);
        relation natLe(Nat, Nat, Bool);
        relation natEq(Nat, Nat, Bool);
    },
}
