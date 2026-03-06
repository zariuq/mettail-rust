language! {
    name: MinskyLite,

    types {
        Nat
        Control
        Status
        Machine
    },

    terms {
        C_Zero . |- "Z" : Nat;
        C_Succ . n:Nat |- "S" n : Nat;
        C_Halt . |- "halt" : Control;
        C_IncA . next:Control |- "incA" next : Control;
        C_IncB . next:Control |- "incB" next : Control;
        C_DecA . zeroNext:Control, succNext:Control |- "decA" "(" zeroNext "," succNext ")" : Control;
        C_DecB . zeroNext:Control, succNext:Control |- "decB" "(" zeroNext "," succNext ")" : Control;
        C_Running . |- "running" : Status;
        C_Done . |- "done" : Status;
        C_Machine . ctrl:Control, regA:Nat, regB:Nat, status:Status |- "state" ctrl regA regB status : Machine;
    },

    equations {    },

    rewrites {
        R0 . |- (C_Machine (C_IncA next) a b C_Running) ~> (C_Machine next (C_Succ a) b C_Running);
        R1 . |- (C_Machine (C_IncB next) a b C_Running) ~> (C_Machine next a (C_Succ b) C_Running);
        R2 . |- (C_Machine (C_DecA zeroNext succNext) C_Zero b C_Running) ~> (C_Machine zeroNext C_Zero b C_Running);
        R3 . |- (C_Machine (C_DecA zeroNext succNext) (C_Succ a) b C_Running) ~> (C_Machine succNext a b C_Running);
        R4 . |- (C_Machine (C_DecB zeroNext succNext) a C_Zero C_Running) ~> (C_Machine zeroNext a C_Zero C_Running);
        R5 . |- (C_Machine (C_DecB zeroNext succNext) a (C_Succ b) C_Running) ~> (C_Machine succNext a b C_Running);
        R6 . |- (C_Machine C_Halt a b C_Running) ~> (C_Machine C_Halt a b C_Done);
    },
}
