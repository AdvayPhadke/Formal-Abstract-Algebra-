-- neutrality of 0 --

theorem zeroadd (n : Nat) : 0 + n = n := by
    induction n with
    | zero => rfl
    | succ d hd =>
        rw[Nat.add_succ]
        rw[hd]
        rfl

--addition and successor--

theorem s_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
    induction b with
    | zero =>
        rw[Nat.add_zero]
        rw[Nat.add_zero]
        rfl
    | succ d hd =>
        rw[Nat.add_succ]
        rw[Nat.add_succ]
        rw[hd]
        rfl

--commutativity--

theorem comm (a b : Nat) : a + b = b + a := by
    induction a with
        | zero =>
            induction b with
                | zero =>
                    rw[zeroadd]
                    rfl
                | succ d hd =>
                    rw[Nat.add_zero]
                    rw[zeroadd]
        | succ c hc =>
            rw[Nat.add_succ]
            rw[Nat.add_zero]
            rw[s_add]
            rw[Nat.add_succ]
            rw[hc]
            rfl

--associativity--

theorem assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
    induction c with
        | zero =>
            rw[Nat.add_zero]
            rw[Nat.add_zero]
            rfl
        | succ d hd =>
            rw[Nat.add_succ]
            rw[Nat.add_succ]
            rw[Nat.add_succ]
            rw[hd]
            rfl

