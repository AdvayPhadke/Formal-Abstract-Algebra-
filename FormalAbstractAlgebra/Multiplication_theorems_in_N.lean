import FormalAbstractAlgebra.Addition_theorems_in_N
namespace FormalAbstractAlgebra

theorem mul_one (m : Nat) : m*1 = m := by
    rw[Nat.mul_succ]
    rw[Nat.mul_zero]
    rw[zeroadd]

theorem mul_zero (m : Nat) : 0*m = 0 := by
    induction m with
        | zero => rw[Nat.mul_zero]
        | succ n hn =>
            rw[Nat.mul_succ]
            rw[Nat.add_zero]
            rw[hn]

theorem succ_mul (a b : Nat) : (Nat.succ a)*b = a*b + b := by
    induction b with
        | zero =>
            rw[Nat.mul_zero]
            rw[Nat.mul_zero]
        | succ c hc =>
            rw[Nat.mul_succ]
            rw[Nat.mul_succ]
            rw[hc]
            rw[Nat.add_succ]
            rw[Nat.add_succ]
            rw[Nat.succ_inj]
            rw[comm]
            rw[←assoc]
            rw[comm a]

theorem mul_comm (a b : Nat) : a*b = b*a := by
    induction b with
        | zero =>
            rw[mul_zero]
            rw[Nat.mul_zero]
        | succ c hc =>
            rw[succ_mul]
            rw[Nat.mul_succ]
            rw[hc]

theorem one_mul (m : Nat) : 1*m = m := by
    rw[mul_comm]
    rw[mul_one]

theorem l_dist (a b c : Nat) : a*(b + c) = a*b + a*c := by
    induction c with
        | zero =>
            rw[Nat.mul_zero]
            rw[Nat.add_zero]
            rw[Nat.add_zero]
        | succ d hd =>
            rw[Nat.add_succ]
            rw[Nat.mul_succ]
            rw[Nat.mul_succ]
            rw[←assoc (a * b)]
            rw[hd]

theorem r_dist (a b c : Nat) : (b + c)*a = b*a + c*a := by
    rw[mul_comm]
    rw[l_dist]
    rw[mul_comm b]
    rw[mul_comm c]

theorem mul_assoc (a b c : Nat) : (a*b)*c = a*(b*c) := by
    induction c with
        | zero =>
             rw[Nat.mul_zero]
             rw[Nat.mul_zero]
             rw[Nat.mul_zero]
        | succ d hd =>
            rw[Nat.mul_succ]
            rw[Nat.mul_succ]
            rw[l_dist]
            rw[hd]
            
