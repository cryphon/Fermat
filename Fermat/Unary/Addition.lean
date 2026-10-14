import Fermat.Unary.Basic

namespace Unary

theorem zero_add (n : Unary) : zero + n = n := by
  induction n with
  | zero =>
    -- goal: zero + zero = zero
    rw [add_zero]
  | succ d hd =>
    -- hd: zero + d = d
    -- goal: zero + succ d = succ d
    rw [add_succ]
    -- goal: succ(zero + d) = d
    rw [hd]

theorem succ_add (a b : Unary) : succ a + b = succ (a + b) := by
  induction b with
  | zero =>
    -- goal: succ(a) + zero = succ(a + zero)
    rw [add_zero]
    rfl
  | succ d hd =>
    -- hd: succ(a) + d = succ(a + d)
    -- goal: succ(a) + succ(d) = (succ a + succ(d))
    rw [add_succ]
    -- goal: succ(succ(a) + d) = succ(a + succ(d))
    rw [hd]
    rfl

theorem add_comm (a b : Unary) : a + b = b + a := by
  induction b with
  | zero =>
    -- goal: a + zero = zero + a
    rw [add_zero]
    -- goal: a = zero + a
    rw [zero_add]
  | succ d hd =>
    -- hd: a + d = d + a
    -- goal: a + succ(d) = succ(d) + a
    rw [succ_add]
    -- goal: a + succ(d) = succ(d + a)
    rw [add_succ]
    -- goal: succ(a + d) = succ(d + a)
    rw [hd]

theorem add_assoc (a b c : Unary) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    -- goal: a + b + zero = a + (b + zero)
    rw [add_zero]
    -- goal: a + b = a + (b + zero)
    rfl
  | succ d hd =>
    -- hd: a + b + d = a + (b + d)
    -- goal: a + b + succ(d) = a + (b + succ(d))
    rw [add_succ]
    -- goal: succ(a + b + d) = a (b + succ(d))
    rw [hd]
    rfl

theorem add_right_comm (a b c : Unary) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]
