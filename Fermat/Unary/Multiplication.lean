import Fermat.Unary.Basic
import Fermat.Unary.Addition

namespace Unary


theorem zero_mul (m : Unary) : zero * m = zero  := by
  induction m with
    | zero =>
      -- goal: zero * zero = zero
      rw [mul_zero]
    | succ h hd =>
      -- goal: zero * succ(h) = zero
      rw [mul_succ]
      -- goal: zero * h + zero = zero
      rw [hd]
      -- goal zero + zero = zero
      rw [add_zero]


theorem succ_mul (m n: Unary) : succ m * n = m * n + n := by
  induction n with
    | zero =>
      -- goal: succ(m) * zero = m * zero + zero
      rw [mul_zero]
      -- goal: zero = m * zero + zero
      rw [mul_zero]
      -- goal: zero = zero + zero
      rw [add_zero]
    | succ h hd =>
      -- hd: succ(m) * h = m * h + h
      -- goal: succ(m) * succ(h) = m * succ(h) + succ(h)
      rw [mul_succ]
      -- goal: succ(m) * h + succ(m) = m * succ(h) + succ(h)
      rw [hd]
      -- goal: m * h + h + succ(m) = m * succ(h) + succ(h)
      rw [mul_succ]
      -- goal: m * h + h + succ(m) = m * h + m + succ(h)
      rw [add_succ]
      -- goal: succ(m * h + h + m) = m * h + m + succ(h)
      rw [add_succ]
      -- goal: succ(m * h + h + m) = succ(m * h + m + h)
      rw [add_assoc]
      -- goal: succ(m * h + (h + m)) = succ(m * h + m + h)
      rw [add_comm h m]
      -- goal: succ(m * h + (m + h)) = succ(m * h + m + h)
      rw [← add_assoc]

theorem mul_one (m : Unary) : m * one = m := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

theorem one_mul (m : Unary) : one * m = m := by
  induction m with
    | zero =>
      -- goal: one * zero = zero
      rw [one_eq_succ_zero]
      -- goal: succ(zero) * zero = zero
      rfl
    | succ h hd =>
      -- hd: one * h = h
      -- goal: one * succ(h) = succ(h)
      rw [mul_succ]
      -- goal: one * h + one = succ(h)
      rw [hd]
      -- goal: h + one = succ()
      rw [one_eq_succ_zero]
      -- goal: h + succ(zero) = succ(h)
      rw [add_succ]
      -- goal: succ(h + zero) = succ(h)
      rw [add_zero]
