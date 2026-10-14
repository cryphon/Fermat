import Fermat.Unary.Basic
import Fermat.Unary.Addition

namespace Unary


theorem zero_mul (m : Unary) : zero * m = zero  := by
  induction m with
    | zero =>
      -- goal: zero * zero = zero
      rw [mul_zero]
    | succ h hd =>
      -- hd: zero * h = zero
      -- goal: zero * succ(h) = zero
      rw [zero_mul]

theorem mul_one (m : Unary) : m * one = m := by
  induction m with
    | zero =>
      -- goal: zero * one = zero
      rw [one_eq_succ_zero]
      -- goal: zero * succ(zero) = zero
      rw [zero_mul]
    | succ h hd =>
      -- hd: h * one = h
      -- goal: succ(h) * one = succ(h)
      rw [one_eq_succ_zero]
      -- goal: succ(h) * succ(zero) = succ(h)
      rw [mul_succ]
      -- goal: succ(h) * zero + succ(h) = succ(h)
      rw [mul_zero]
      -- goal: zero + succ(h) = succ(h)
      rw [zero_add]



