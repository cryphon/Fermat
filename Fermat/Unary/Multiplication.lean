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





