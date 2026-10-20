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
      rw [add_right_comm]

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

theorem mul_add (m a b : Unary) : m * (a + b) = m * a + m * b := by
  induction b with
  | zero =>
    -- goal: m * (a + zero) = m * a + m * zero
    rw [add_zero]
    -- goal: m * a = m * a + m * zero
    rw [mul_zero]
    -- goal: m * a = m * a + zero
    rw [add_zero]
  | succ h hd =>
    simp only [add_succ, mul_succ, hd,add_assoc]

theorem add_mul (a b t : Unary) : (a + b) * t = a * t + b * t := by
  induction b with
  | zero =>
    -- goal: (a + zero) * t = a * t + zero * t
    rw [add_zero a, zero_mul t, add_zero (a * t)]
  | succ h hd =>
    -- hd: (a + b) * h = a * h + b * h
    -- goal: (a + b) * succ(h) = a * succ(h) + b * succ(h)
    rw [add_succ a h, succ_mul (a + h), hd, succ_mul h t,
        add_assoc (a *t) (h * t)]

theorem mul_assoc (a b c : Unary) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
    simp only [mul_zero]
  | succ h hd =>
    -- hd: a * b * h = a * (b * h)
    -- goal: a * b * succ(h) = a * (b * succ(h))
    simp only [mul_succ]
    -- goal: a * b * h + a * b = a * (b * h + b)
    rw [hd]
    -- goal: a * (b * h) + a * b = a * (b * h + b)
    rw [mul_add]


