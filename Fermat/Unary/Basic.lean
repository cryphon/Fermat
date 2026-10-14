inductive Unary where
  | zero : Unary
  | succ : Unary → Unary
  deriving Repr

namespace Unary

def one : Unary := succ zero

def add : Unary → Unary → Unary
  | a, zero => a
  | a, succ b => succ (add a b)

instance : Add Unary := {add}

def mul : Unary → Unary → Unary
  | _, zero => zero
  | a, succ b => mul a b + a

instance : Mul Unary := {mul}

theorem add_zero (a : Unary)    : a + zero = a := rfl
theorem add_succ (a b : Unary)  : a + succ b = succ (a + b) := rfl
theorem mul_zero (a : Unary)    : a * zero = zero := rfl
theorem mul_succ (a b : Unary) : a * succ b = a * b + a := rfl
theorem one_eq_succ_zero : one = succ zero := rfl
theorem succ_eq_add_one (a : Unary) : succ a = a + one := rfl

end Unary
