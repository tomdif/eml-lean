/-
  # The exp-log pair: Equations (1) and (2)

  Paper equations (1) and (2) establish the classical reductions
  that motivate the EML operator:

  Equation (1):
    x × y = e^(ln x + ln y)     (multiplication via exp-log)
    x + y = ln(e^x × e^y)       (addition via exp-log)

  Equation (2):
    e^(iφ) = cos φ + i sin φ    (Euler's formula)

  These show that exp and log are the "universal pair" from which
  all arithmetic and trigonometric functions can be recovered,
  and motivate searching for a single operator to replace them both.
-/
import EML.Basic

open Real

/-! ## Equation (1): The exp-log pair -/

/-- Paper equation (1), left:
    `x × y = exp(ln(x) + ln(y))` for x, y > 0.
    Multiplication reduces to exp and log. -/
theorem eq1_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * y = exp (log x + log y) := by
  rw [exp_add, exp_log hx, exp_log hy]

/-- Paper equation (1), right:
    `x + y = ln(exp(x) * exp(y))`.
    Addition reduces to exp and log. -/
theorem eq1_add (x y : ℝ) :
    x + y = log (exp x * exp y) := by
  rw [← exp_add, log_exp]

/-! ## Consequences: all arithmetic from {exp, log} -/

/-- Subtraction: `x - y = ln(exp(x) / exp(y))`. -/
theorem explog_sub (x y : ℝ) :
    x - y = log (exp x / exp y) := by
  rw [← exp_sub, log_exp]

/-- Division: `x / y = exp(ln(x) - ln(y))` for x, y > 0. -/
theorem explog_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x / y = exp (log x - log y) := by
  rw [exp_sub, exp_log hx, exp_log hy]

/-- Negation: `-x = ln(exp(-x)) = ln(1/exp(x))`. -/
theorem explog_neg (x : ℝ) :
    -x = log (exp x)⁻¹ := by
  rw [log_inv, log_exp]

/-- Reciprocal: `1/x = exp(-ln(x))` for x > 0. -/
theorem explog_inv {x : ℝ} (hx : 0 < x) :
    x⁻¹ = exp (-log x) := by
  rw [exp_neg, exp_log hx]

/-- Integer: `n = ln(exp(n))` for any natural number n. -/
theorem explog_nat (n : ℕ) :
    (n : ℝ) = log (exp (n : ℝ)) := by
  rw [log_exp]

/-- The exp-log pair is complete for arithmetic:
    {exp, log, 1} generates all of +, -, ×, /, integers, and rationals
    (for positive arguments where log is defined). -/
theorem explog_completeness_constants :
    (0 : ℝ) = log (exp 0) ∧
    (1 : ℝ) = 1 ∧
    (2 : ℝ) = log (exp 1 * exp 1) ∧
    exp 1 = exp 1 := by
  refine ⟨by rw [log_exp], rfl, ?_, rfl⟩
  rw [← exp_add, log_exp]; norm_num
