/-
  # Arithmetic operations from EML

  We show that once exp and ln are available (proved in Basic.lean),
  all arithmetic operations can be expressed via eml.
-/
import EML.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Real

/-! ## Addition via exp-log -/

/-- Addition via exp-log: `x + y = ln(exp(x) * exp(y))` -/
theorem add_eq_log_exp_mul (x y : ℝ) :
    x + y = log (exp x * exp y) := by
  rw [← exp_add, log_exp]

/-- Addition in EML form: `x + y = log(eml(x, 1) * eml(y, 1))` -/
theorem add_eq_log_eml_mul (x y : ℝ) :
    x + y = log (eml x 1 * eml y 1) := by
  rw [eml_mul, log_exp]

/-! ## Subtraction via exp-log -/

/-- Subtraction via exp-log: `x - y = ln(exp(x) / exp(y))` -/
theorem sub_eq_log_exp_div (x y : ℝ) :
    x - y = log (exp x / exp y) := by
  rw [← exp_sub, log_exp]

/-! ## Multiplication via exp-log -/

/-- Multiplication via exp-log: `x * y = exp(ln(x) + ln(y))` for x, y > 0. -/
theorem mul_eq_exp_log_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * y = exp (log x + log y) := by
  rw [exp_add, exp_log hx, exp_log hy]

/-! ## Division via exp-log -/

/-- Division via exp-log: `x / y = exp(ln(x) - ln(y))` for x, y > 0. -/
theorem div_eq_exp_log_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x / y = exp (log x - log y) := by
  rw [exp_sub, exp_log hx, exp_log hy]

/-! ## Negation -/

/-- Negation via exp-log: `-x = ln(1 / exp(x))` -/
theorem neg_eq_log_inv_exp (x : ℝ) :
    -x = log (1 / exp x) := by
  rw [one_div, log_inv, log_exp]

/-! ## Reciprocal -/

/-- Reciprocal via exp-log: `x⁻¹ = exp(-ln(x))` for x > 0. -/
theorem inv_eq_exp_neg_log {x : ℝ} (hx : 0 < x) :
    x⁻¹ = exp (-log x) := by
  rw [exp_neg, exp_log hx]

/-! ## Real exponentiation -/

/-- Real power via exp-log: `x ^ y = exp(ln(x) * y)` for x > 0.
    Paper Table 1: pow(x, y) = x^y. -/
theorem rpow_eq_exp_log_mul {x : ℝ} (hx : 0 < x) (y : ℝ) :
    x ^ y = exp (log x * y) := by
  exact rpow_def_of_pos hx y

/-! ## Logarithm with arbitrary base -/

/-- Arbitrary-base logarithm: `log_b(x) = ln(x) / ln(b)`.
    Paper Table 1: log_x(y). -/
theorem logb_eq_log_div (b x : ℝ) :
    logb b x = log x / log b := by
  rfl

/-! ## Average -/

/-- Arithmetic mean: `avg(x,y) = (x + y) / 2`.
    Paper Table 1: avg(x, y) = (x + y) / 2. -/
theorem avg_eq_add_div_two (x y : ℝ) :
    (x + y) / 2 = log (eml x 1 * eml y 1) / 2 := by
  rw [eml_mul, log_exp]

/-! ## Square -/

/-- Square via exp-log: `x ^ 2 = exp(2 * ln(x))` for x > 0.
    Paper Table 1: sqr(x) = x². -/
theorem sq_eq_exp_two_log {x : ℝ} (hx : 0 < x) :
    x ^ 2 = exp (2 * log x) := by
  rw [← rpow_natCast x 2, rpow_def_of_pos hx]
  ring_nf

/-! ## Half -/

/-- Half via exp-log: `x / 2 = exp(ln(x) - ln(2))` for x > 0.
    Paper Table 1: half(x). -/
theorem half_eq_exp_log_sub_log2 {x : ℝ} (hx : 0 < x) :
    x / 2 = exp (log x - log 2) := by
  rw [exp_sub, exp_log hx, exp_log (by norm_num : (0:ℝ) < 2)]

/-! ## Composition: all arithmetic reduces to eml -/

/-- Direct EML expression for addition, fully expanded. -/
theorem add_via_eml_chain (x y : ℝ) :
    x + y = log (eml x 1 * eml y 1) := by
  rw [eml_mul, log_exp]
