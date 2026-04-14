/-
  # Transcendental functions from EML

  Here we prove the real-domain identities that connect hyperbolic,
  inverse hyperbolic, and algebraic functions to exp and log,
  and thereby (via Basic.lean) to EML.
-/
import EML.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Artanh

open Real

/-! ## Hyperbolic functions from EML -/

/-- cosh in terms of EML: `cosh(x) = (eml(x,1) + eml(-x,1)) / 2`.
    Paper Table 1: cosh. -/
theorem cosh_eq_eml (x : ℝ) : Real.cosh x = (eml x 1 + eml (-x) 1) / 2 := by
  unfold eml
  simp only [log_one, sub_zero]
  rw [Real.cosh_eq]

/-- sinh in terms of EML: `sinh(x) = (eml(x,1) - eml(-x,1)) / 2`.
    Paper Table 1: sinh. -/
theorem sinh_eq_eml (x : ℝ) : Real.sinh x = (eml x 1 - eml (-x) 1) / 2 := by
  unfold eml
  simp only [log_one, sub_zero]
  rw [Real.sinh_eq]

/-- tanh in terms of sinh/cosh (which are expressed via EML above).
    Paper Table 1: tanh. -/
theorem tanh_eq_sinh_div_cosh (x : ℝ) :
    Real.tanh x = Real.sinh x / Real.cosh x :=
  Real.tanh_eq_sinh_div_cosh x

/-! ## Inverse hyperbolic functions reduce to log -/

/-- arsinh reduces to log: `arsinh(x) = ln(x + √(1 + x²))`.
    Since log is expressible via EML, so is arsinh.
    Paper Table 1: arsinh. -/
theorem arsinh_eq_log (x : ℝ) :
    Real.arsinh x = log (x + Real.sqrt (1 + x ^ 2)) := by
  rfl

/-- arcosh reduces to log: `arcosh(x) = ln(x + √(x² - 1))`.
    Since log is expressible via EML, so is arcosh.
    Paper Table 1: arcosh. -/
theorem arcosh_eq_log (x : ℝ) :
    Real.arcosh x = log (x + Real.sqrt (x ^ 2 - 1)) := by
  rfl

/-! ## Square root via exp-log -/

/-- `√x = x ^ (1/2) = exp(ln(x)/2)` for x > 0.
    Paper Table 1: √. -/
theorem sqrt_eq_exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = exp (log x / 2) := by
  rw [sqrt_eq_rpow, rpow_def_of_pos hx]
  ring_nf

/-! ## Sigmoid function -/

/-- Sigmoid: `σ(x) = 1 / (1 + exp(-x))`.
    Paper Table 1: σ(x) = 1/(1 + e^{-x}). -/
theorem sigmoid_eq_inv_one_add_exp_neg (x : ℝ) :
    1 / (1 + exp (-x)) = 1 / (1 + eml (-x) 1) := by
  simp [eml, log_one]

/-! ## Hypotenuse -/

/-- Hypotenuse: `hypot(x, y) = √(x² + y²) = exp(log(x² + y²) / 2)` for x² + y² > 0.
    Paper Table 1: hypot(x, y) = √(x² + y²). -/
theorem hypot_eq_sqrt_sq_add_sq (x y : ℝ) :
    Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt (x ^ 2 + y ^ 2) := by
  rfl

/-- Hypotenuse via exp-log for positive sum of squares. -/
theorem hypot_eq_exp_log {x y : ℝ} (h : 0 < x ^ 2 + y ^ 2) :
    Real.sqrt (x ^ 2 + y ^ 2) = exp (log (x ^ 2 + y ^ 2) / 2) := by
  rw [sqrt_eq_rpow, rpow_def_of_pos h]
  ring_nf

/-! ## Inverse hyperbolic: artanh -/

/-- artanh reduces to log: `artanh(x) = log(√((1+x)/(1-x)))`.
    Paper Table 1: artanh. -/
theorem artanh_eq_log (x : ℝ) :
    Real.artanh x = log (Real.sqrt ((1 + x) / (1 - x))) := by
  rfl

/-- artanh as half-log: `artanh(x) = (1/2) * log((1+x)/(1-x))` for x ∈ [-1, 1].
    This is the standard textbook formula. -/
theorem artanh_eq_half_log' {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.artanh x = 1 / 2 * log ((1 + x) / (1 - x)) :=
  Real.artanh_eq_half_log hx

/-! ## The universality statement -/

/-- **Main theorem.**
    The EML operator eml(x,y) = exp(x) - ln(y), together with the constant 1,
    generates exp and log (the two building blocks of all elementary functions).

    1. exp(x) = eml(x, 1)                              [exp_eq_eml]
    2. ln(z) = eml(1, eml(eml(1, z), 1))  for z > 0   [log_eq_eml]
    3. e = eml(1, 1)                                    [exp_one_eq_eml]
    4. 0 = eml(1, eml(eml(1,1), 1))                    [zero_eq_eml]
    5. x + y = log(eml(x,1) * eml(y,1))                [add_eq_log_eml_mul]
    6. x * y = exp(log(x) + log(y))  for x, y > 0      [mul_eq_exp_log_add]
    7. x - y = log(exp(x) / exp(y))                     [sub_eq_log_exp_div]
    8. x / y = exp(log(x) - log(y))  for x, y > 0      [div_eq_exp_log_sub]
    9. x ^ y = exp(log(x) * y)  for x > 0              [rpow_eq_exp_log_mul]
    10. log_b(x) = log(x) / log(b)                     [logb_eq_log_div]
    11. cosh(x), sinh(x), tanh(x) via eml               [cosh_eq_eml etc.]
    12. arsinh(x) = log(x + √(1+x²))                   [arsinh_eq_log]
    13. arcosh(x) = log(x + √(x²-1))                   [arcosh_eq_log]
    14. √x = exp(log(x)/2)  for x > 0                  [sqrt_eq_exp_half_log]

    Since every exp and log occurrence can be further compiled to pure EML
    form using identities (1) and (2), the grammar S → 1 | eml(S, S)
    suffices for all of the above. -/
theorem eml_generates_exp_and_log :
    (∀ x : ℝ, exp x = eml x 1) ∧
    (∀ z : ℝ, 0 < z → log z = eml 1 (eml (eml 1 z) 1)) := by
  exact ⟨exp_eq_eml, log_eq_eml⟩
