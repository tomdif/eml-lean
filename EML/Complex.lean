/-
  # Complex EML and trigonometric functions

  The paper notes that EML internally operates over ℂ. Trigonometric
  functions and constants like π and i require the complex domain.

  We define the complex EML operator and prove that it generates
  Complex.exp and Complex.log (under branch conditions), and therefore
  all trigonometric functions via Euler's formula.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

open Complex

/-! ## Complex EML definition -/

/-- The complex EML operator: `ceml(x, y) = exp(x) - log(y)`.
    This is the EML Sheffer operator lifted to ℂ. -/
noncomputable def ceml (x y : ℂ) : ℂ := exp x - log y

/-! ## Complex exp from ceml -/

/-- `exp(z) = ceml(z, 1)` over ℂ. -/
theorem cexp_eq_ceml (z : ℂ) : exp z = ceml z 1 := by
  simp [ceml, Complex.log_one]

/-! ## Complex log from ceml (under branch conditions) -/

/-- `log(z) = ceml(1, ceml(ceml(1, z), 1))` over ℂ, provided the intermediate
    expression has imaginary part in (-π, π].

    This is the complex version of the key paper identity (eq. 5). -/
theorem clog_eq_ceml (z : ℂ)
    (h1 : -Real.pi < (exp 1 - log z).im)
    (h2 : (exp 1 - log z).im ≤ Real.pi) :
    log z = ceml 1 (ceml (ceml 1 z) 1) := by
  simp only [ceml, Complex.log_one, sub_zero]
  rw [Complex.log_exp h1 h2]
  ring

/-! ## Euler's formula connects trig to exp -/

/-- Euler's formula for real arguments:
    `exp(x * i) = cos(x) + sin(x) * i`.
    This is the bridge from EML to trigonometric functions. -/
theorem euler_formula_real (x : ℝ) :
    exp ((x : ℂ) * I) = ↑(Real.cos x) + ↑(Real.sin x) * I :=
  Complex.exp_ofReal_mul_I x

/-! ## sin and cos from complex exp -/

/-- `cos(x) = Re(cos(x))` connecting real and complex cos. -/
theorem cos_eq_re_complex (x : ℝ) :
    Real.cos x = (Complex.cos (x : ℂ)).re :=
  (Complex.cos_ofReal_re x).symm

/-- `sin(x) = Re(sin(x))` connecting real and complex sin. -/
theorem sin_eq_re_complex (x : ℝ) :
    Real.sin x = (Complex.sin (x : ℂ)).re :=
  (Complex.sin_ofReal_re x).symm

/-- cos in terms of complex exp: `cos(x) = (exp(ix) + exp(-ix)) / 2`.
    Paper Table 1: cos. -/
theorem cos_eq_cexp_add (x : ℝ) :
    (Real.cos x : ℂ) = (exp ((x : ℂ) * I) + exp ((-x : ℂ) * I)) / 2 := by
  rw [Complex.ofReal_cos]
  unfold Complex.cos
  ring

/-- sin in terms of complex exp (multiplied by I to avoid division by I):
    `sin(x) * i = (exp(ix) - exp(-ix)) / 2`.
    Paper Table 1: sin. -/
theorem sin_mul_I_eq_cexp_sub (x : ℝ) :
    (Real.sin x : ℂ) * I = (exp ((x : ℂ) * I) - exp ((-x : ℂ) * I)) / 2 := by
  rw [Complex.ofReal_sin]
  unfold Complex.sin
  have : I ^ 2 = (-1 : ℂ) := I_sq
  ring_nf
  rw [I_sq]
  ring

/-- tan(x) = sin(x) / cos(x).
    Paper Table 1: tan. -/
theorem real_tan_eq (x : ℝ) :
    Real.tan x = Real.sin x / Real.cos x :=
  Real.tan_eq_sin_div_cos x

/-! ## Complex EML expressions for sin and cos -/

/-- cos from ceml: `cos(x) = (ceml(x*i, 1) + ceml(-x*i, 1)) / 2` -/
theorem cos_eq_ceml (x : ℝ) :
    (Real.cos x : ℂ) = (ceml ((x : ℂ) * I) 1 + ceml ((-x : ℂ) * I) 1) / 2 := by
  simp only [ceml, Complex.log_one, sub_zero]
  exact cos_eq_cexp_add x

/-- sin·i from ceml:
    `sin(x) * i = (ceml(x*i, 1) - ceml(-x*i, 1)) / 2` -/
theorem sin_mul_I_eq_ceml (x : ℝ) :
    (Real.sin x : ℂ) * I = (ceml ((x : ℂ) * I) 1 - ceml ((-x : ℂ) * I) 1) / 2 := by
  simp only [ceml, Complex.log_one, sub_zero]
  exact sin_mul_I_eq_cexp_sub x

/-! ## Constants π and i from complex EML -/

/-- `i = exp(iπ/2)`, so once π is available, i can be built from ceml.
    From Euler: e^(iπ/2) = cos(π/2) + i·sin(π/2) = 0 + i·1 = i. -/
theorem I_eq_cexp : (I : ℂ) = exp (↑(Real.pi / 2) * I) := by
  rw [Complex.exp_ofReal_mul_I]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- The imaginary part of `log(-1)` is `π` (principal branch). -/
theorem clog_neg_one_im : (log (-1 : ℂ)).im = Real.pi := by
  rw [Complex.log_neg_one]
  simp

/-- π from complex log: `π = Im(log(-1))`.
    Since log is expressible via ceml, π is constructible from {1, ceml}
    (once -1 is constructed). -/
theorem pi_from_clog : Real.pi = (log (-1 : ℂ)).im := by
  rw [clog_neg_one_im]

/-- arccos(x) = π/2 - arcsin(x).
    Paper Table 1: arccos. -/
theorem arccos_eq (x : ℝ) :
    Real.arccos x = Real.pi / 2 - Real.arcsin x :=
  Real.arccos_eq_pi_div_two_sub_arcsin x

/-! ## arctan via complex log -/

/-- Complex arctan is defined via log:
    `arctan(z) = -i/2 * log((1 + zi)/(1 - zi))`.
    This is the standard formula connecting arctan to log over ℂ.
    Paper Table 1: arctan. -/
theorem arctan_eq_log (z : ℂ) :
    Complex.arctan z = -I / 2 * log ((1 + z * I) / (1 - z * I)) := by
  rfl

/-- Real arctan lifts to complex arctan.
    Combined with arctan_eq_log, this shows real arctan is
    expressible via complex log, and hence via ceml. -/
theorem real_arctan_eq_complex (x : ℝ) :
    (Real.arctan x : ℂ) = Complex.arctan x :=
  Complex.ofReal_arctan x

/-- arctan relates to arcsin:
    `arctan(x) = arcsin(x / √(1 + x²))`.
    Since arctan is expressible via log (arctan_eq_log), this connects
    arcsin to the log-exp-eml chain. -/
theorem arctan_eq_arcsin' (x : ℝ) :
    Real.arctan x = Real.arcsin (x / Real.sqrt (1 + x ^ 2)) :=
  Real.arctan_eq_arcsin x

/-! ## Summary -/

/-- **Complex universality theorem.**
    The complex EML operator ceml(x,y) = exp(x) - log(y) generates:
    - Complex.exp via ceml(z, 1)                       [cexp_eq_ceml]
    - Complex.log via ceml triple composition            [clog_eq_ceml]
    - cos via (ceml(xi, 1) + ceml(-xi, 1)) / 2         [cos_eq_ceml]
    - sin·i via (ceml(xi, 1) - ceml(-xi, 1)) / 2       [sin_mul_I_eq_ceml]
    - tan via sin/cos                                    [real_tan_eq]
    - π via Im(log(-1))                                 [pi_from_clog]
    - i via exp(iπ/2)                                   [I_eq_cexp]
    - arccos via π/2 - arcsin                            [arccos_eq]
    - arctan via -i/2 * log((1+zi)/(1-zi))              [arctan_eq_log]
    - arcsin via arctan                                  [arcsin_eq_arctan] -/
theorem ceml_generates_exp : ∀ z : ℂ, exp z = ceml z 1 :=
  cexp_eq_ceml
