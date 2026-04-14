/-
  # EML variants: EDL and -EML

  Paper equations (4a)-(4c) define three related operators:
    eml(x, y) = exp(x) - ln(y)    with constant 1    (4a)
    edl(x, y) = exp(x) / ln(y)    with constant e    (4b)
    -eml(y, x) = ln(x) - exp(y)   with constant -∞   (4c)

  Each generates all elementary functions. We define EDL and prove
  its basic properties, showing the parallel with EML.
-/
import EML.Basic

open Real

/-! ## EDL (Exp-Div-Log) operator -/

/-- The EDL operator: `edl(x, y) = exp(x) / ln(y)`.
    Paper equation (4b). Requires constant e (not 1). -/
noncomputable def edl (x y : ℝ) : ℝ := exp x / log y

/-- `exp(x) = edl(x, e)` since edl(x, e) = exp(x)/ln(e) = exp(x)/1 = exp(x). -/
theorem exp_eq_edl (x : ℝ) : exp x = edl x (exp 1) := by
  simp [edl, log_exp]

/-- `1 = edl(0, e)` since edl(0, e) = exp(0)/ln(e) = 1/1 = 1.
    So EDL with constant e can generate 1. -/
theorem one_eq_edl : (1 : ℝ) = edl 0 (exp 1) := by
  simp [edl, log_exp]

/-- `e^e = edl(e, e)` since edl(e, e) = exp(e)/ln(e) = e^e/1 = e^e. -/
theorem edl_e_e : edl (exp 1) (exp 1) = exp (exp 1) := by
  simp [edl, log_exp]

/-! ## Negated EML: -eml(y, x) = ln(x) - exp(y) -/

/-- The negated EML operator: `neml(x, y) = ln(x) - exp(y)`.
    Paper equation (4c): -eml(y, x) = ln(x) - exp(y).
    Requires constant -∞ (or equivalently, extended reals). -/
noncomputable def neml (x y : ℝ) : ℝ := log x - exp y

/-- neml is the negation of eml with swapped arguments. -/
theorem neml_eq_neg_eml (x y : ℝ) : neml x y = -eml y x := by
  simp [neml, eml]

/-! ## Relationships between variants -/

/-- `edl(x, y) * ln(y) = exp(x)` for ln(y) ≠ 0. -/
theorem edl_mul_log {y : ℝ} (x : ℝ) (hy : log y ≠ 0) :
    edl x y * log y = exp x := by
  simp [edl, div_mul_cancel₀ _ hy]

/-- `eml(x, y) + ln(y) = exp(x)` — EML recovers exp by adding back ln. -/
theorem eml_add_log (x y : ℝ) : eml x y + log y = exp x := by
  simp [eml]

/-- `eml(x, y) = (edl(x, y) - 1) * ln(y)` when ln(y) ≠ 0. -/
theorem eml_eq_edl_sub_one_mul_log {y : ℝ} (x : ℝ) (hy : log y ≠ 0) :
    eml x y = (edl x y - 1) * log y := by
  simp only [eml, edl]
  rw [sub_one_mul, div_mul_cancel₀ _ hy]
