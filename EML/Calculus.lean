/-
  # Calculus of EML

  Partial derivatives and monotonicity of eml(x, y) = exp(x) - ln(y).
-/
import EML.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Real

/-! ## Partial derivatives -/

/-- ∂/∂x eml(x, y) = exp(x). -/
theorem hasDerivAt_eml_fst (y : ℝ) (x : ℝ) :
    HasDerivAt (fun x => eml x y) (exp x) x := by
  unfold eml
  have := (hasDerivAt_exp x).sub (hasDerivAt_const x (log y))
  simp at this
  exact this

/-- ∂/∂y eml(x, y) = -1/y for y ≠ 0. -/
theorem hasDerivAt_eml_snd (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y => eml x y) (-y⁻¹) y := by
  unfold eml
  have := (hasDerivAt_const y (exp x)).sub (hasDerivAt_log hy)
  simp at this
  exact this

/-! ## Monotonicity -/

/-- eml is strictly monotone increasing in x. -/
theorem eml_strictMono_fst (y : ℝ) : StrictMono (fun x => eml x y) := by
  intro a b hab
  simp only [eml]
  linarith [exp_strictMono hab]

/-- eml is monotone increasing in x. -/
theorem eml_mono_fst (y : ℝ) : Monotone (fun x => eml x y) :=
  (eml_strictMono_fst y).monotone

/-- eml is strictly monotone decreasing in y for y > 0. -/
theorem eml_strictAnti_snd (x : ℝ) :
    StrictAntiOn (fun y => eml x y) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [eml, Set.mem_Ioi] at *
  linarith [log_lt_log ha hab]

/-! ## Injectivity -/

/-- eml is injective in x (for fixed y). -/
theorem eml_injective_fst (y : ℝ) :
    Function.Injective (fun x => eml x y) :=
  (eml_strictMono_fst y).injective

/-- eml is injective in y (for fixed x, on y > 0). -/
theorem eml_injective_snd (x : ℝ) :
    Set.InjOn (fun y => eml x y) (Set.Ioi 0) :=
  (eml_strictAnti_snd x).injOn
