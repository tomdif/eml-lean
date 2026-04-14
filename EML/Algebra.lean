/-
  # Algebraic structure of EML

  The EML operator eml(x,y) = exp(x) - ln(y) is non-commutative,
  non-associative, and has no identity element.
-/
import EML.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open Real

/-! ## Non-commutativity -/

/-- EML is non-commutative: eml(0, 1) = 1 ≠ e = eml(1, 0). -/
theorem eml_not_comm : ¬ ∀ x y : ℝ, eml x y = eml y x := by
  intro h
  have := h 0 1
  simp [eml, log_one, log_zero] at this
  linarith [exp_one_gt_two]

/-! ## Non-associativity -/

/-- EML is non-associative: eml(eml(0,1),1) = e ≠ 0 = eml(0,eml(1,1)). -/
theorem eml_not_assoc :
    ¬ ∀ a b c : ℝ, eml (eml a b) c = eml a (eml b c) := by
  intro h
  have := h 0 1 1
  simp only [eml, log_one, sub_zero, log_exp] at this
  -- this : exp(exp 0) = exp 0 - 1. Since exp 0 = 1, this gives exp 1 = 0.
  simp [exp_zero] at this

/-! ## No identity element -/

/-- No left identity for EML. -/
theorem eml_no_left_identity : ¬ ∃ e : ℝ, ∀ x : ℝ, eml e x = x := by
  intro ⟨e, h⟩
  have h1 := h 1
  simp [eml, log_one] at h1
  -- h1 : exp e = 1, so e = 0
  have h2 := h (exp 1)
  simp [eml, h1, log_exp] at h2
  linarith [exp_pos 1]

/-- No right identity for EML. -/
theorem eml_no_right_identity : ¬ ∃ e : ℝ, ∀ x : ℝ, eml x e = x := by
  intro ⟨e, h⟩
  have h0 := h 0
  have h1 := h 1
  simp [eml] at h0 h1
  -- h0 : 1 - log e = 0, h1 : exp 1 - log e = 1
  -- From h0: log e = 1. Substituting into h1: exp 1 - 1 = 1, i.e. exp 1 = 2.
  linarith [exp_one_gt_two]

/-- Combined: EML has no two-sided identity element. -/
theorem eml_no_identity :
    ¬ ∃ e : ℝ, (∀ x : ℝ, eml e x = x) ∧ (∀ x : ℝ, eml x e = x) := by
  intro ⟨e, hleft, _⟩
  exact eml_no_left_identity ⟨e, hleft⟩
