/-
  # Fixed points and zeros of EML
-/
import EML.Basic

open Real

/-! ## Zero set of EML -/

/-- `eml(a, b) = 0 ↔ exp(a) = log(b)`. -/
theorem eml_eq_zero_iff (a b : ℝ) :
    eml a b = 0 ↔ exp a = log b := by
  simp [eml, sub_eq_zero]

/-- `eml(a, exp(exp(a))) = 0` for all a. -/
theorem eml_zero_at (a : ℝ) : eml a (exp (exp a)) = 0 := by
  simp [eml, log_exp]

/-- If eml(a, b) = 0 and b > 0, then b = exp(exp(a)). -/
theorem eml_zero_implies {a b : ℝ} (hb : 0 < b) (h : eml a b = 0) :
    b = exp (exp a) := by
  rw [eml_eq_zero_iff] at h
  rw [← exp_log hb, h]

/-! ## Level sets -/

/-- `eml(a, b) = c ↔ b = exp(exp(a) - c)` for b > 0. -/
theorem eml_eq_iff {a b c : ℝ} (hb : 0 < b) :
    eml a b = c ↔ b = exp (exp a - c) := by
  constructor
  · intro h
    have : log b = exp a - c := by simp [eml] at h; linarith
    rw [← this, exp_log hb]
  · intro h; simp [eml, h, log_exp]

/-! ## Fixed points: eml(x, x) = x -/

/-- `eml(x, x) = x ↔ exp(x) - x = log(x)`. -/
theorem eml_fixed_point_iff (x : ℝ) :
    eml x x = x ↔ exp x - x = log x := by
  constructor
  · intro h; simp [eml] at h; linarith
  · intro h; simp [eml]; linarith

/-- At a fixed point with x > 0, we have x > 1.
    Proof: exp(x) - x = log(x), and exp(x) > 1 + x for x > 0,
    so log(x) > 1, hence x > e > 1. -/
theorem eml_fixed_point_gt_one {x : ℝ} (hx : 0 < x)
    (hfp : eml x x = x) : 1 < x := by
  rw [eml_fixed_point_iff] at hfp
  have hne : x ≠ 0 := ne_of_gt hx
  have hexp : x + 1 < exp x := add_one_lt_exp hne
  have hlog : 1 < log x := by linarith
  rw [show (1 : ℝ) = log (exp 1) from (log_exp 1).symm] at hlog
  rw [log_lt_log_iff (exp_pos 1) hx] at hlog
  linarith [add_one_lt_exp (one_ne_zero)]

/-! ## Self-application identities -/

/-- `eml(x, eml(x, 1)) = exp(x) - x`. -/
theorem eml_self_app (x : ℝ) : eml x (eml x 1) = exp x - x := by
  simp [eml, log_one, sub_zero, log_exp]

/-- `eml(0, eml(0, 1)) = 1`. -/
theorem eml_self_app_zero : eml 0 (eml 0 1) = 1 := by
  simp [eml, log_one]

/-- `eml(eml(x, 1), x) = exp(exp(x)) - log(x)`. -/
theorem eml_exp_self (x : ℝ) :
    eml (eml x 1) x = exp (exp x) - log x := by
  simp [eml, log_one, sub_zero]
