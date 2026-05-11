/-
  # Anti-diagonal F identities

  A structural identity that extracts `exp` from a single function `F` by
  evaluating it at three dilated points and combining the results algebraically.

  The function

      F(x) = exp(x) + log(x)

  is the "anti-diagonal" of the EML operator: where `eml(x, x) = exp(x) − log(x)`,
  here we package both transcendental halves into one expression,

      F(x) = exp(x) − log(1/x) = eml(x, x⁻¹).

  ## Main identity

  For `x ≠ 0`,

      exp(x) = (F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2) − 1.

  The `− log k` term in each difference exactly cancels the
  `log(kx) − log(x) = log k` shift, leaving only `exp(kx) − exp(x)`. The
  ratio then telescopes:
      (a³ − a) / (a² − a) = (a − 1)(a + 1) / (a − 1) = a + 1, with a = exp(x).
-/
import EML.Basic

open Real

namespace EML.Identities

/-- The "anti-diagonal" of EML: `F(x) = exp(x) + log(x) = eml(x, x⁻¹)`. -/
noncomputable def F (x : ℝ) : ℝ := exp x + log x

/-- F is exactly EML evaluated on the anti-diagonal `(x, x⁻¹)`. -/
theorem F_eq_eml_inv (x : ℝ) : F x = eml x x⁻¹ := by
  simp [F, eml, Real.log_inv]

/-- Key cancellation lemma. For `x ≠ 0` and `k > 0`,
    `F(k·x) − F(x) − log k = exp(k·x) − exp(x)`. -/
theorem F_dilate_sub {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F (k * x) - F x - log k = exp (k * x) - exp x := by
  simp only [F]
  rw [Real.log_mul hk.ne' hx]
  ring

/-- **Main identity.** For `x ≠ 0`,
    `exp(x) = (F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2) − 1`. -/
theorem exp_eq_F_quotient {x : ℝ} (hx : x ≠ 0) :
    exp x =
      (F (3 * x) - F x - log 3) / (F (2 * x) - F x - log 2) - 1 := by
  have h3 : F (3 * x) - F x - log 3 = exp (3 * x) - exp x :=
    F_dilate_sub hx (by norm_num : (0:ℝ) < 3)
  have h2 : F (2 * x) - F x - log 2 = exp (2 * x) - exp x :=
    F_dilate_sub hx (by norm_num : (0:ℝ) < 2)
  have e2 : exp (2 * x) = exp x * exp x := by
    rw [show (2 * x : ℝ) = x + x from by ring, Real.exp_add]
  have e3 : exp (3 * x) = exp x * exp x * exp x := by
    rw [show (3 * x : ℝ) = x + x + x from by ring, Real.exp_add, Real.exp_add]
  have hp : (0 : ℝ) < exp x := Real.exp_pos x
  have hexp_ne : exp x ≠ 1 := fun h =>
    hx (Real.exp_injective (h.trans Real.exp_zero.symm))
  have hne' : exp x - 1 ≠ 0 := sub_ne_zero.mpr hexp_ne
  rw [h3, h2, e2, e3]
  have hden : exp x * exp x - exp x ≠ 0 := by
    have hfac : exp x * exp x - exp x = exp x * (exp x - 1) := by ring
    rw [hfac]
    exact mul_ne_zero hp.ne' hne'
  field_simp
  ring

end EML.Identities
