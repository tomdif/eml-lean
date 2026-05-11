/-
  # The anti-diagonal F identity family

  Extensions of the main identity from `EML.Identities`. The underlying
  mechanism is always the same:

      F(k·x) − F(x) − log k = exp(k·x) − exp(x).

  Combining this evaluation at different dilation factors and via different
  finite-difference patterns yields an infinite zoo of clean identities.

  ## Contents

  • `exp_mul_eq_F_quotient` — for every real `m ≥ 2`,

        exp((m-1)·x) = (F((2m-1)·x) − F(x) − log(2m-1))
                     / (F(m·x)     − F(x) − log m) − 1.

    Specializes to the image's identity at m = 2.

  • `F_pow` — the power-function anti-diagonal `F_pow(a, x) = x^a + log x`
    and the constant-ratio identity:

        (F_pow_a(3x) − F_pow_a(x) − log 3) · (2^a − 1)
      = (F_pow_a(2x) − F_pow_a(x) − log 2) · (3^a − 1)

    (a non-divided form; the implied ratio (3^a − 1)/(2^a − 1) is constant
    in x and *encodes the exponent a*.)

  • `F_second_diff` — second-order finite difference of F on `{x, 2x, 3x}`
    extracts `exp(x)·(exp(x) − 1)²`:

        F(3x) − 2 F(2x) + F(x) = exp(x)·(exp(x) − 1)² + log 3 − 2 log 2.

  • `sinh_eq_F_diff` — hyperbolic sine from the parity-reflection of F:

        sinh(x) = (F(x) − F(−x)) / 2.

  • `cosh_eq_F_sum` — hyperbolic cosine, complementary:

        cosh(x) = (F(x) + F(−x)) / 2 − log x.
-/
import EML.Identities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace EML.Identities

/-! ## Cyclotomic-family generalization -/

/-- **Generalized anti-diagonal identity.** For `x ≠ 0` and any real `m ≥ 2`,

      exp((m-1)·x) = (F((2m-1)·x) − F(x) − log(2m-1))
                   / (F(m·x)     − F(x) − log m) − 1.

    The image's identity is the case `m = 2`. Larger `m` extract higher
    powers of `exp(x)`:
      m = 3 ⇒ recovers exp(2x) via F at {x, 3x, 5x}
      m = 4 ⇒ recovers exp(3x) via F at {x, 4x, 7x} -/
theorem exp_mul_eq_F_quotient {x m : ℝ} (hx : x ≠ 0) (hm : 2 ≤ m) :
    exp ((m - 1) * x) =
      (F ((2 * m - 1) * x) - F x - log (2 * m - 1)) /
        (F (m * x) - F x - log m) - 1 := by
  have hm_pos : (0 : ℝ) < m := by linarith
  have h2m_pos : (0 : ℝ) < 2 * m - 1 := by linarith
  have hm1_pos : (0 : ℝ) < m - 1 := by linarith
  have hm1x_ne : (m - 1) * x ≠ 0 := mul_ne_zero hm1_pos.ne' hx
  have hnum : F ((2 * m - 1) * x) - F x - log (2 * m - 1)
                = exp ((2 * m - 1) * x) - exp x :=
    F_dilate_sub hx h2m_pos
  have hden : F (m * x) - F x - log m = exp (m * x) - exp x :=
    F_dilate_sub hx hm_pos
  rw [hnum, hden]
  have e1 : exp ((2 * m - 1) * x) = exp ((m - 1) * x) * exp (m * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : exp (m * x) = exp ((m - 1) * x) * exp x := by
    rw [← Real.exp_add]; congr 1; ring
  have hp : (0 : ℝ) < exp x := Real.exp_pos x
  have hexp_ne_one : exp ((m - 1) * x) ≠ 1 := fun h =>
    hm1x_ne (Real.exp_injective (h.trans Real.exp_zero.symm))
  have hsub_ne : exp ((m - 1) * x) - 1 ≠ 0 := sub_ne_zero.mpr hexp_ne_one
  rw [e1, e2]
  have hden_ne : exp ((m - 1) * x) * exp x - exp x ≠ 0 := by
    have hfac : exp ((m - 1) * x) * exp x - exp x
                  = exp x * (exp ((m - 1) * x) - 1) := by ring
    rw [hfac]
    exact mul_ne_zero hp.ne' hsub_ne
  field_simp
  ring

/-! ## Power-function anti-diagonal -/

/-- The power-function anti-diagonal: `F_pow(a, x) = x^a + log x`. -/
noncomputable def F_pow (a x : ℝ) : ℝ := x ^ a + log x

/-- Dilation cancellation for `F_pow`: for `x > 0` and `k > 0`,
    `F_pow(a, k·x) − F_pow(a, x) − log k = (k^a − 1)·x^a`. -/
theorem F_pow_dilate_sub {a x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    F_pow a (k * x) - F_pow a x - log k = (k ^ a - 1) * x ^ a := by
  simp only [F_pow]
  rw [Real.mul_rpow hk.le hx.le, Real.log_mul hk.ne' hx.ne']
  ring

/-- **Constant-ratio identity for the power-function anti-diagonal.**
    Stated in cross-multiplied form (no nonzero hypothesis on `2^a − 1`):

      (F_pow_a(3x) − F_pow_a(x) − log 3) · (2^a − 1)
    = (F_pow_a(2x) − F_pow_a(x) − log 2) · (3^a − 1).

    The implied ratio `(F_pow_a(3x) − …)/(F_pow_a(2x) − …) = (3^a − 1)/(2^a − 1)`
    is independent of `x` and encodes the exponent `a`. -/
theorem F_pow_ratio_eq {x a : ℝ} (hx : 0 < x) :
    (F_pow a (3 * x) - F_pow a x - log 3) * ((2 : ℝ) ^ a - 1)
      = (F_pow a (2 * x) - F_pow a x - log 2) * ((3 : ℝ) ^ a - 1) := by
  have h3 := F_pow_dilate_sub (a := a) hx (by norm_num : (0:ℝ) < 3)
  have h2 := F_pow_dilate_sub (a := a) hx (by norm_num : (0:ℝ) < 2)
  rw [h3, h2]
  ring

/-! ## Second-order finite difference -/

/-- **Second-difference identity.** For `x ≠ 0`,

      F(3x) − 2·F(2x) + F(x) = exp(x)·(exp(x) − 1)² + log 3 − 2·log 2.

    The log terms collapse because the coefficients `(1, −2, 1)` sum to zero;
    only the constant `log 3 − 2·log 2 = log(3/4)` survives. The exp part
    becomes `e^{3x} − 2 e^{2x} + e^x = e^x (e^x − 1)²`. -/
theorem F_second_diff {x : ℝ} (hx : x ≠ 0) :
    F (3 * x) - 2 * F (2 * x) + F x
      = exp x * (exp x - 1) ^ 2 + log 3 - 2 * log 2 := by
  simp only [F]
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hx,
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx]
  have e3 : exp (3 * x) = exp x * exp x * exp x := by
    rw [show (3 * x : ℝ) = x + x + x from by ring, Real.exp_add, Real.exp_add]
  have e2 : exp (2 * x) = exp x * exp x := by
    rw [show (2 * x : ℝ) = x + x from by ring, Real.exp_add]
  rw [e3, e2]
  ring

/-! ## Parity-reflection identities (sinh / cosh) -/

/-- **Hyperbolic-sine from F.** The log piece in `F = exp + log` is even
    (`log(−x) = log x`), so it drops out of `F(x) − F(−x)`, leaving
    `exp(x) − exp(−x) = 2·sinh(x)`. Holds for all real `x`. -/
theorem sinh_eq_F_diff (x : ℝ) : Real.sinh x = (F x - F (-x)) / 2 := by
  simp only [F, Real.log_neg_eq_log]
  rw [Real.sinh_eq]
  ring

/-- **Hyperbolic-cosine from F.** Complementary identity: the log piece
    survives in the sum and is removed by subtracting `log x` once. -/
theorem cosh_eq_F_sum (x : ℝ) : Real.cosh x = (F x + F (-x)) / 2 - log x := by
  simp only [F, Real.log_neg_eq_log]
  rw [Real.cosh_eq]
  ring

end EML.Identities
