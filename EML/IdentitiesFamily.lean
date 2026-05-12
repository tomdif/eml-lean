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

/-! ## Inversion-reflection identities (x ↔ x⁻¹) -/

/-- **Inversion-sum identity.** For all `x ≠ 0`,

      F(x) + F(x⁻¹) = exp(x) + exp(x⁻¹).

    The log piece is *odd under inversion* (`log(1/x) = −log x`), so it
    cancels entirely in the sum, leaving only the exp piece evaluated at
    `x` and `1/x`. -/
theorem F_inv_sum {x : ℝ} (_hx : x ≠ 0) :
    F x + F x⁻¹ = exp x + exp x⁻¹ := by
  simp only [F, Real.log_inv]
  ring

/-- **Inversion-difference identity.** For all `x`,

      F(x) − F(x⁻¹) = exp(x) − exp(x⁻¹) + 2·log(x).

    The log piece doubles under the inversion-difference. -/
theorem F_inv_diff (x : ℝ) :
    F x - F x⁻¹ = exp x - exp x⁻¹ + 2 * log x := by
  simp only [F, Real.log_inv]
  ring

/-! ## Dilation cocycle composition -/

/-- **Cocycle composition.** The "dilation difference" `c(k, x) = F(k·x) − F(x)`
    satisfies the 1-cocycle relation: composing dilations adds the differences.

      [F((a·b)·x) − F(x)] = [F(a·x) − F(x)] + [F(a·b·x) − F(a·x)]

    Equivalently, the `log k` and `exp(k·x) − exp(x)` pieces both compose
    correctly under successive dilations `x ↦ a·x ↦ ab·x`. -/
theorem F_dilate_cocycle {x a b : ℝ} (hx : x ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    F (a * b * x) - F x - log (a * b) =
      (F (a * x) - F x - log a) + (F (a * b * x) - F (a * x) - log b) := by
  -- Both sides reduce to exp(abx) - exp(x) via F_dilate_sub.
  have hab : F (a * b * x) - F x - log (a * b) = exp (a * b * x) - exp x := by
    have : F ((a * b) * x) - F x - log (a * b) = exp ((a * b) * x) - exp x :=
      F_dilate_sub hx (mul_pos ha hb)
    simpa [mul_assoc] using this
  have h_a : F (a * x) - F x - log a = exp (a * x) - exp x :=
    F_dilate_sub hx ha
  have h_b : F (a * b * x) - F (a * x) - log b = exp (a * b * x) - exp (a * x) := by
    -- Recognize a*b*x = b * (a*x); F_dilate_sub at the point (a*x) with k = b.
    have hax_ne : a * x ≠ 0 := mul_ne_zero ha.ne' hx
    have := F_dilate_sub hax_ne hb
    -- this : F (b * (a * x)) - F (a * x) - log b = exp (b * (a * x)) - exp (a * x)
    have heq : b * (a * x) = a * b * x := by ring
    rw [heq] at this
    exact this
  rw [hab, h_a, h_b]
  ring

/-! ## The negative anti-diagonal G = exp − log = eml(x, x)

EML has *two* "anti-diagonals":
  • `F(x) = exp(x) + log(x) = eml(x, x⁻¹)` (positive, the one used so far)
  • `G(x) = exp(x) − log(x) = eml(x, x)` (negative; this is literally the
    EML-diagonal evaluated at the same argument twice, already studied in
    `FixedPoints.lean`).

`G` carries the dilation cocycle with the opposite sign (`α = −1` instead of
`α = +1`), giving a parallel mechanism: the same main identity, with a sign
flip on the `log k` term. -/

/-- The negative anti-diagonal of EML: `G(x) = exp(x) − log(x) = eml(x, x)`. -/
noncomputable def G (x : ℝ) : ℝ := exp x - log x

/-- `G` is exactly `eml` on the diagonal. -/
theorem G_eq_eml_diag (x : ℝ) : G x = eml x x := by
  simp [G, eml]

/-- **Mirror cancellation lemma for `G`.** For `x ≠ 0` and `k > 0`,

      G(k·x) − G(x) + log(k) = exp(k·x) − exp(x).

  The sign on the `log(k)` term is **opposite** to `F_dilate_sub`'s (which
  has `− log k`), reflecting that `G`'s log-component has sign `α = −1`. -/
theorem G_dilate_sub {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    G (k * x) - G x + log k = exp (k * x) - exp x := by
  simp only [G]
  rw [Real.log_mul hk.ne' hx]
  ring

/-- **Mirror main identity** (for `x ≠ 0`):

      exp(x) = (G(3x) − G(x) + log 3) / (G(2x) − G(x) + log 2) − 1.

  Same shape as `exp_eq_F_quotient` but with `+ log k` instead of `− log k`. -/
theorem exp_eq_G_quotient {x : ℝ} (hx : x ≠ 0) :
    Real.exp x =
      (G (3 * x) - G x + Real.log 3) / (G (2 * x) - G x + Real.log 2) - 1 := by
  have h3 : G (3 * x) - G x + Real.log 3 = Real.exp (3 * x) - Real.exp x :=
    G_dilate_sub hx (by norm_num : (0:ℝ) < 3)
  have h2 : G (2 * x) - G x + Real.log 2 = Real.exp (2 * x) - Real.exp x :=
    G_dilate_sub hx (by norm_num : (0:ℝ) < 2)
  rw [h3, h2]
  have e2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show (2 * x : ℝ) = x + x from by ring, Real.exp_add]
  have e3 : Real.exp (3 * x) = Real.exp x * Real.exp x * Real.exp x := by
    rw [show (3 * x : ℝ) = x + x + x from by ring, Real.exp_add, Real.exp_add]
  rw [e2, e3]
  have hp : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hexp_ne : Real.exp x ≠ 1 := fun h =>
    hx (Real.exp_injective (h.trans Real.exp_zero.symm))
  have hne' : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr hexp_ne
  have hden : Real.exp x * Real.exp x - Real.exp x ≠ 0 := by
    have : Real.exp x * Real.exp x - Real.exp x = Real.exp x * (Real.exp x - 1) := by ring
    rw [this]
    exact mul_ne_zero hp.ne' hne'
  field_simp
  ring

/-- **F + G = 2·exp**: the two anti-diagonals sum to twice the exponential. -/
theorem F_add_G (x : ℝ) : F x + G x = 2 * Real.exp x := by
  simp [F, G]; ring

/-- **F − G = 2·log**: the two anti-diagonals differ by twice the logarithm. -/
theorem F_sub_G (x : ℝ) : F x - G x = 2 * Real.log x := by
  simp [F, G]; ring

end EML.Identities
