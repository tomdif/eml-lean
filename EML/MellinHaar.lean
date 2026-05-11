/-
  # F, the multiplicative Haar measure, and the Mellin transform

  This file proves the differential characterization of the anti-diagonal
  function F:

      F'(x) = exp(x) + 1/x.

  The two summands have distinct group-theoretic meanings on (0, ∞):

    • `exp(x)` is the **density of the F-tangent** at x — what gets extracted
      by the dilation-difference identities.

    • `1/x` is the **density of the multiplicative Haar measure** `dx/x` on
      the group `(ℝ⁺, ·)`. It is the unique (up to scaling) translation-invariant
      density on this group.

  Integrating: `F(x) = exp(x) + log(x) + C` is the unique antiderivative whose
  derivative decomposes into (i) an exponential and (ii) the Haar density.

  ## Bridge to Mellin / Tate

  The Mellin transform is the L²-Fourier transform of the multiplicative group
  `(ℝ⁺, ·)`:

      M[f](s) = ∫₀^∞ f(x) · x^s · dx/x.

  It diagonalizes the dilation operator `D_k f(x) = f(k·x)` to multiplication
  by `k^{-s}`. The dilation-difference identities in `Identities.lean` are the
  arithmetic shadow of this diagonalization: subtracting `f` from its dilate
  is precisely what becomes `(k^{-s} − 1) · M[f](s)` on the spectral side.

  The `log k` constants that thread through every identity in this repo are
  the **infinitesimals of the multiplicative Haar measure**: `log k = ∫₁^k dx/x`.

  This is the same circle of ideas that appears in Tate's thesis and in the
  Connes-Consani-Moscovici 2025 spectral-triple approach to RH — there the
  Mellin transform is replaced by an idelic integral, and the dilation
  operator's spectrum encodes the zeros of ξ.
-/
import EML.Identities
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Real

namespace EML.Identities.MellinHaar

/-- **Differential characterization of F.** For `x ≠ 0`,

      F'(x) = exp(x) + x⁻¹.

    The `x⁻¹` summand is the density of the multiplicative Haar measure
    `dx/x` on `(ℝ⁺, ·)`; the `exp(x)` summand is the F-tangent that survives
    the dilation-difference cancellation. -/
theorem hasDerivAt_F {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt F (Real.exp x + x⁻¹) x := by
  unfold F
  exact (Real.hasDerivAt_exp x).add (Real.hasDerivAt_log hx)

/-- F is differentiable away from 0. -/
theorem differentiableAt_F {x : ℝ} (hx : x ≠ 0) : DifferentiableAt ℝ F x :=
  (hasDerivAt_F hx).differentiableAt

/-- The classical derivative function: `deriv F x = exp(x) + x⁻¹` for `x ≠ 0`. -/
theorem deriv_F {x : ℝ} (hx : x ≠ 0) : deriv F x = Real.exp x + x⁻¹ :=
  (hasDerivAt_F hx).deriv

/-- **F is characterized by an inhomogeneous Euler equation.** Multiplying
    `F'(x) = exp(x) + 1/x` through by `x`:

        x · F'(x) − 1 = x · exp(x).

    The `−1` on the left is the contribution of the multiplicative-Haar
    summand to the Euler operator `x · d/dx`. -/
theorem F_euler_eq {x : ℝ} (hx : x ≠ 0) :
    x * deriv F x - 1 = x * Real.exp x := by
  rw [deriv_F hx]
  field_simp
  ring

/-! ## Second derivative

    F''(x) = exp(x) − 1/x². The exp piece is unchanged (eigenfunction of d/dx);
    the Haar piece becomes its own derivative (−1/x²), which is the second-order
    Haar contribution. -/

/-- F''(x) = exp(x) − 1/x². -/
theorem hasDerivAt_F_deriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => Real.exp y + y⁻¹) (Real.exp x - (x ^ 2)⁻¹) x := by
  have h_inv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx
  have h_sum := (Real.hasDerivAt_exp x).add h_inv
  -- h_sum derivative is `exp x + -(x ^ 2)⁻¹`, which equals `exp x - (x ^ 2)⁻¹`.
  simpa using h_sum

end EML.Identities.MellinHaar
