/-
  # Multi-variable anti-diagonal

  The anti-diagonal mechanism extends straightforwardly to multiple variables.
  The simplest two-variable version:

      F₂(x, y) := exp(x) + exp(y) + log(x) + log(y)
                = F(x) + F(y).

  Under joint dilation `(x, y) ↦ (k·x, k·y)`, the log piece picks up `2·log k`
  (one from each coordinate), and the exp piece picks up its dilation differences:

      F₂(k·x, k·y) − F₂(x, y) − 2·log(k) = (exp(k·x) − exp(x)) + (exp(k·y) − exp(y)).

  More generally, F_n(x₁, …, xₙ) = Σᵢ (exp(xᵢ) + log(xᵢ)) satisfies analogous
  identities with `n·log(k)` and separate exp differences per coordinate.

  Independent dilations `(x, y) ↦ (a·x, b·y)` give the most general form.
-/
import EML.Identities

open Real

namespace EML.Identities.MultiVar

/-- The two-variable anti-diagonal. -/
noncomputable def F₂ (x y : ℝ) : ℝ := exp x + exp y + log x + log y

/-- `F₂(x, y) = F(x) + F(y)`. The multi-variable version is just the sum of
    single-variable F's, since exp and log are both univariate functions. -/
theorem F₂_eq_F_add_F (x y : ℝ) : F₂ x y = F x + F y := by
  simp [F₂, F]; ring

/-- **Joint dilation cancellation.** For `x ≠ 0`, `y ≠ 0`, and `k > 0`,

      F₂(k·x, k·y) − F₂(x, y) − 2·log(k)
        = (exp(k·x) − exp(x)) + (exp(k·y) − exp(y)).

    The `2·log(k)` constant is twice the single-variable constant: one
    coordinate's worth from each. -/
theorem F₂_joint_dilate_sub {x y k : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k) :
    F₂ (k * x) (k * y) - F₂ x y - 2 * log k =
      (exp (k * x) - exp x) + (exp (k * y) - exp y) := by
  rw [F₂_eq_F_add_F, F₂_eq_F_add_F]
  have hxF := F_dilate_sub hx hk
  have hyF := F_dilate_sub hy hk
  linarith

/-- **Independent dilations.** For `x ≠ 0`, `y ≠ 0`, and `a, b > 0`,

      F₂(a·x, b·y) − F₂(x, y) − log(a) − log(b)
        = (exp(a·x) − exp(x)) + (exp(b·y) − exp(y)).

    The two coordinates carry independent log-shifts. -/
theorem F₂_indep_dilate_sub {x y a b : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (ha : 0 < a) (hb : 0 < b) :
    F₂ (a * x) (b * y) - F₂ x y - log a - log b =
      (exp (a * x) - exp x) + (exp (b * y) - exp y) := by
  rw [F₂_eq_F_add_F, F₂_eq_F_add_F]
  have hxF := F_dilate_sub hx ha
  have hyF := F_dilate_sub hy hb
  linarith

/-- **Decoupling under joint dilation.** The two-variable joint-dilation
    difference is exactly the sum of two single-variable dilation differences.
    Multi-variable F is "separable" along the dilation direction. -/
theorem F₂_joint_exp_sum (x y k : ℝ) :
    F₂ (k * x) (k * y) - F₂ x y - 2 * log k
      = (F (k * x) - F x - log k) + (F (k * y) - F y - log k) := by
  rw [F₂_eq_F_add_F, F₂_eq_F_add_F]
  ring

end EML.Identities.MultiVar
