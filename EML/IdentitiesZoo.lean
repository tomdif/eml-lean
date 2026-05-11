/-
  # The anti-diagonal zoo

  The universal mechanism behind every identity in `Identities.lean` and
  `IdentitiesFamily.lean`: for **any** function `g`, the function

      F_g(x) := g(x) + log(x)

  satisfies the dilation-difference cancellation

      F_g(k·x) − F_g(x) − log(k) = g(k·x) − g(x).

  This is purely about log being the unique solution to `h(kx) − h(x) = c(k)`.
  Specializations below give cleanly cancelling identities for `sin`, `cos`,
  `sinh`, `cosh` — and by the same template, for any other `g`.
-/
import EML.Identities

open Real

namespace EML.Identities.Zoo

/-- **Universal anti-diagonal lemma.** For any function `g`, the function
    `F_g(x) := g(x) + log(x)` satisfies

      F_g(k·x) − F_g(x) − log(k) = g(k·x) − g(x)

    for `x ≠ 0` and `k > 0`. The log piece cancels purely from
    `log(k·x) = log k + log x`; the choice of `g` is irrelevant. -/
theorem anti_diag_dilate_sub (g : ℝ → ℝ) {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    (g (k * x) + log (k * x)) - (g x + log x) - log k = g (k * x) - g x := by
  rw [Real.log_mul hk.ne' hx]
  ring

/-! ## Sine anti-diagonal -/

/-- `F_sin(x) := sin(x) + log(x)`. -/
noncomputable def F_sin (x : ℝ) : ℝ := sin x + log x

theorem F_sin_dilate_sub {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F_sin (k * x) - F_sin x - log k = sin (k * x) - sin x :=
  anti_diag_dilate_sub sin hx hk

/-! ## Cosine anti-diagonal -/

/-- `F_cos(x) := cos(x) + log(x)`. -/
noncomputable def F_cos (x : ℝ) : ℝ := cos x + log x

theorem F_cos_dilate_sub {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F_cos (k * x) - F_cos x - log k = cos (k * x) - cos x :=
  anti_diag_dilate_sub cos hx hk

/-! ## Hyperbolic-sine anti-diagonal -/

/-- `F_sinh(x) := sinh(x) + log(x)`. -/
noncomputable def F_sinh (x : ℝ) : ℝ := sinh x + log x

theorem F_sinh_dilate_sub {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F_sinh (k * x) - F_sinh x - log k = sinh (k * x) - sinh x :=
  anti_diag_dilate_sub sinh hx hk

/-! ## Hyperbolic-cosine anti-diagonal -/

/-- `F_cosh(x) := cosh(x) + log(x)`. -/
noncomputable def F_cosh (x : ℝ) : ℝ := cosh x + log x

theorem F_cosh_dilate_sub {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F_cosh (k * x) - F_cosh x - log k = cosh (k * x) - cosh x :=
  anti_diag_dilate_sub cosh hx hk

/-! ## Identity anti-diagonal: F_id(x) = x + log(x)

    The simplest non-trivial g: just g(x) = x. Then F_id(kx) − F_id(x) − log k = (k−1)x. -/

noncomputable def F_id (x : ℝ) : ℝ := x + log x

theorem F_id_dilate_sub {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F_id (k * x) - F_id x - log k = (k - 1) * x := by
  have := anti_diag_dilate_sub id hx hk
  simp only [F_id, id] at *
  linarith

end EML.Identities.Zoo
