/-
  # The general cocycle-cancellation mechanism

  This file abstracts the common structure between:

    • `F_dilate_sub`        (dilation:    `F(k·x) − F(x) − log k = exp(k·x) − exp(x)`)
    • `F_trans_translate_sub` (translation: `F̃(x+a) − F̃(x) − a    = exp(x+a) − exp(x)`)

  Both are instances of a **single algebraic mechanism**, depending only on:

    1. A transformation `T : ℝ → ℝ` of the input (here `T(x) = k·x` or `T(x) = x+a`).
    2. A "carrier" function `c̃ : ℝ → ℝ` whose difference along `T` is constant:
       `c̃(T x) − c̃(x) = c` for some constant `c` (the "cocycle value at `T`").
    3. An arbitrary "target" function `g : ℝ → ℝ`.

  Then `F := g + c̃` satisfies the **universal cancellation**

      F(T x) − F x − c = g(T x) − g x.

  The constant `c` is the value of the 1-cocycle at the group element corresponding
  to the transformation `T`:
    • dilation by `k`: c = log k     (so c̃ = log)
    • translation by `a`: c = a       (so c̃ = id)

  ## Significance

  The dilation- and translation-case theorems are SPECIAL CASES of `cocycle_cancellation`
  below. The mechanism extends mechanically to:
    • complex rotation z ↦ e^{iθ}·z (with c̃ = arg, c = θ),
    • modular transformations on the upper half plane,
    • any other group action with a continuous 1-cocycle into ℝ.

  Together with `Characterization.lean` (which proves the carrier `c̃` is unique up to
  constant), this gives a clean, formal statement of the F-mechanism's universality.
-/
import EML.Identities
import EML.TranslationCocycle

open Real

namespace EML.Identities.CocycleMechanism

/-- **The general cocycle-cancellation mechanism.**

    For any transformation `T : ℝ → ℝ`, any "target" function `g`, and any
    "carrier" function `c̃` whose `T`-difference is the constant `c`,

        F(T x) − F x − c = g(T x) − g x,

    where `F := g + c̃`. Trivial algebraic content, but it identifies the
    mechanism behind every dilation/translation F-identity in this repo. -/
theorem cocycle_cancellation
    (T : ℝ → ℝ) (c : ℝ) (ctilde : ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ)
    (h_ctilde : ctilde (T x) - ctilde x = c) :
    (g (T x) + ctilde (T x)) - (g x + ctilde x) - c
      = g (T x) - g x := by
  linarith

/-! ## Dilation as a special case

    Recovers `F_dilate_sub` from `Identities.lean` via `T = (k · ·)`,
    `c = log k`, `c̃ = log`, `g = exp`. -/

theorem dilate_specialization {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F (k * x) - F x - log k = exp (k * x) - exp x := by
  -- Apply cocycle_cancellation with T(y) := k*y, c̃ = log, c = log k, g = exp.
  have h_ctilde : Real.log (k * x) - Real.log x = Real.log k := by
    rw [Real.log_mul hk.ne' hx]; ring
  have key := cocycle_cancellation (T := fun y => k * y) (c := Real.log k)
                (ctilde := Real.log) (g := Real.exp) x h_ctilde
  simpa [F] using key

/-! ## Translation as a special case

    Recovers `F_trans_translate_sub` from `TranslationCocycle.lean` via
    `T = (· + a)`, `c = a`, `c̃ = id`, `g = exp`. -/

theorem translate_specialization (x a : ℝ) :
    TranslationCocycle.F_trans (x + a) - TranslationCocycle.F_trans x - a
      = exp (x + a) - exp x := by
  -- Apply cocycle_cancellation with T(y) := y + a, c̃ = id, c = a, g = exp.
  have h_ctilde : (x + a : ℝ) - x = a := by ring
  have key := cocycle_cancellation (T := fun y => y + a) (c := a)
                (ctilde := id) (g := Real.exp) x h_ctilde
  simpa [TranslationCocycle.F_trans] using key

end EML.Identities.CocycleMechanism
