/-
  # Characterization theorems: the converse universal mechanism

  The universal mechanism (in `IdentitiesZoo`) showed that **any** `F = g + α·log`
  has the dilation cancellation `F(k·x) − F(x) − α·log(k) = g(k·x) − g(x)`.

  This file proves the **converse**: that property *forces* F to have this form.
  So `F = g + α·log + const` is not just *a* solution but is *the unique*
  family of solutions to the dilation-cocycle equation.

  ## Main results

  • `pure_log_characterization` — if `h(k·x) − h(x) = α·log(k)` for all
    positive x, k, then `h(x) = α·log(x) + h(1)`. So log (up to scalar and
    constant) is the **unique** solution to the pure-log cocycle.

  • `dilation_decomposition` — if `F(k·x) − F(x) − α·log(k) = g(k·x) − g(x)`
    for all positive x, k, then `F(x) = g(x) + α·log(x) + (F(1) − g(1))`.
    The dilation-cocycle structure determines F up to additive constant.

  • `F_unique_up_to_constant` — specialization: any G satisfying the
    anti-diagonal cancellation `G(kx) − G(x) − log(k) = exp(kx) − exp(x)`
    equals the canonical `F = exp + log` up to a constant.

  ## Why this matters

  The "Mellin/Haar" observation from `MellinHaar.lean` says: F'(x) = g(x) + 1/x,
  and the 1/x is the multiplicative Haar density. This file proves the
  matching uniqueness: given the dilation-difference equation, F is uniquely
  determined up to constant. So the anti-diagonal F is the **canonical**
  function with both an exp-tangent and the Haar-density tangent.
-/
import EML.Identities

open Real

namespace EML.Identities.Characterization

/-- **Pure-log characterization.** If `h: ℝ → ℝ` satisfies
    `h(k·x) − h(x) = α·log(k)` for all positive x, k, then
    `h(x) = α·log(x) + h(1)` on `(0, ∞)`.

    Proof: specialize `k := x⁻¹`. Then `h(1) − h(x) = α·log(x⁻¹) = −α·log(x)`,
    giving `h(x) = α·log(x) + h(1)`. This is a one-line consequence of
    `log(1/x) = −log(x)`. -/
theorem pure_log_characterization {h : ℝ → ℝ} {α : ℝ}
    (hh : ∀ x k : ℝ, 0 < x → 0 < k → h (k * x) - h x = α * Real.log k)
    {x : ℝ} (hx : 0 < x) :
    h x = α * Real.log x + h 1 := by
  have hxinv : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
  have key := hh x x⁻¹ hx hxinv
  rw [inv_mul_cancel₀ hx.ne', Real.log_inv] at key
  linarith

/-- **Dilation decomposition (converse universal mechanism).** If F satisfies
    `F(k·x) − F(x) − α·log(k) = g(k·x) − g(x)` for all positive x, k, then
    `F(x) = g(x) + α·log(x) + (F(1) − g(1))`.

    So the dilation-difference equation determines F up to additive constant
    of the form `(F(1) − g(1))`. -/
theorem dilation_decomposition (F g : ℝ → ℝ) {α : ℝ}
    (h : ∀ x k : ℝ, 0 < x → 0 < k →
          F (k * x) - F x - α * Real.log k = g (k * x) - g x)
    {x : ℝ} (hx : 0 < x) :
    F x = g x + α * Real.log x + (F 1 - g 1) := by
  -- The function `F − g` satisfies the pure-log cocycle.
  have hkey : ∀ y k : ℝ, 0 < y → 0 < k →
              (F (k * y) - g (k * y)) - (F y - g y) = α * Real.log k := by
    intro y k hy hk
    have := h y k hy hk
    linarith
  have := pure_log_characterization
            (h := fun z => F z - g z) hkey hx
  linarith

/-- **Pure-linear characterization (translation analog).** If `h : ℝ → ℝ`
    satisfies `h(x + a) − h(x) = α·a` for all `x, a : ℝ`, then
    `h(x) = α·x + h(0)`.

    Same trick as `pure_log_characterization`, in the translation group.
    Specialize `a := −x`: `h(0) − h(x) = α·(−x) = −α·x`, so `h(x) = α·x + h(0)`.
    No regularity required — the strong hypothesis (RHS specified explicitly
    as `α·a`) makes Cauchy pathologies impossible. -/
theorem pure_linear_characterization {h : ℝ → ℝ} {α : ℝ}
    (hh : ∀ x a : ℝ, h (x + a) - h x = α * a) (x : ℝ) :
    h x = α * x + h 0 := by
  have key := hh x (-x)
  simp at key
  linarith

/-! ## Abstract carrier-uniqueness theorem

The dilation case (`pure_log_characterization`) and the translation case
(`pure_linear_characterization`) are both instances of a single abstract
theorem about cocycle carriers. Whenever a group action on `X` has a
"witness" function reducing every point to a fixed reference, any carrier
of a cocycle is determined explicitly by its value at the reference.

This is the underlying meta-principle of the F-mechanism's uniqueness side.
-/

/-- **Carrier-uniqueness, abstract form.** Let `act : G → X → X` be an action,
    `c : G → ℝ` a cocycle (specifying the carrier-difference at each `g`),
    and `w : X → G` a witness that reduces every `x` to a reference `x₀`.
    Then any carrier `f : X → ℝ` of `c` is determined by

        f(x) = f(x₀) − c(w(x)).

    No structure on `G`, `X`, `act` is required — the proof is one line
    of algebra after the witness is applied. -/
theorem cocycle_carrier_explicit
    {G X : Type*} (act : G → X → X) (c : G → ℝ) (f : X → ℝ)
    (hf : ∀ s x, f (act s x) - f x = c s)
    (x₀ : X) (w : X → G) (h_wit : ∀ x, act (w x) x = x₀)
    (x : X) :
    f x = f x₀ - c (w x) := by
  have h := hf (w x) x
  rw [h_wit] at h
  linarith

/-- **Carrier-uniqueness (difference form).** Two carriers of the same
    cocycle differ by a constant. -/
theorem cocycle_carrier_diff_const
    {G X : Type*} (act : G → X → X) {c : G → ℝ}
    {f g : X → ℝ}
    (hf : ∀ s x, f (act s x) - f x = c s)
    (hg : ∀ s x, g (act s x) - g x = c s)
    (x₀ : X) (w : X → G) (h_wit : ∀ x, act (w x) x = x₀)
    (x : X) :
    f x - g x = f x₀ - g x₀ := by
  rw [cocycle_carrier_explicit act c f hf x₀ w h_wit x,
      cocycle_carrier_explicit act c g hg x₀ w h_wit x]
  ring

/-- **F is unique up to additive constant.** The canonical anti-diagonal
    `F = exp + log` is the unique function (up to additive constant)
    satisfying `G(k·x) − G(x) − log(k) = exp(k·x) − exp(x)` for all positive
    x, k.

    Combined with `F_dilate_sub` (the existence direction), this gives a
    complete characterization of F by its dilation-difference behavior. -/
theorem F_unique_up_to_constant (G : ℝ → ℝ)
    (h : ∀ x k : ℝ, 0 < x → 0 < k →
         G (k * x) - G x - Real.log k = Real.exp (k * x) - Real.exp x)
    {x : ℝ} (hx : 0 < x) :
    G x = F x + (G 1 - F 1) := by
  -- Decompose G via dilation_decomposition with g = exp and α = 1.
  have h1 : ∀ y k : ℝ, 0 < y → 0 < k →
            G (k * y) - G y - (1 : ℝ) * Real.log k = Real.exp (k * y) - Real.exp y := by
    intro y k hy hk
    have := h y k hy hk
    linarith
  have hG := dilation_decomposition G Real.exp h1 hx
  -- hG : G x = exp x + 1 * log x + (G 1 - exp 1)
  -- F x = exp x + log x by def, so F x = exp x + log x.
  have hF : F x = Real.exp x + Real.log x := rfl
  have hF1 : F 1 = Real.exp 1 + Real.log 1 := rfl
  rw [Real.log_one] at hF1
  linarith

end EML.Identities.Characterization
