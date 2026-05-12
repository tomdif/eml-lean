/-
  # Translation analog of the anti-diagonal F-mechanism

  The F-mechanism in `Identities.lean` and `IdentitiesFamily.lean` is a
  special case of **cocycle cancellation under a group action**:

    • Dilation `x ↦ k·x` has canonical 1-cocycle `log(k)`.
    • The function `F(x) = exp(x) + log(x)` carries that cocycle additively,
      enabling the cancellation `F(k·x) − F(x) − log(k) = exp(k·x) − exp(x)`.

  Switching to a different group action gives a different cocycle and a
  different "F" — but the **same mechanism** and **the same identity shape**.

  This file applies the mechanism to **translation** `x ↦ x + a`. The
  canonical 1-cocycle of translation (a group homomorphism `(ℝ, +) → ℝ`)
  is the identity `a ↦ a`. The translation analog of F is therefore

      F̃(x) := exp(x) + x.

  ## Main results

  • `F_trans_translate_sub` — `F̃(x + a) − F̃(x) − a = exp(x + a) − exp(x)`
    for all `x, a`. This is the translation analog of `F_dilate_sub`. No
    positivity hypothesis is needed: linear cocycle is unconditional.

  • `exp_eq_F_trans_quotient` — for `a ≠ 0` and any `x`,

      exp(a) = (F̃(x + 2a) − F̃(x) − 2a) / (F̃(x + a) − F̃(x) − a) − 1.

    The "extracted" variable is `a` (the shift), not `x` (the base point).
    In the dilation case, the extracted variable was `x`. This is a
    structural difference: dilation's cocycle is x-independent (`log k`),
    while translation's cocycle is a-linear (`a` itself).

  ## Why this is the right analog

  The F-mechanism works whenever:

    1. A group `G` acts on `ℝ` (here trivially, via the additive structure of ℝ).
    2. There is a non-trivial 1-cocycle `c : G → ℝ` (`log` for dilation, `id`
       for translation).
    3. We package `F = g + c` for some function `g`, then `F(γ·x) − F(x) − c(γ)`
       cancels the cocycle, leaving `g(γ·x) − g(x)`.

  For dilation, `c(k) = log k` and `g = exp` gives the original F-formula.
  For translation, `c(a) = a` and `g = exp` gives this file's formula.
-/
import EML.Identities

open Real

namespace EML.Identities.TranslationCocycle

/-- The translation anti-diagonal: `F̃(x) := exp(x) + x`.

    Compare to `F(x) = exp(x) + log(x)` from `Identities.lean`:
    in both cases F is "exp plus the canonical 1-cocycle of the group action."
    For dilation the cocycle is `log`; for translation it is the identity. -/
noncomputable def F_trans (x : ℝ) : ℝ := exp x + x

/-- **Translation cancellation lemma.** For any `x, a : ℝ`,

      F̃(x + a) − F̃(x) − a = exp(x + a) − exp(x).

    Translation analog of `F_dilate_sub`. Unconditional (no positivity needed). -/
theorem F_trans_translate_sub (x a : ℝ) :
    F_trans (x + a) - F_trans x - a = Real.exp (x + a) - Real.exp x := by
  simp only [F_trans]
  ring

/-- **Main translation identity.** For `a ≠ 0` and any `x : ℝ`,

      exp(a) = (F̃(x + 2a) − F̃(x) − 2a) / (F̃(x + a) − F̃(x) − a) − 1.

    The extracted variable is `a` (the translation amount). Compare to
    `exp_eq_F_quotient`, where the extracted variable is `x` (the base
    point under dilation). -/
theorem exp_eq_F_trans_quotient {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    Real.exp a =
      (F_trans (x + 2 * a) - F_trans x - 2 * a) /
        (F_trans (x + a) - F_trans x - a) - 1 := by
  -- Translate both numerator and denominator to pure-exp differences.
  have hnum : F_trans (x + 2 * a) - F_trans x - 2 * a
                = Real.exp (x + 2 * a) - Real.exp x := by
    have := F_trans_translate_sub x (2 * a)
    linarith
  have hden : F_trans (x + a) - F_trans x - a
                = Real.exp (x + a) - Real.exp x := by
    exact F_trans_translate_sub x a
  rw [hnum, hden]
  -- Goal: exp a = (exp(x + 2a) - exp x)/(exp(x + a) - exp x) - 1
  -- Factor: exp(x+a) = exp x * exp a, exp(x+2a) = exp x * exp a * exp a.
  have e1 : Real.exp (x + 2 * a) = Real.exp x * Real.exp a * Real.exp a := by
    rw [show (x + 2 * a : ℝ) = x + a + a from by ring,
        Real.exp_add, Real.exp_add]
  have e2 : Real.exp (x + a) = Real.exp x * Real.exp a := by
    rw [Real.exp_add]
  rw [e1, e2]
  have hp : 0 < Real.exp x := Real.exp_pos x
  have ha_exp_ne : Real.exp a ≠ 1 := fun h =>
    ha (Real.exp_injective (h.trans Real.exp_zero.symm))
  have ha_sub_ne : Real.exp a - 1 ≠ 0 := sub_ne_zero.mpr ha_exp_ne
  have hden_ne : Real.exp x * Real.exp a - Real.exp x ≠ 0 := by
    have : Real.exp x * Real.exp a - Real.exp x = Real.exp x * (Real.exp a - 1) := by ring
    rw [this]
    exact mul_ne_zero hp.ne' ha_sub_ne
  field_simp
  ring

/-! ## Mechanism comparison

The dilation and translation cases are **the same mechanism applied to
different groups**. Side-by-side:

|                      | Dilation                        | Translation                    |
|----------------------|---------------------------------|--------------------------------|
| Group                | `(ℝ⁺, ·)`                       | `(ℝ, +)`                       |
| Action on `x`        | `x ↦ k · x`                     | `x ↦ x + a`                    |
| Canonical 1-cocycle  | `log : ℝ⁺ → ℝ`                  | `id : ℝ → ℝ`                   |
| Anti-diagonal F      | `F(x) = exp(x) + log(x)`        | `F̃(x) = exp(x) + x`            |
| Cancellation lemma   | `F_dilate_sub`                  | `F_trans_translate_sub`        |
| Main identity        | `exp_eq_F_quotient`             | `exp_eq_F_trans_quotient`      |
| Extracts             | `exp(x)` (the base point)       | `exp(a)` (the shift amount)    |
| Positivity needed    | yes (`x ≠ 0`, `k > 0`)          | no (unconditional)             |

The cleaner translation case (no positivity, simpler cocycle) is suggestive:
**translation may be the "right" base case for this family of identities**,
with dilation a slightly-twisted variant introduced by the multiplicative
group's non-trivial topology.

Generalizing further: any group `G` with `Hom(G, ℝ) ≠ 0` gives an analogous
F-mechanism. The space `Hom(G, ℝ) = H¹(G, ℝ_triv)` is the 1-cohomology with
trivial coefficients; for `G = ℝ⁺` and `G = ℝ` it is 1-dimensional, hence
the unique-cocycle uniqueness we proved in `Characterization.lean`. -/

end EML.Identities.TranslationCocycle
