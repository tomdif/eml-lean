/-
  # S-cocycle of the modular F-function

  Companion to `EML/ModularCocycle.lean`. Whereas the T-cocycle uses the
  simple "translation" carrier `c̃(τ) = τ`, here we use the carrier
  `c̃(τ) = Complex.log τ` to get a clean cocycle identity for the
  inversion `S : τ ↦ −1/τ` (Mathlib's `ModularGroup.S`).

  ## Goal

  Define the modular F-function with logarithmic carrier:

      F_mod_S g τ := g τ + Complex.log τ.

  Then for any `τ : ℍ`, `S • τ = mk (-(τ : ℂ)⁻¹) _`, so the coercion
  `((S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ = -1/τ`. The cocycle value is the
  τ-dependent quantity

      c_S(τ) := Complex.log (-(τ : ℂ)⁻¹) − Complex.log τ,

  and we prove the universal cancellation

      F_mod_S g (S • τ) − F_mod_S g τ − c_S(τ) = g (S • τ) − g τ.

  Unlike the T-cocycle (constant value `1`), `c_S(τ)` is **not** constant
  in `τ` — it depends on the principal branch of `log`. This file then
  proves a clean closed form valid throughout `ℍ`:

      c_S(τ) = π·I − 2 · log τ,

  using `Complex.log_inv` and `Complex.arg_neg_eq_arg_sub_pi_of_im_pos`.
  This is the modular analog of the dilation/translation cocycle, with
  the S-generator playing the role of the parabolic generator in
  `EML/ModularCocycle.lean`.

  ## What this file does NOT do

  • It does not analyze the **full** SL(2, ℤ) cocycle, only the value
    on the inversion generator `S`. Combining with the T-cocycle in
    `EML/ModularCocycle.lean` plus the relations `S² = -1`, `(ST)³ = -1`
    would yield the cocycle on all of SL(2, ℤ), but this requires
    additional group-theoretic infrastructure (and does not change the
    carrier — only the bookkeeping).

  • It does not address Eichler-Shimura period polynomials or the
    Dedekind eta multiplier. Those require higher-weight carriers and
    integration; see the outlook in `EML/ModularCocycle.lean`.
-/
import EML.Identities
import EML.CocycleMechanism
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open UpperHalfPlane ModularGroup Complex
open scoped Real

namespace EML.Identities.SCocycle

/-- The modular F-function with logarithmic carrier:
    `F_mod_S g τ := g τ + Complex.log τ`, where `Complex.log` is the
    principal branch (imaginary part in `(-π, π]`).

    The carrier `Complex.log` produces a non-trivial S-cocycle (the
    inversion `τ ↦ −1/τ`), in contrast to the linear carrier `τ` in
    `EML/ModularCocycle.lean` which gives a constant T-cocycle. -/
noncomputable def F_mod_S (g : ℍ → ℂ) (τ : ℍ) : ℂ := g τ + Complex.log (τ : ℂ)

/-- The S-cocycle value at `τ` is **τ-dependent**:
    `c_S(τ) := log(−1/τ) − log τ`.

    This is the value of the canonical 1-cocycle for the inversion
    generator `S`. Unlike the constant T-cocycle (value `1`), `c_S(τ)`
    varies with `τ`; the closed form `π·I − 2 · log τ` is proved
    in `c_S_eq` below. -/
noncomputable def c_S (τ : ℍ) : ℂ :=
  Complex.log ((ModularGroup.S • τ : ℍ) : ℂ) - Complex.log (τ : ℂ)

/-- **S-cocycle of `F_mod_S`.** For any `g : ℍ → ℂ` and any `τ : ℍ`,

      F_mod_S g (S • τ) − F_mod_S g τ − c_S(τ) = g (S • τ) − g τ.

    Algebraic specialization of the general `cocycle_cancellation`
    mechanism (in `CocycleMechanism.lean`) to the inversion
    `S : ℍ → ℍ` with carrier `c̃(τ) = log τ` and cocycle value
    `c = c_S(τ)`. The non-triviality is that `c_S(τ)` is τ-dependent;
    its closed form is given by `c_S_eq`. -/
theorem F_mod_S_S_cocycle (g : ℍ → ℂ) (τ : ℍ) :
    F_mod_S g (ModularGroup.S • τ) - F_mod_S g τ - c_S τ
      = g (ModularGroup.S • τ) - g τ := by
  simp only [F_mod_S, c_S]
  ring

/-- The coerced image of `S • τ` in `ℂ` is `(−τ)⁻¹`.

    Direct consequence of `modular_S_smul` plus the `coe_mk`
    computation rule for `UpperHalfPlane.mk`. -/
theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := by
  rw [modular_S_smul]

/-- **Closed form for the S-cocycle value.**

    For `τ : ℍ` (so `0 < (τ : ℂ).im`), the τ-dependent cocycle value
    `c_S(τ) = log(−1/τ) − log τ` simplifies via the principal branch
    of `Complex.log` to

        c_S(τ) = π · I − 2 · log τ.

    Mechanism:
      • `−τ` has negative imaginary part, so `arg(−τ) ≠ π` (in fact
        `arg(−τ) < 0`).
      • Hence `log((−τ)⁻¹) = −log(−τ)` by `Complex.log_inv`.
      • And `log(−τ) = log τ − π·I`, using
        `arg_neg_eq_arg_sub_pi_of_im_pos` and `norm_neg`.
      • Combine: `c_S(τ) = (π·I − log τ) − log τ = π·I − 2 · log τ`. -/
theorem c_S_eq (τ : ℍ) :
    c_S τ = π * Complex.I - 2 * Complex.log (τ : ℂ) := by
  -- Positive imaginary part: this is the defining property of `ℍ`.
  have hz_im : 0 < (τ : ℂ).im := τ.coe_im_pos
  -- Step 1: rewrite the S-action coercion as `(-τ)⁻¹`.
  have hcoe : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := coe_S_smul τ
  -- Step 2: `(-τ).im < 0`, so `arg(-τ) ≠ π`.
  have hneg_im : (-(τ : ℂ)).im < 0 := by
    rw [neg_im]; linarith
  have harg_ne : (-(τ : ℂ)).arg ≠ π := by
    intro h
    rw [arg_eq_pi_iff] at h
    exact (lt_irrefl _ (h.2 ▸ hneg_im))
  -- Step 3: `log((-τ)⁻¹) = -log(-τ)`.
  have h_log_inv : Complex.log ((-(τ : ℂ))⁻¹) = -Complex.log (-(τ : ℂ)) :=
    Complex.log_inv (-(τ : ℂ)) harg_ne
  -- Step 4: `log(-τ) = log τ - π·I`.
  -- Use `log_re`/`log_im` plus `norm_neg`/`arg_neg_eq_arg_sub_pi_of_im_pos`.
  have h_log_neg :
      Complex.log (-(τ : ℂ)) = Complex.log (τ : ℂ) - π * Complex.I := by
    apply Complex.ext
    · -- Real parts: `Real.log ‖-τ‖ = Real.log ‖τ‖`.
      simp [Complex.log_re]
    · -- Imaginary parts: `arg(-τ) = arg τ - π`.
      have harg : (-(τ : ℂ)).arg = (τ : ℂ).arg - π :=
        Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz_im
      simp [Complex.log_im, harg]
  -- Step 5: assemble `log((-τ)⁻¹) = π·I - log τ`.
  have h_log_S :
      Complex.log ((-(τ : ℂ))⁻¹) = π * Complex.I - Complex.log (τ : ℂ) := by
    rw [h_log_inv, h_log_neg]
    ring
  -- Finally compute `c_S τ`.
  simp only [c_S]
  rw [hcoe, h_log_S]
  ring

/-- **Combined form.** Inlining `c_S_eq` into `F_mod_S_S_cocycle` gives
    the cocycle identity directly in closed form:

      F_mod_S g (S • τ) − F_mod_S g τ − (π·I − 2 · log τ) = g (S • τ) − g τ.

    This is the modular S-analog of the dilation/translation
    cocycle identities (see `CocycleMechanism.cocycle_cancellation`). -/
theorem F_mod_S_S_cocycle_explicit (g : ℍ → ℂ) (τ : ℍ) :
    F_mod_S g (ModularGroup.S • τ) - F_mod_S g τ
        - (π * Complex.I - 2 * Complex.log (τ : ℂ))
      = g (ModularGroup.S • τ) - g τ := by
  have h := F_mod_S_S_cocycle g τ
  rw [c_S_eq] at h
  exact h

/-- **Specialization for S-invariant `g`** (e.g., a weight-0 modular
    form). When `g(S·τ) = g τ`, the residual vanishes and we obtain
    the clean identity

      F_mod_S g (S · τ) − F_mod_S g τ = π · I − 2 · log τ.

    Modular analog of `F_mod_T_invariant_g` in `EML/ModularCocycle.lean`. -/
theorem F_mod_S_S_invariant_g
    (g : ℍ → ℂ) (h_g_inv : ∀ τ : ℍ, g (ModularGroup.S • τ) = g τ) (τ : ℍ) :
    F_mod_S g (ModularGroup.S • τ) - F_mod_S g τ
      = π * Complex.I - 2 * Complex.log (τ : ℂ) := by
  have hcoc := F_mod_S_S_cocycle_explicit g τ
  rw [h_g_inv, sub_self] at hcoc
  linear_combination hcoc

/-! ## Outlook

The two cocycles `F_mod_T_cocycle` (in `EML/ModularCocycle.lean`) and
`F_mod_S_S_cocycle` (this file) together encode the cocycle structure
on the two generators of SL(2, ℤ). Combining them via the relations
`S² = -1` and `(ST)³ = -1` (modulo the center `{±1}`) would give a
1-cocycle on all of PSL(2, ℤ). That assembly is bookkeeping; the
substantive content is the carrier choice (here `Complex.log`), which
trades the constant T-value `1` for the τ-dependent S-value
`π · I − 2 · log τ`.

The next step toward Eichler-Shimura theory is to replace `Complex.log`
with **higher-weight carriers** (period integrals of weight-k modular
forms). Those carriers produce period polynomials rather than constants,
and the corresponding cocycle lands in a `(k − 2)`-dimensional
polynomial representation of SL(2, ℤ) rather than in `ℂ` itself.
That generalization, plus connections to L-functions, is the
classical setting of period polynomials and Hecke operators — and
remains future work. -/

end EML.Identities.SCocycle
