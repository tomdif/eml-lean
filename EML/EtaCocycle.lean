/-
  # T- and S-cocycles of `log η` (Dedekind eta function)

  Goal: extend the modular F-mechanism from `ModularCocycle.lean` to the
  Dedekind eta function. Where `ModularCocycle.lean` realised the carrier
  `c̃(τ) = τ` of the T-cocycle, this file realises the carrier
  `c̃(τ) = Complex.log (η τ)` and gives both the T- and S-cocycles.

  ## What this file delivers

  Let `η : ℂ → ℂ` be Mathlib's Dedekind eta function
  (`ModularForm.eta`, defined in
  `Mathlib/NumberTheory/ModularForms/DedekindEta.lean`).

  ### Multiplicative transformation laws (unconditional)

  * `eta_T_smul`        : `η (T • τ) = exp (π·I/12) · η τ`.
  * `eta_S_smul`        : `η (S • τ) = (√I)⁻¹ · √(τ : ℂ) · η τ`.

  Both are derived from the q-expansion of `η` and from Mathlib's
  `ModularForm.eta_comp_eq_csqrt_I_inv` respectively.

  ### Additive (log) cocycles

  Define the modular eta F-function

      F_mod_eta g τ := g τ + Complex.log (η τ).

  Then we prove

  * `F_mod_eta_T_cocycle`     : the T-cocycle with constant value `π·I/12`,
                                under a one-line branch-compatibility
                                hypothesis on `arg (η τ)`.
  * `F_mod_eta_S_cocycle`     : the S-cocycle with τ-dependent value
                                `log ((√I)⁻¹ · √τ)`, under the analogous
                                branch-compatibility hypothesis.
  * `S_cocycle_carrier_eq_half_log_neg_I_mul` : the S-carrier matches the
                                standard form `(1/2) · log(-I·τ)` on the
                                principal branch.
  * `F_mod_eta_T_invariant_g`  : corollary for T-invariant `g`.

  ## Branch-of-log discipline

  The principal branch `Complex.log` satisfies `log(a·b) = log a + log b`
  only when `arg a + arg b ∈ Ioc(-π, π]`
  (Mathlib's `Complex.log_mul_eq_add_log_iff`). The multiplicative laws
  above are exact algebraic identities in `ℂ`, but the corresponding
  additive identities for `log η` hold only with respect to the principal
  branch under a side condition. We make this side condition explicit
  rather than hide it inside a custom log-of-eta function: this matches
  the discussion at the end of `ModularCocycle.lean` (the S-cocycle
  "depends on a branch of log").

  In the canonical fundamental domain `τ ∈ 𝒟` one expects
  `arg (η τ) ≈ π · τ.re / 12` (small for `|τ.re| ≤ 1/2`), so the
  branch-compatibility hypothesis is satisfied with room to spare. We do
  not prove this estimate here; we only register the cocycle structure
  and isolate the analytic side conditions.

  ## Style

  Matches `EML/ModularCocycle.lean`: same open scope (with `UpperHalfPlane`
  opened hiding `I` to avoid the conflict with `Complex.I`, as in
  `Mathlib/NumberTheory/ModularForms/DedekindEta.lean`), same namespace
  pattern (`EML.Identities.<Sub>`), same documentation rhythm.
-/
import EML.ModularCocycle
import Mathlib.NumberTheory.ModularForms.Delta

open Complex ModularGroup ModularForm Function
open UpperHalfPlane hiding I
open scoped Real

namespace EML.Identities.EtaCocycle

/-! ## Section 1. Multiplicative transformation laws of `η`

These are exact identities in `ℂ` (no branch issues). They are the
content that makes the additive cocycles in Section 3 work. -/

/-- **T-transformation of the q-parameter** at scale 24:
`Periodic.qParam 24 (z + 1) = exp(π·I/12) · Periodic.qParam 24 z`. The factor
`exp(π·I/12) = exp(2π·I / 24)` is the multiplier of `η` under the
parabolic generator `T`. -/
lemma qParam_24_add_one (z : ℂ) :
    Periodic.qParam 24 (z + 1) = Complex.exp (π * I / 12) * Periodic.qParam 24 z := by
  unfold Periodic.qParam
  rw [show (2 * π * I * (z + 1) / ((24 : ℝ) : ℂ) : ℂ)
        = (π * I / 12) + (2 * π * I * z / ((24 : ℝ) : ℂ)) by
        push_cast; ring,
      Complex.exp_add]

/-- **T-invariance of each q-power factor**: `eta_q n (z + 1) = eta_q n z`.
Each `eta_q n z = exp(2π·I·(n+1)·z)` is `1`-periodic because
`exp(2π·I·(n+1)) = 1`. -/
lemma eta_q_add_one (n : ℕ) (z : ℂ) :
    ModularForm.eta_q n (z + 1) = ModularForm.eta_q n z := by
  rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp]
  rw [show (2 * π * I * (n + 1) * (z + 1) : ℂ)
        = (2 * π * I * (n + 1) * z) + ((n + 1 : ℕ) : ℂ) * (2 * π * I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I (n + 1), mul_one]

/-- The infinite product factor of `η` is T-invariant. -/
lemma tprod_one_sub_eta_q_add_one (z : ℂ) :
    ∏' n, (1 - ModularForm.eta_q n (z + 1)) = ∏' n, (1 - ModularForm.eta_q n z) := by
  refine tprod_congr (fun n => ?_)
  rw [eta_q_add_one]

/-- **Multiplicative T-transformation of `η` (raw, on `ℂ`)**:
`η (z + 1) = exp(π·I/12) · η z`. -/
lemma eta_add_one (z : ℂ) :
    ModularForm.eta (z + 1) = Complex.exp (π * I / 12) * ModularForm.eta z := by
  unfold ModularForm.eta
  rw [qParam_24_add_one, tprod_one_sub_eta_q_add_one]
  ring

/-- **Multiplicative T-transformation of `η` on `ℍ`**:
`η (T • τ) = exp(π·I/12) · η τ`. -/
theorem eta_T_smul (τ : ℍ) :
    ModularForm.eta ((ModularGroup.T • τ : ℍ) : ℂ)
      = Complex.exp (π * I / 12) * ModularForm.eta (τ : ℂ) := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    simpa using ModularGroup.coe_T_zpow_smul_eq (z := τ) (n := 1)
  rw [hT, eta_add_one]

/-- **Multiplicative S-transformation of `η` on `ℍ`**, repackaged from
Mathlib's `ModularForm.eta_comp_eq_csqrt_I_inv`:

  `η (S • τ) = (√I)⁻¹ · √(τ : ℂ) · η τ`.

This is the standard Dedekind multiplier formula `η(-1/τ) = √(-iτ)·η(τ)`
in the disambiguated form (matching Mathlib's convention; the
equivalence to the `√(-iτ)` form on the principal branch is recorded in
`S_cocycle_carrier_eq_half_log_neg_I_mul`). -/
theorem eta_S_smul (τ : ℍ) :
    ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ)
      = (Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) * ModularForm.eta (τ : ℂ) := by
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
    simp
  rw [hS]
  have hτ : (τ : ℂ) ∈ upperHalfPlaneSet := τ.2
  have h := ModularForm.eta_comp_eq_csqrt_I_inv (x := (τ : ℂ)) hτ
  -- `eta_comp_eq_csqrt_I_inv` states `(η ∘ (-1 / ·)) x = ((sqrt I)⁻¹ • (sqrt * η)) x`.
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  -- `h : η (-1 / τ) = (sqrt I)⁻¹ * (sqrt τ * η τ)`
  have hrw : (-((τ : ℂ))⁻¹ : ℂ) = -1 / (τ : ℂ) := by rw [neg_div, one_div]
  rw [hrw, h]
  ring

/-! ## Section 2. The modular eta F-function

The eta F-function carries `Complex.log (η τ)` as its modular cocycle
generator, just as `F_mod` of `ModularCocycle.lean` carried the
identity `τ`. The two should be regarded as parallel: one is the
"linear" cocycle (translation), the other the "logarithmic" cocycle
(scaling by the eta multiplier system). -/

/-- The eta F-function: `F_mod_eta g τ := g τ + Complex.log (η τ)`. -/
noncomputable def F_mod_eta (g : ℍ → ℂ) (τ : ℍ) : ℂ :=
  g τ + Complex.log (ModularForm.eta (τ : ℂ))

/-! ## Section 3. Additive (log) cocycle identities

`Complex.log` is the principal branch. For the multiplicative law
`η(T•τ) = exp(π·I/12) · η τ` to upgrade to the additive log law
`log η(T•τ) − log η τ = π·I/12` one needs the branch-compatibility
condition `arg(exp(π·I/12)) + arg(η τ) ∈ Ioc(-π, π]`, equivalently
`π/12 + arg(η τ) ∈ Ioc(-π, π]`. We register this as a hypothesis. -/

/-- **T-cocycle of `F_mod_eta`** (additive, principal branch).

For any `g : ℍ → ℂ` and any `τ : ℍ`, *if* the principal-log branch
condition

  `arg (exp (π·I/12)) + arg (η τ) ∈ Set.Ioc (-π) π`

holds (equivalently `π/12 + arg(η τ) ∈ Ioc(-π, π]`), then

  `F_mod_eta g (T • τ) − F_mod_eta g τ − (π·I/12) = g (T • τ) − g τ`.

The cocycle value is the constant `π·I/12`, matching the multiplicative
multiplier `exp(π·I/12)` of `η` under `T`. -/
theorem F_mod_eta_T_cocycle
    (g : ℍ → ℂ) (τ : ℍ)
    (hbranch :
      Complex.arg (Complex.exp ((π : ℂ) * I / 12))
        + Complex.arg (ModularForm.eta (τ : ℂ)) ∈ Set.Ioc (-(π : ℝ)) π) :
    F_mod_eta g (ModularGroup.T • τ) - F_mod_eta g τ - ((π : ℂ) * I / 12)
      = g (ModularGroup.T • τ) - g τ := by
  simp only [F_mod_eta]
  -- Multiplicative law
  have hmul := eta_T_smul τ
  -- η τ ≠ 0
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  -- exp factor ≠ 0
  have hexp : Complex.exp ((π : ℂ) * I / 12) ≠ 0 := Complex.exp_ne_zero _
  -- Apply log to the multiplicative identity, using the branch hypothesis.
  have hlog :
      Complex.log (ModularForm.eta ((ModularGroup.T • τ : ℍ) : ℂ))
        = Complex.log (Complex.exp ((π : ℂ) * I / 12))
          + Complex.log (ModularForm.eta (τ : ℂ)) := by
    rw [hmul]
    exact (Complex.log_mul_eq_add_log_iff hexp hη).mpr hbranch
  -- `log (exp (π·I/12)) = π·I/12` since `(π·I/12).im = π/12 ∈ (-π, π]`.
  have him : (((π : ℂ) * I / 12)).im = π / 12 := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have hlog_exp : Complex.log (Complex.exp ((π : ℂ) * I / 12)) = (π : ℂ) * I / 12 := by
    apply Complex.log_exp
    · rw [him]
      have hπ := Real.pi_pos
      nlinarith
    · rw [him]
      have hπ := Real.pi_pos.le
      nlinarith
  rw [hlog, hlog_exp]
  ring

/-- **S-cocycle of `F_mod_eta`** (additive, principal branch).

Under the branch-compatibility hypothesis

  `arg ((√I)⁻¹ · √(τ : ℂ)) + arg (η τ) ∈ Ioc(-π, π]`

we get the τ-dependent cocycle

  `F_mod_eta g (S • τ) − F_mod_eta g τ − Complex.log ((√I)⁻¹ · √(τ : ℂ))
     = g (S • τ) − g τ`.

The cocycle carrier `Complex.log ((√I)⁻¹ · √(τ : ℂ))` is the standard
Dedekind log-multiplier; on the principal branch it equals
`(1/2) · log(-I·τ)`, as recorded in `S_cocycle_carrier_eq_half_log_neg_I_mul`
below (with one further branch hypothesis). -/
theorem F_mod_eta_S_cocycle
    (g : ℍ → ℂ) (τ : ℍ)
    (hbranch :
      Complex.arg ((Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ))
        + Complex.arg (ModularForm.eta (τ : ℂ)) ∈ Set.Ioc (-(π : ℝ)) π) :
    F_mod_eta g (ModularGroup.S • τ) - F_mod_eta g τ
        - Complex.log ((Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ))
      = g (ModularGroup.S • τ) - g τ := by
  simp only [F_mod_eta]
  -- Multiplicative law η(S•τ) = (√I)⁻¹ · √τ · η τ
  have hmul := eta_S_smul τ
  -- Non-vanishing facts
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  -- √I ≠ 0
  have hsqrtI : Complex.sqrt I ≠ 0 := by
    rw [sqrt_eq_exp Complex.I_ne_zero]; exact Complex.exp_ne_zero _
  have hsqrtInv : (Complex.sqrt I)⁻¹ ≠ 0 := inv_ne_zero hsqrtI
  -- √τ ≠ 0
  have hsqrtτ : Complex.sqrt (τ : ℂ) ≠ 0 := by
    rw [sqrt_eq_exp (UpperHalfPlane.ne_zero τ)]; exact Complex.exp_ne_zero _
  -- The product (√I)⁻¹ · √τ ≠ 0
  have hprod : (Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) ≠ 0 := mul_ne_zero hsqrtInv hsqrtτ
  -- Apply log to the multiplicative identity using the branch hypothesis.
  have hlog :
      Complex.log (ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ))
        = Complex.log ((Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ))
          + Complex.log (ModularForm.eta (τ : ℂ)) := by
    rw [hmul,
        show ((Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) * ModularForm.eta (τ : ℂ) : ℂ)
          = ((Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ)) * ModularForm.eta (τ : ℂ) by ring]
    exact (Complex.log_mul_eq_add_log_iff hprod hη).mpr hbranch
  rw [hlog]
  ring

/-! ## Section 4. The standard form of the S-carrier

The S-cocycle carrier in `F_mod_eta_S_cocycle` is `log((√I)⁻¹ · √τ)`.
On the principal branch this equals `(1/2) · log(-I·τ)`, the standard
"half-log of `−iτ`" form quoted in the introduction. The identity
depends on yet another branch-compatibility condition between
`arg(−I)` and `arg(τ)`. We register this as a lemma. -/

/-- Standard form of the S-cocycle carrier as `(1/2) · log(-I·τ)`,
under the branch-compatibility hypothesis
`arg(-I) + arg(τ) ∈ Ioc(-π, π]`. -/
lemma S_cocycle_carrier_eq_half_log_neg_I_mul
    (τ : ℍ)
    (hbranch : Complex.arg (-I) + Complex.arg (τ : ℂ) ∈ Set.Ioc (-(π : ℝ)) π) :
    Complex.log ((Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ)) =
      (1 / 2 : ℂ) * Complex.log ((-I) * (τ : ℂ)) := by
  -- Step 1. Rewrite (√I)⁻¹ as √(-I) (principal branch).
  have hI_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hnegI_ne : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr hI_ne
  have hsqrtI_inv : (Complex.sqrt I)⁻¹ = Complex.sqrt (-I) := by
    rw [sqrt_eq_exp hI_ne, sqrt_eq_exp hnegI_ne]
    rw [Complex.log_I, Complex.log_neg_I, ← Complex.exp_neg]
    congr 1
    ring
  rw [hsqrtI_inv]
  -- Step 2. Combine √(-I) · √τ = √((-I)·τ) using the half-log identity.
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hnegIτ_ne : ((-I : ℂ) * (τ : ℂ)) ≠ 0 := mul_ne_zero hnegI_ne hτ_ne
  rw [sqrt_eq_exp hnegI_ne, sqrt_eq_exp hτ_ne, ← Complex.exp_add,
      show (Complex.log (-I) / 2 + Complex.log (τ : ℂ) / 2 : ℂ)
        = (Complex.log (-I) + Complex.log (τ : ℂ)) / 2 by ring]
  -- Combine: log(-I) + log τ = log((-I)·τ)
  have hsum_eq : Complex.log (-I) + Complex.log (τ : ℂ) =
      Complex.log ((-I) * (τ : ℂ)) := by
    exact ((Complex.log_mul_eq_add_log_iff hnegI_ne hτ_ne).mpr hbranch).symm
  rw [← hsum_eq]
  -- Now log(exp((log(-I) + log τ)/2)) = (log(-I) + log τ)/2 since the imaginary
  -- part is (arg(-I) + arg τ)/2 ∈ ((-π)/2, π/2] ⊂ (-π, π].
  have him :
      ((Complex.log (-I) + Complex.log (τ : ℂ)) / 2 : ℂ).im
        = (Complex.arg (-I) + Complex.arg (τ : ℂ)) / 2 := by
    simp [Complex.add_im, Complex.log_im]
  have hlogexp :
      Complex.log (Complex.exp ((Complex.log (-I) + Complex.log (τ : ℂ)) / 2))
        = (Complex.log (-I) + Complex.log (τ : ℂ)) / 2 := by
    apply Complex.log_exp
    · rw [him]
      have h1 := hbranch.1
      have hπ := Real.pi_pos
      linarith
    · rw [him]
      have h2 := hbranch.2
      have hπ := Real.pi_pos.le
      linarith
  rw [hlogexp]
  ring

/-! ## Section 5. Specialization: T-invariant `g`

When `g` is T-invariant (e.g., a weight-0 modular form, or any function
factoring through `q = exp(2π·I·τ)`), the residual `g(T•τ) − g τ` vanishes
and we obtain the **clean** additive T-translation identity. -/

/-- **Specialization for T-periodic `g`.** When `g (T • τ) = g τ` and the
branch hypothesis holds, the cocycle gives the clean identity

  `F_mod_eta g (T • τ) − F_mod_eta g τ = π·I/12`. -/
theorem F_mod_eta_T_invariant_g
    (g : ℍ → ℂ) (h_g_inv : ∀ τ : ℍ, g (ModularGroup.T • τ) = g τ) (τ : ℍ)
    (hbranch :
      Complex.arg (Complex.exp ((π : ℂ) * I / 12))
        + Complex.arg (ModularForm.eta (τ : ℂ)) ∈ Set.Ioc (-(π : ℝ)) π) :
    F_mod_eta g (ModularGroup.T • τ) - F_mod_eta g τ = (π : ℂ) * I / 12 := by
  have hcoc := F_mod_eta_T_cocycle g τ hbranch
  rw [h_g_inv, sub_self] at hcoc
  linear_combination hcoc

/-! ## Outlook

This file establishes the additive cocycle structure of `log η`
*on the principal branch*, with the necessary branch hypotheses stated
explicitly. The next steps in a full Eichler-Shimura formalization would
be:

  1. Construct the canonical continuous branch of `log η` on `ℍ`
     (using `multipliableLocallyUniformlyOn_eta` and the simply
     connected nature of `ℍ`), and discharge the branch hypotheses
     automatically for any `τ ∈ ℍ`.

  2. Combine the T- and S-cocycles into a full `SL(2, ℤ)`-1-cocycle
     `c : SL(2, ℤ) → (ℍ → ℂ)` for the slash action of weight `1/2`.

  3. Restrict to weight-0 modular targets `g` and read off the
     resulting period-integral identities.

  Step 1 in particular reduces all branch hypotheses to a statement
  about the range of `arg (η τ)` on `ℍ`. Numerically it stays well
  inside `(-π/2, π/2)` (in fact close to `π·τ.re/12`), so the
  branch hypotheses hold with room to spare; making this precise is
  a standard but nontrivial analytic lemma. -/

end EML.Identities.EtaCocycle
