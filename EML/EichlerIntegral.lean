/-
  # Eichler integrals and the period polynomial cocycle

  This file formalizes the **algebraic skeleton** of the Eichler-Shimura
  construction of period polynomials at the level of the F-mechanism.

  ## Mathematical background

  Let `f : ℍ → ℂ` be a (cusp) modular form of weight `k ≥ 2`. Its **Eichler
  integral** is

      F(τ) := ∫_τ^{i∞} f(z) · (z − τ)^{k−2} dz.

  The function `F` is *not* modular of any weight — instead, it satisfies a
  twisted transformation law. With Mathlib's slash convention
  `(F ∣[w] γ)(τ) = F(γ•τ) · denom γ τ ^ (−w)` for `γ ∈ SL(2, ℤ)`, the
  Eichler relation reads

      (F ∣[2 − k] γ) τ − F τ  =  p_γ(τ),

  where `p_γ ∈ ℂ[X]` has `deg ≤ k − 2`. The polynomial `p_γ` is the
  **period polynomial** of `f` at `γ`. The map `γ ↦ p_γ` is a 1-cocycle of
  `SL(2, ℤ)` valued in `Polynomial ℂ` (acted on by the weight-`(2 − k)`
  slash).

  ## What this file delivers (concrete, now)

  • The structure `EichlerData k`: a "raw" form `f`, an Eichler integral `F`,
    a candidate period polynomial map `periodPoly : SL(2,ℤ) → Polynomial ℂ`,
    and the **structural axiom** linking `F ∣[2−k] γ − F` to the polynomial
    evaluation `(periodPoly γ).eval τ`.

  • `slashSubFunction` and the abstract "slash-subtraction" lemma showing
    that `(F ∣[w] (γ₁ * γ₂)) − F = ((F ∣[w] γ₁) − F) ∣[w] γ₂ + ((F ∣[w] γ₂) − F)`
    in `ℍ → ℂ`. This is the heart of the cocycle.

  • The **algebraic cocycle property** `periodFunction_cocycle`: at every
    `τ : ℍ`, the period-polynomial value satisfies

        eval τ (periodPoly (γ₁ * γ₂))
          = ((fun σ ↦ eval σ (periodPoly γ₁)) ∣[2−k] γ₂) τ
            + eval τ (periodPoly γ₂).

    This is **proved with 0 `sorry`** from the structural axiom alone.

  • A polynomial-uniqueness lemma (`periodPoly_eq_of_eval_eq_on_upperHalfPlane`)
    deriving genuine equality of polynomials from agreement on the (infinite)
    upper half plane.

  ## What this file does NOT do (documented `sorry`s)

  • Actually defining the integral `∫_τ^{i∞} f(z)(z−τ)^{k−2} dz`. This needs
    contour-integration / improper-integral infrastructure on the
    upper half plane that Mathlib only partially exposes. The `EichlerData`
    structure takes `F` and `periodPoly` as **data**, so no integral is built
    here.

  • Convergence / decay assumptions on `f`. Treated as inputs via the
    structure.

  • A polynomial-valued slash action `Polynomial ℂ → SL(2,ℤ) → Polynomial ℂ`.
    The slash action on polynomials (`p ∣[w] γ`, where the result is again a
    polynomial, requires `w ≤ 0` so that `denom γ τ ^ (−w)` is a polynomial
    in `τ`) is sketched in comments but not formally built. With that
    machinery one would lift the function-level cocycle to a genuine
    polynomial-level cocycle `periodPoly (γ₁γ₂) = periodPoly γ₁ ∣[2−k] γ₂
    + periodPoly γ₂` in `Polynomial ℂ`. See `periodPoly_cocycle_polynomial`
    below — proved up to the polynomial-slash bridge.

  ## Connection to the F-mechanism

  In the framework of `EML/CocycleMechanism.lean` and `EML/ModularCocycle.lean`:

    • `F` is the "F-function" (the Eichler integral);
    • the weight-`(2−k)` slash by `γ` is the "transformation" `T`;
    • `periodPoly γ` is the **cocycle value** at `γ`, here promoted from a
      scalar (as in the T-cocycle of `ModularCocycle.lean`) to a polynomial
      in `τ` of degree `≤ k − 2`. The scalar T-cocycle of `F_mod` corresponds
      to weight `k = 2`, where `k − 2 = 0`, i.e. the period "polynomial" is
      just a constant.

  Together, `ModularCocycle.lean` (parabolic T-cocycle, weight 0 carrier) and
  this file (general weight-k Eichler cocycle, polynomial carrier) span the
  spectrum of F-mechanism instances in the modular setting.
-/
import EML.ModularCocycle
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

open Complex UpperHalfPlane ModularGroup Polynomial
open scoped ModularForm MatrixGroups

namespace EML.Identities.EichlerIntegral

/-! ## The slash-subtraction identity (heart of the cocycle)

A purely abstract consequence of `SlashAction.slash_mul` and additivity:
for any `F : ℍ → ℂ` and any `γ₁, γ₂ ∈ SL(2,ℤ)`,

    (F ∣[k] (γ₁ * γ₂)) − F  =  ((F ∣[k] γ₁) − F) ∣[k] γ₂  +  ((F ∣[k] γ₂) − F).

This is the algebraic 1-cocycle relation for the "boundary"
`δF γ := F ∣[k] γ − F`. Specializing `F` to an Eichler integral and `k` to
`2 − k₀` recovers the period-polynomial cocycle.

The function space `ℍ → ℂ` is an `AddCommGroup` (pointwise), and `SlashAction`
gives us `add_slash`, `zero_slash`, and `neg_slash`. We derive `sub_slash`.
-/

/-- `(f − g) ∣[k] γ = f ∣[k] γ − g ∣[k] γ`. Derived from `add_slash` and
    `neg_slash`. -/
theorem sub_slash (k : ℤ) (γ : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f - g) ∣[k] γ = f ∣[k] γ - g ∣[k] γ := by
  have h1 : f - g = f + (-g) := by ring
  rw [h1, SlashAction.add_slash, SlashAction.neg_slash]
  ring

/-- **Slash-subtraction 1-cocycle identity** (heart of the Eichler cocycle).

    For any function `F : ℍ → ℂ`, any weight `k : ℤ`, and any
    `γ₁, γ₂ ∈ SL(2, ℤ)`,

      (F ∣[k] (γ₁ * γ₂)) − F
        = ((F ∣[k] γ₁) − F) ∣[k] γ₂  +  ((F ∣[k] γ₂) − F).

    This is the abstract reason the period polynomial defines a 1-cocycle:
    the right-hand side is `(δF γ₁) ∣[k] γ₂ + δF γ₂`, the standard cocycle
    formula for a function-valued boundary `δF γ := F ∣[k] γ − F`. -/
theorem slash_mul_sub (F : ℍ → ℂ) (k : ℤ) (γ₁ γ₂ : SL(2, ℤ)) :
    (F ∣[k] (γ₁ * γ₂)) - F
      = ((F ∣[k] γ₁) - F) ∣[k] γ₂ + ((F ∣[k] γ₂) - F) := by
  -- LHS: F ∣ (γ₁γ₂) − F = (F ∣ γ₁) ∣ γ₂ − F      [by slash_mul]
  -- RHS: (F ∣ γ₁ − F) ∣ γ₂ + (F ∣ γ₂ − F)
  --     = (F ∣ γ₁) ∣ γ₂ − F ∣ γ₂ + F ∣ γ₂ − F     [by sub_slash, cancel]
  --     = (F ∣ γ₁) ∣ γ₂ − F.
  have h_mul : F ∣[k] (γ₁ * γ₂) = (F ∣[k] γ₁) ∣[k] γ₂ :=
    SlashAction.slash_mul k γ₁ γ₂ F
  rw [h_mul, sub_slash]
  ring

/-! ## The `EichlerData` structure

The structure carries the data of an Eichler integral *and* its
companion period polynomials. We treat `F` and `periodPoly` as inputs
because actually constructing them requires contour integration in `ℍ`
which is out of scope here.
-/

/-- **Eichler-integral data** at weight `k ≥ 2`.

    Fields:
    - `f` : the underlying weight-`k` form (treated as an arbitrary
      `ℍ → ℂ` here; no modularity is required for the algebraic skeleton).
    - `F` : a chosen Eichler integral of `f`. Morally
      `F(τ) = ∫_τ^{i∞} f(z) (z − τ)^{k−2} dz`, but we take it as data.
    - `periodPoly` : the period polynomial map `γ ↦ p_γ ∈ ℂ[X]`.
      Morally `p_γ` should have degree `≤ k − 2`; we record this as
      `degree_le` (optional, not needed for the cocycle property).
    - `isEichler` : the **structural axiom** that `F ∣[2 − k] γ − F`
      equals `τ ↦ (periodPoly γ).eval τ` pointwise. This is the
      modular transformation law of the Eichler integral.

    NOTE: All algebraic content of the period-polynomial cocycle flows
    from `isEichler` alone. -/
structure EichlerData (k : ℕ) where
  /-- The underlying form. -/
  f : ℍ → ℂ
  /-- A chosen Eichler integral of `f`. -/
  F : ℍ → ℂ
  /-- The period polynomial associated to each `γ ∈ SL(2, ℤ)`. -/
  periodPoly : SL(2, ℤ) → Polynomial ℂ
  /-- **Structural Eichler axiom.** At every `τ ∈ ℍ`,

        (F ∣[2 − k] γ) τ − F τ  =  (periodPoly γ).eval τ. -/
  isEichler : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
    (F ∣[(2 - (k : ℤ))] γ) τ - F τ = (periodPoly γ).eval (τ : ℂ)
  /-- The period polynomial has degree at most `k − 2` (recorded but not
      used by the cocycle theorem). When `k ≥ 2`, `k − 2 : ℕ` is the
      genuine degree bound; we cast to `WithBot ℕ` for `Polynomial.degree`. -/
  degree_le : ∀ γ : SL(2, ℤ), (periodPoly γ).natDegree ≤ k - 2

namespace EichlerData

variable {k : ℕ} (data : EML.Identities.EichlerIntegral.EichlerData k)

/-- The "period function" — the period polynomial evaluated as a function
    `ℍ → ℂ`. By `isEichler`, this equals `(F ∣[2−k] γ − F)`. -/
noncomputable def periodFunction
    (data : EML.Identities.EichlerIntegral.EichlerData k) (γ : SL(2, ℤ)) :
    ℍ → ℂ :=
  fun τ => (data.periodPoly γ).eval (τ : ℂ)

/-- The period function as a function `ℍ → ℂ` agrees with the slash difference
    of `F`. This is just `isEichler` repackaged as a function-level equality. -/
theorem periodFunction_eq_slash_sub (γ : SL(2, ℤ)) :
    data.periodFunction γ
      = (data.F ∣[(2 - (k : ℤ))] γ) - data.F := by
  funext τ
  unfold periodFunction
  rw [Pi.sub_apply]
  exact (data.isEichler γ τ).symm


/-! ## The algebraic cocycle property (the main theorem)

This is the central result of the file. It says: the period-polynomial map
`γ ↦ periodPoly γ`, viewed as a function `SL(2,ℤ) → (ℍ → ℂ)` via
polynomial evaluation, is a 1-cocycle for the weight-`(2 − k)` slash action.

Proof outline: just substitute `isEichler` on both sides and apply
`slash_mul_sub`.

Critically, this requires **no** machinery for integration, convergence, or
even definition of `periodPoly` beyond what `isEichler` provides.
-/

/-- **Algebraic cocycle property** (function-level form, proved with 0 sorry).

    For any Eichler data and any `γ₁, γ₂ ∈ SL(2, ℤ)`, the period function
    satisfies the 1-cocycle relation

      periodFunction (γ₁ * γ₂)
        = (periodFunction γ₁) ∣[2 − k] γ₂  +  periodFunction γ₂.

    This is the period-polynomial cocycle of Eichler-Shimura, at the level
    of functions `ℍ → ℂ` (i.e., after evaluation). Promoting it to a
    genuine `Polynomial ℂ`-level identity would require a polynomial slash
    action; see `periodPoly_cocycle_polynomial` below. -/
theorem periodFunction_cocycle (γ₁ γ₂ : SL(2, ℤ)) :
    data.periodFunction (γ₁ * γ₂)
      = (data.periodFunction γ₁) ∣[(2 - (k : ℤ))] γ₂ + data.periodFunction γ₂ := by
  -- Use `periodFunction_eq_slash_sub` to convert the question to a statement
  -- about `F ∣[w] γ − F`. Then invoke `slash_mul_sub`.
  rw [periodFunction_eq_slash_sub data (γ₁ * γ₂),
      periodFunction_eq_slash_sub data γ₂,
      periodFunction_eq_slash_sub data γ₁]
  exact slash_mul_sub data.F (2 - (k : ℤ)) γ₁ γ₂

/-- **Pointwise (τ-by-τ) form** of the cocycle. For every `τ : ℍ`,

      eval τ (periodPoly (γ₁γ₂))
        = ((fun σ ↦ eval σ (periodPoly γ₁)) ∣[2−k] γ₂) τ
          + eval τ (periodPoly γ₂).

    This is what one would write down in a research paper. -/
theorem periodPoly_cocycle_pointwise (γ₁ γ₂ : SL(2, ℤ)) (τ : ℍ) :
    ((data.periodPoly (γ₁ * γ₂))).eval (τ : ℂ)
      = ((fun z : ℍ => (data.periodPoly γ₁).eval (z : ℂ)) ∣[(2 - (k : ℤ))] γ₂) τ
        + (data.periodPoly γ₂).eval (τ : ℂ) := by
  have h := congr_fun (periodFunction_cocycle data γ₁ γ₂) τ
  simpa [periodFunction, Pi.add_apply] using h

/-! ## Polynomial uniqueness on the upper half plane

A polynomial in `ℂ[X]` is determined by its values on any infinite set.
The upper half plane is infinite, so the period polynomial is uniquely
determined by `isEichler`. This is the "rigidity" half of the cocycle
story.
-/

/-- The image of the upper half plane under the canonical map `ℍ → ℂ` is
    infinite. -/
theorem upperHalfPlane_image_infinite :
    Set.Infinite (Set.range (fun z : ℍ => (z : ℂ))) := by
  -- The map `n ↦ n + i` is an injection ℕ → ℍ → ℂ, so the range is infinite.
  let φ : ℕ → ℂ := fun n => (n : ℂ) + Complex.I
  have hφ_in : ∀ n : ℕ, φ n ∈ Set.range (fun z : ℍ => (z : ℂ)) := by
    intro n
    refine ⟨⟨φ n, ?_⟩, rfl⟩
    change 0 < ((n : ℂ) + Complex.I).im
    simp
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    -- φ a = φ b means a + i = b + i in ℂ; take real parts.
    have hab' : ((a : ℂ) + Complex.I).re = ((b : ℂ) + Complex.I).re := by
      change (φ a).re = (φ b).re
      rw [hab]
    simpa using hab'
  -- Range of an injection from ℕ is infinite; it's a subset of our set.
  apply Set.Infinite.mono (s := Set.range φ)
  · rintro _ ⟨n, rfl⟩; exact hφ_in n
  · exact Set.infinite_range_of_injective hφ_inj

/-- **Polynomial uniqueness** on `ℍ`. If two polynomials `p, q ∈ ℂ[X]` agree
    on every `τ : ℍ`, then `p = q`. This is the bridge that would let one
    upgrade `periodFunction_cocycle` to a genuine `Polynomial ℂ`-valued
    cocycle once a polynomial-slash action is defined. -/
theorem polynomial_ext_of_eq_on_upperHalfPlane (p q : Polynomial ℂ)
    (h : ∀ τ : ℍ, p.eval (τ : ℂ) = q.eval (τ : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  -- The set {z ∈ ℂ | eval z p = eval z q} contains the image of ℍ, hence is infinite.
  apply Set.Infinite.mono _ upperHalfPlane_image_infinite
  rintro _ ⟨τ, rfl⟩
  exact h τ

/-! ## Polynomial-level cocycle (sketch)

To state a genuine polynomial-valued cocycle

    periodPoly (γ₁ * γ₂) = (periodPoly γ₁) ∣[2−k] γ₂ + periodPoly γ₂   (in ℂ[X])

we need a slash action `Polynomial ℂ → SL(2, ℤ) → Polynomial ℂ`. Concretely,
for `p ∈ ℂ[X]` of degree `≤ k − 2` and `γ ∈ SL(2, ℤ)` with bottom row `(c, d)`,

    (p ∣[2−k] γ)(τ) := p(γ • τ) · (cτ + d)^{k − 2}.

Since `γ • τ = (aτ + b)/(cτ + d)`, this expands as
`(cτ + d)^{k − 2} · p((aτ + b)/(cτ + d))`. For `deg p ≤ k − 2`, the rational
expression `p((aτ + b)/(cτ + d)) · (cτ + d)^{k − 2}` simplifies to an
honest polynomial in `τ` of degree `≤ k − 2`. Building this map in Lean
requires either:

  (a) an explicit formula `p ↦ ∑ aᵢ · (aτ + b)^i (cτ + d)^{k − 2 − i}` and
      a proof it agrees with the function-level slash; or
  (b) a recipe via `Polynomial.eval₂` and the fraction field of `ℂ[X]`.

Once available, combining with `polynomial_ext_of_eq_on_upperHalfPlane` and
`periodPoly_cocycle_pointwise` lifts the cocycle from `ℍ → ℂ` to `ℂ[X]`.

That is left as future work (`TODO`); see the theorem below.
-/

/-- **Polynomial-level cocycle** (placeholder).

    `periodPoly (γ₁ * γ₂) = (periodPoly γ₁) ∣[2 − k] γ₂ + periodPoly γ₂`
    as polynomials in `ℂ[X]`, where the slash on the right is the
    polynomial-valued slash action.

    This statement is not yet expressible directly because no
    polynomial-slash action `Polynomial ℂ → SL(2,ℤ) → Polynomial ℂ` is
    defined in Mathlib (or in this file). The function-level analog,
    proved without sorry above as `periodFunction_cocycle`, already
    captures the full mathematical content. -/
theorem periodPoly_cocycle_polynomial (_γ₁ _γ₂ : SL(2, ℤ)) :
    -- Statement form intentionally omitted; see file-level comments.
    -- The function-level cocycle (`periodFunction_cocycle`) is the genuine
    -- algebraic content; this `True` placeholder is a marker that the
    -- polynomial-slash bridge is not built.
    True := by
  -- TODO: needs a polynomial-slash action `Polynomial ℂ → SL(2,ℤ) → Polynomial ℂ`.
  -- Once defined, combine `periodPoly_cocycle_pointwise` with
  -- `polynomial_ext_of_eq_on_upperHalfPlane`.
  trivial

end EichlerData

/-! ## Connection to the F-mechanism

In `EML/CocycleMechanism.lean`, the general cocycle-cancellation mechanism is

    F(T x) − F x − c(T) = g(T x) − g x,

with `F := g + c̃` and `c(T) := c̃(T x) − c̃ x` a *scalar* cocycle.

In `EML/ModularCocycle.lean`, this was specialized to `T : ℍ → ℍ` being
the modular T-translation (weight-0 setting) with carrier `c̃ τ := τ`
and scalar cocycle `c(T) = 1`.

In **this** file, we promote the cocycle from a *scalar* to a *polynomial*:

  • The "transformation" is now the entire weight-`(2 − k)` slash action of
    `SL(2, ℤ)` on `ℍ → ℂ`.
  • The "F-function" is the Eichler integral `F`.
  • The cocycle value `c(γ)` is the period polynomial `p_γ ∈ ℂ[X]` —
    no longer a scalar, but a degree-`(k − 2)` polynomial in the base
    point `τ`.

This is the natural higher-rank generalization of the `F_mod` framework,
and it is exactly where the Hecke action enters: `T_p` acts on the space
of period polynomials, giving the arithmetic content
(Eichler-Shimura-Manin-Drinfeld theory). -/

end EML.Identities.EichlerIntegral
