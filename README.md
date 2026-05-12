# EML: Lean 4 Formalization

A Lean 4 + Mathlib formalization of the results in:

> **Andrzej Odrzywołek** (Institute of Theoretical Physics, Jagiellonian University),
> *"All elementary functions from a single binary operator"*,
> [arXiv:2603.21852](https://arxiv.org/abs/2603.21852) [cs.SC], April 2026.

**All mathematical results from the paper are due to Odrzywołek.** This project is a machine-checked formalization of his work in the Lean 4 theorem prover, plus some original extensions (algebraic structure, calculus, and fixed-point analysis of the EML operator). The discovery of the EML operator, the exhaustive search methodology, the completeness proof strategy, and all identities originate from the paper above.

## The result

Odrzywołek discovered that a single binary operator

```
eml(x, y) = exp(x) - ln(y)
```

together with the constant **1**, generates the entire standard repertoire of a scientific calculator: arithmetic, exponentiation, logarithms, trigonometric and hyperbolic functions, their inverses, and fundamental constants like *e*, *π*, and *i*. This is the continuous analogue of the NAND gate in digital logic.

## What is formalized

**32 Lean files. 0 sorry across 30 of them; 2 honest `sorry`s in `HeckeAction.lean` (with multi-line `-- TODO:` references to Diamond–Shurman §5.2.1 and Manin 1972).**

### 🆕 Recent additions (NEW)

The 17 files marked **NEW** below are recent work, all on a single research arc: starting from the anti-diagonal identity `e^x = (F(3x) − F(x) − ln 3) / (F(2x) − F(x) − ln 2) − 1` with `F = exp + log`, building outward through universal cocycle mechanism, modular cocycles, an F-rational grammar, Eichler integrals, and Hecke operators. The arc bridges elementary function theory and analytic number theory, with all proofs machine-checked.

Companion empirical work (in `/Users/thomasdifiore/`):
- `eml_sr_experiment.py` — brute-force comparison of EML grammar vs. standard symbolic-regression grammar.
- `f_tree_search.py` — confirms `exp(x)` is recoverable from `F` in the F-rational grammar at tree-size K = 21; no smaller tree found by enumerating 3.2M candidates up to size 9.
- `f_activation_experiment.py` — PyTorch comparison of F as a neural-network activation vs. ReLU/GELU/Tanh.

### Core identities (`Basic.lean`)
- `exp(x) = eml(x, 1)`
- `e = eml(1, 1)`
- `ln(z) = eml(1, eml(eml(1, z), 1))` for z > 0 — paper equation (5)
- `0 = eml(1, eml(eml(1, 1), 1))` — pure EML tree, K = 7
- `-1` and `2` derivable via the exp-log chain

### All 36 calculator primitives (`Arithmetic.lean`, `Transcendental.lean`, `Complex.lean`)

Every primitive from the paper's Table 1 is shown to reduce to `{1, eml}`:

| Category | Primitives |
|---|---|
| **Constants** | 1, e, 0, -1, 2, π, i |
| **Functions** | exp, ln, inv, half, minus, √, sqr, σ, sin, cos, tan, arcsin, arccos, arctan, sinh, cosh, tanh, arsinh, arcosh, artanh |
| **Operations** | +, −, ×, /, x^y, log_b, avg, hypot |

Trigonometric functions and the constants π and i are proved over ℂ using Euler's formula and a complex EML operator `ceml(x,y) = exp(x) - log(y)`.

### Constructive EML trees (`Trees.lean`)

Pure EML trees for the "hard" functions, found by exhaustive brute-force search (reproducing the paper's Table 4 methodology) and verified symbolically in Lean:

| Function | K | Theorem |
|---|---|---|
| `x - y` | 11 | `eml_expr_sub_eval` |
| `-x` | 17 | `eml_expr_neg_eval` |
| `1/x` | 17 | `eml_expr_inv_eval` |
| `x * y` | 17 | `eml_expr_mul_eval` |

The search script (`search.py`) is included for reproducibility.

### EML grammar and expression trees (`Grammar.lean`)
- Inductive types `EmlTree`, `EmlExpr`, `EmlExpr₂` formalizing the context-free grammar `S → 1 | x | eml(S, S)`
- Verified tree evaluations matching Figure 2: exp (K=3), ln (K=7), identity (K=9), zero (K=7), e (K=3)

### Compiler correctness (`Compile.lean`, `ComplexCompile.lean`)
- An `ExpLogExpr` type for expressions built from `{1, x, exp, log}`
- A `compile` function converting exp-log expressions to EML trees
- **`compile_correct`** (`Compile.lean`): over ℝ, unconditional. Real-domain
  evaluation uses `Real.log`, which satisfies `log(exp x) = x` for all `x : ℝ`
  (since `exp x > 0`), so no branch hypothesis is needed.
- **`compile_correctC`** (`ComplexCompile.lean`): over ℂ, conditioned on a
  branch predicate `BranchOk x e` that asserts every `cLog` node's inner
  exponent stays in the principal strip `(−π, π]`. The unconditional complex
  version is *false*: at `x = −1` for `e = cLog .var`, compile gives `−πi`
  while the actual value is `πi` — the `2πi` branch discrepancy is real and
  intrinsic to the principal-log setup.

### Exp-log pair (`ExpLog.lean`)
- Paper equation (1): `x × y = exp(ln x + ln y)` and `x + y = ln(exp x · exp y)`
- Subtraction, division, negation, reciprocal, integers via exp-log

### Operator variants (`Variants.lean`)
- EDL operator: `edl(x, y) = exp(x) / ln(y)` — paper equation (4b)
- Negated EML: `neml(x, y) = ln(x) - exp(y)` — paper equation (4c)
- Relationships between variants

### Master formula (`MasterFormula.lean`)
- Level-1 and level-2 parametrized master formulas — paper equation (6)
- Recovering `exp(x)`, `e`, and `exp(exp(x))` from specific parameter choices
- Parameter count formula: `5 × 2ⁿ − 6`

### The suc/pre/inv identity (`SucPreInv.lean`)
- `suc(inv(pre(inv(suc(inv(x)))))) = -x` — paper Section 2

### Algebraic structure (`Algebra.lean`) — *original*
Properties of eml as a binary operation, not discussed in the paper:
- **Non-commutativity**: `eml(0, 1) = 1 ≠ e = eml(1, 0)`
- **Non-associativity**: `eml(eml(0,1), 1) = e ≠ 0 = eml(0, eml(1,1))`
- **No identity element**: no `e` exists such that `eml(e, x) = x` for all `x`, nor `eml(x, e) = x` for all `x`

### Calculus of EML (`Calculus.lean`) — *original*
Differential and monotonicity properties of eml:
- **Partial derivatives**: `∂/∂x eml(x, y) = exp(x)` and `∂/∂y eml(x, y) = -1/y`
- **Monotonicity**: strictly increasing in x, strictly decreasing in y (for y > 0)
- **Injectivity**: injective in each argument (for y > 0 in the second)

### Fixed points and zeros (`FixedPoints.lean`) — *original*
Analysis of special values of eml:
- **Zero set**: `eml(a, b) = 0 ↔ b = exp(exp(a))`
- **Level sets**: `eml(a, b) = c ↔ b = exp(exp(a) - c)` for b > 0
- **Fixed point equation**: `eml(x, x) = x ↔ exp(x) - x = log(x)`
- **Fixed points satisfy x > 1** (proved via strict convexity of exp)
- **Self-application**: `eml(x, eml(x, 1)) = exp(x) - x`

### Anti-diagonal F identities — *original*, **NEW**

The "anti-diagonal" of EML is the function `F(x) := eml(x, x⁻¹) = exp(x) + log(x)`. The single combinatorial fact `log(k·x) − log(x) = log(k)` generates a wide family of identities relating `F` at dilated points to algebraic combinations of `exp`. Seventeen files explore the mechanism, its universal scope, its limits, and its connection to analytic number theory.

#### `Identities.lean` — The main identity *(NEW)*

For `x ≠ 0`,
```
e^x = (F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2) − 1.
```

- `F_eq_eml_inv`: `F(x) = eml(x, x⁻¹)`, placing F as a specific EML expression.
- `F_dilate_sub`: `F(k·x) − F(x) − log(k) = exp(k·x) − exp(x)` — the cancellation lemma underlying everything else.
- `exp_eq_F_quotient`: the main identity, by reduction to `(a³ − a)/(a² − a) = a + 1` with `a = e^x`.

#### `IdentitiesFamily.lean` — Family extensions *(NEW)*

- `exp_mul_eq_F_quotient`: infinite cyclotomic family, `e^{(m−1)x}` from `F` at `{x, m·x, (2m−1)·x}` for all real `m ≥ 2`.
- `F_pow`, `F_pow_ratio_eq`: power-function anti-diagonal `F_a(x) := x^a + log(x)`. The ratio `(F_a(3x) − F_a(x) − log 3) / (F_a(2x) − F_a(x) − log 2) = (3^a − 1)/(2^a − 1)` is constant in `x` and encodes the exponent `a`.
- `F_second_diff`: second-order finite difference `F(3x) − 2F(2x) + F(x) = e^x(e^x − 1)² + log(3/4)`.
- `sinh_eq_F_diff`, `cosh_eq_F_sum`: hyperbolic functions from the parity reflection `F(x) ± F(−x)`.
- `F_inv_sum`, `F_inv_diff`: inversion identities. `F(x) + F(1/x) = e^x + e^{1/x}` — log is odd under inversion and cancels in the sum.
- `F_dilate_cocycle`: the dilation difference `c(k, x) = F(k·x) − F(x) − log(k)` is a 1-cocycle for the multiplicative-group action on ℝ.

#### `IdentitiesZoo.lean` — Universal mechanism *(NEW)*

- `anti_diag_dilate_sub`: for **any** function `g`, the function `F_g(x) := g(x) + log(x)` satisfies `F_g(k·x) − F_g(x) − log(k) = g(k·x) − g(x)`. The choice of `g` is irrelevant; the cancellation rests purely on `log`.
- Specializations: `F_sin`, `F_cos`, `F_sinh`, `F_cosh`, `F_id` (with `g = identity`).

#### `LogLogBreaks.lean` — Negative result *(NEW)*

Replacing `log(x)` by `log(log(x))` breaks the cancellation. `F_loglog_breaks`: at `x = e`, `k = e`, the residual is `log 2 − 1`, which is negative since `log 2 < log e = 1`. This rules out iterated logs and singles out log at "depth 1" as uniquely positioned.

#### `ComplexIdentities.lean` — Trig from F at imaginary argument *(NEW)*

Define `F_C(z) := exp(z) + log(z)` over ℂ. For `x > 0`:
- `F_C_imag_re`: `Re(F_C(i·x)) = cos(x) + log(x)`.
- `F_C_imag_im`: `Im(F_C(i·x)) = sin(x) + π/2`.
- `cos_eq_F_C_re`, `sin_eq_F_C_im`: trig extraction from `F_C`.

#### `MellinHaar.lean` — Differential structure / Haar bridge *(NEW)*

- `hasDerivAt_F`: `F'(x) = exp(x) + x⁻¹`. The `x⁻¹` summand is the density of the multiplicative Haar measure `dx/x` on `(ℝ⁺, ·)`; the `exp(x)` summand is the F-tangent that survives dilation differences.
- `F_euler_eq`: `x · F'(x) − 1 = x · exp(x)` (Euler-operator form).
- `hasDerivAt_F_deriv`: `F''(x) = exp(x) − 1/x²`.

The differential characterization makes explicit why the `log(k)` constants pervade every identity in this section: they are line integrals of the multiplicative-Haar density `1/x` from `1` to `k`.

#### `MultiVar.lean` — Multi-variable extension *(NEW)*

`F₂(x, y) := exp(x) + exp(y) + log(x) + log(y) = F(x) + F(y)`. Joint and independent dilations give analogous identities with `2·log(k)` and `log(a) + log(b)` respectively.

#### `VonMangoldt.lean` — Number-theoretic structure *(NEW)*

The dilation cocycle `c(k) := log(k)`, restricted to natural-number dilations, decomposes via the von Mangoldt function `Λ`:
- `cocycle_eq_logSum_vonMangoldt`: `c(n) = log(n) = ∑_{d ∣ n} Λ(d)` (the standard `log = Λ ∗ 1` Dirichlet identity).
- `cocycle_at_prime_power`: `c(p^j) = j · log(p)` for prime `p`.
- `F_dilate_sub_prime_power`, `F_dilate_sub_divisor_sum`: F-identities expressed in `Λ` form.

The cocycle of the F-identity is the same `log = Λ ∗ 1` decomposition that drives the explicit formula in analytic number theory. The theorems here are structural — they identify the vocabulary, not the content.

#### `Characterization.lean` — Converse universal mechanism *(NEW)*

The universal mechanism in `IdentitiesZoo` proves `F = g + α·log + const` is *sufficient* for the dilation cancellation. This file proves it is also *necessary*:
- `pure_log_characterization`: if `h(k·x) − h(x) = α·log(k)` for all positive `x, k`, then `h(x) = α·log(x) + h(1)`. A three-line proof via `k := x⁻¹`.
- `dilation_decomposition`: if `F(k·x) − F(x) − α·log(k) = g(k·x) − g(x)` for all positive `x, k`, then `F = g + α·log + (F(1) − g(1))`.
- `F_unique_up_to_constant`: specialization — the canonical `F = exp + log` is uniquely characterized (up to additive constant) by its dilation-cancellation behavior.

Combined with `F_dilate_sub` (existence direction), this gives a complete characterization of F by dilation differences.

#### `FRational.lean` — Univariate Sheffer completeness *(NEW)*

A different completeness result: the *univariate* function `F` plus rational arithmetic suffices to recover `exp` (and hence everything else).
- `FExpr` — inductive grammar: leaves (`var`, `const ℝ`), unary (`F`), binary (`+, −, ×, ÷`).
- `fFormulaTree` — explicit K=21 tree `((F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2)) − 1` for `exp(x)`.
- `fFormulaTree_size : fFormulaTree.size = 21` and `fFormulaTree_eval : fFormulaTree.eval x = exp x` (for `x ≠ 0`).
- `exp_from_univariate`, `exp_K_in_F_rational_at_most_21`: arity-reduction theorems (binary `eml` at K=3 → univariate `F` at K≤21, a ~7× node cost for arity reduction).

#### `TranslationCocycle.lean` — Translation analog of F *(NEW)*

The dilation F-mechanism is one instance of "cocycle cancellation under a group action." For the translation group `(ℝ, +)`, the canonical 1-cocycle is the identity, giving anti-diagonal `F̃(x) := exp(x) + x`:
- `F_trans_translate_sub`: `F̃(x+a) − F̃(x) − a = exp(x+a) − exp(x)`. Unconditional (no positivity needed).
- `exp_eq_F_trans_quotient`: `exp(a) = (F̃(x+2a) − F̃(x) − 2a) / (F̃(x+a) − F̃(x) − a) − 1` for `a ≠ 0`. Extracts `a` (the shift), not `x`.

#### `CocycleMechanism.lean` — General unifying theorem *(NEW)*

- `cocycle_cancellation`: abstract theorem unifying dilation and translation. For any transformation `T : ℝ → ℝ` and any "carrier" function `c̃` with `c̃(T x) − c̃(x) = c`, the function `g + c̃` satisfies the F-style cancellation against `g`.
- `dilate_specialization`, `translate_specialization`: recover `F_dilate_sub` and `F_trans_translate_sub` from the abstract theorem.

#### `ModularCocycle.lean` — F-mechanism on the upper half plane *(NEW)*

The T-action `τ ↦ τ + 1` on `ℍ` (Mathlib's `ModularGroup.T`) has cocycle value 1.
- `F_mod g τ := g τ + (τ : ℂ)` and `F_mod_T_cocycle`: T-cocycle theorem.
- `F_mod_T_invariant_g`: clean specialization for T-periodic `g` (e.g., weight-0 modular forms).
- `F_mod_T_pow_cocycle`: T^n cocycle iteration.

#### `SCocycle.lean` — S-action with log carrier *(NEW)*

The S-action `τ ↦ −1/τ` on `ℍ` has a τ-dependent cocycle (unlike T's constant cocycle).
- `F_mod_S g τ := g τ + Complex.log τ`.
- `c_S_eq`: closed-form `c_S(τ) = π·I − 2·log(τ)` via `Complex.log_inv` + `arg_neg_eq_arg_sub_pi_of_im_pos`. Verified numerically at τ = i (gives 0) and τ = 2i (gives −2·log 2).
- `F_mod_S_S_cocycle`, `F_mod_S_S_cocycle_explicit`: S-cocycle and explicit form.

#### `EtaCocycle.lean` — T and S cocycles of `log η` *(NEW)*

Classical Dedekind eta transformations (Rademacher), machine-checked.
- `eta_T_smul`: `η(T·τ) = exp(π·I/12) · η(τ)`. Derived from scratch — Mathlib has only the S-transformation (in `Discriminant.lean`) at the time of writing.
- `eta_S_smul`: packaging of Mathlib's S-transformation for SL(2,ℤ).
- `F_mod_eta_T_cocycle`: T-cocycle (constant `π·I/12`).
- `F_mod_eta_S_cocycle`: S-cocycle (carrier `(1/2)·log(-Iτ)`).
- Branch-compatibility hypotheses are honest side conditions matching `Complex.log_mul_eq_add_log_iff`.

#### `EichlerIntegral.lean` — Algebraic skeleton of Eichler integrals *(NEW)*

The natural higher-weight analog of additive cocycles. The cocycle becomes **polynomial-valued** (period polynomial) instead of scalar.
- `EichlerData k` — structure carrying `f, F, periodPoly`, the structural relation `F(γτ) − (cτ+d)^{k−2} · F(τ) = periodPoly γ(τ)`, and a degree bound.
- `slash_mul_sub` — abstract slash 1-cocycle identity.
- `periodFunction_cocycle` and `periodPoly_cocycle_pointwise` — algebraic cocycle property of the period polynomial proved structurally (no integration needed).
- `polynomial_ext_of_eq_on_upperHalfPlane` — polynomials in `ℂ[X]` are determined by their values on `ℍ` (helper lemma, no Eichler structure needed).
- TODO (documented in comments only — not `sorry`): actual integral construction `∫_τ^{i∞} f(z)(z-τ)^{k−2} dz` and polynomial-valued slash action.

#### `HeckeAction.lean` — Hecke operator skeleton *(NEW)*

The bridge from Eichler cocycles to L-functions of cusp forms. Mathlib has **no** Hecke-operator infrastructure (verified by searching all of Mathlib — only "Hecke's bound" on Fourier coefficients is present); this file establishes the framework.
- `heckeOp p hp k f` — definition of `T_p` in weight `k`.
- `heckeOp_add`, `heckeOp_smul`, `heckeOp_zero`: linearity. Proved.
- `heckeOp_slash_commute`, `heckeOp_period_polynomial`: deep theorems. **Stated, with 2 honest `sorry`s** — multi-line `-- TODO:` blocks citing Diamond–Shurman §5.2.1 (coset decomposition: ~1-2 weeks of Lean work) and Manin 1972 (Eichler integration: ~2-4 weeks once the prerequisites land).

## What is not formalized

- **Table 4 optimality**: proving a K value is *minimal* requires exhaustive enumeration of all smaller trees — a computation, not a deduction.
- **EDL completeness**: the paper states EDL also generates all primitives but provides no explicit constructions.
- **Symbolic regression convergence** (Section 4.3): an empirical result from training experiments.

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

```bash
lake update
lake build
```

## Attribution

The core mathematical content formalized here is the work of **Andrzej Odrzywołek**. The algebraic structure, calculus, and fixed-point sections are original extensions. Please cite his paper:

```
@article{odrzywołek2026eml,
  title={All elementary functions from a single binary operator},
  author={Odrzywołek, Andrzej},
  year={2026},
  eprint={2603.21852},
  archivePrefix={arXiv},
  primaryClass={cs.SC}
}
```

## License

MIT
