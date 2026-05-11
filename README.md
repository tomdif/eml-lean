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

**24 Lean files. 0 sorry.**

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

### Anti-diagonal F identities — *original*

The "anti-diagonal" of EML is the function `F(x) := eml(x, x⁻¹) = exp(x) + log(x)`. The single combinatorial fact `log(k·x) − log(x) = log(k)` generates a wide family of identities relating `F` at dilated points to algebraic combinations of `exp`. Nine files explore the mechanism, its universal scope, its limits, and its connection to analytic number theory.

#### `Identities.lean` — The main identity

For `x ≠ 0`,
```
e^x = (F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2) − 1.
```

- `F_eq_eml_inv`: `F(x) = eml(x, x⁻¹)`, placing F as a specific EML expression.
- `F_dilate_sub`: `F(k·x) − F(x) − log(k) = exp(k·x) − exp(x)` — the cancellation lemma underlying everything else.
- `exp_eq_F_quotient`: the main identity, by reduction to `(a³ − a)/(a² − a) = a + 1` with `a = e^x`.

#### `IdentitiesFamily.lean` — Family extensions

- `exp_mul_eq_F_quotient`: infinite cyclotomic family, `e^{(m−1)x}` from `F` at `{x, m·x, (2m−1)·x}` for all real `m ≥ 2`.
- `F_pow`, `F_pow_ratio_eq`: power-function anti-diagonal `F_a(x) := x^a + log(x)`. The ratio `(F_a(3x) − F_a(x) − log 3) / (F_a(2x) − F_a(x) − log 2) = (3^a − 1)/(2^a − 1)` is constant in `x` and encodes the exponent `a`.
- `F_second_diff`: second-order finite difference `F(3x) − 2F(2x) + F(x) = e^x(e^x − 1)² + log(3/4)`.
- `sinh_eq_F_diff`, `cosh_eq_F_sum`: hyperbolic functions from the parity reflection `F(x) ± F(−x)`.
- `F_inv_sum`, `F_inv_diff`: inversion identities. `F(x) + F(1/x) = e^x + e^{1/x}` — log is odd under inversion and cancels in the sum.
- `F_dilate_cocycle`: the dilation difference `c(k, x) = F(k·x) − F(x) − log(k)` is a 1-cocycle for the multiplicative-group action on ℝ.

#### `IdentitiesZoo.lean` — Universal mechanism

- `anti_diag_dilate_sub`: for **any** function `g`, the function `F_g(x) := g(x) + log(x)` satisfies `F_g(k·x) − F_g(x) − log(k) = g(k·x) − g(x)`. The choice of `g` is irrelevant; the cancellation rests purely on `log`.
- Specializations: `F_sin`, `F_cos`, `F_sinh`, `F_cosh`, `F_id` (with `g = identity`).

#### `LogLogBreaks.lean` — Negative result

Replacing `log(x)` by `log(log(x))` breaks the cancellation. `F_loglog_breaks`: at `x = e`, `k = e`, the residual is `log 2 − 1`, which is negative since `log 2 < log e = 1`. This rules out iterated logs and singles out log at "depth 1" as uniquely positioned.

#### `ComplexIdentities.lean` — Trig from F at imaginary argument

Define `F_C(z) := exp(z) + log(z)` over ℂ. For `x > 0`:
- `F_C_imag_re`: `Re(F_C(i·x)) = cos(x) + log(x)`.
- `F_C_imag_im`: `Im(F_C(i·x)) = sin(x) + π/2`.
- `cos_eq_F_C_re`, `sin_eq_F_C_im`: trig extraction from `F_C`.

#### `MellinHaar.lean` — Differential structure / Haar bridge

- `hasDerivAt_F`: `F'(x) = exp(x) + x⁻¹`. The `x⁻¹` summand is the density of the multiplicative Haar measure `dx/x` on `(ℝ⁺, ·)`; the `exp(x)` summand is the F-tangent that survives dilation differences.
- `F_euler_eq`: `x · F'(x) − 1 = x · exp(x)` (Euler-operator form).
- `hasDerivAt_F_deriv`: `F''(x) = exp(x) − 1/x²`.

The differential characterization makes explicit why the `log(k)` constants pervade every identity in this section: they are line integrals of the multiplicative-Haar density `1/x` from `1` to `k`.

#### `MultiVar.lean` — Multi-variable extension

`F₂(x, y) := exp(x) + exp(y) + log(x) + log(y) = F(x) + F(y)`. Joint and independent dilations give analogous identities with `2·log(k)` and `log(a) + log(b)` respectively.

#### `VonMangoldt.lean` — Number-theoretic structure

The dilation cocycle `c(k) := log(k)`, restricted to natural-number dilations, decomposes via the von Mangoldt function `Λ`:
- `cocycle_eq_logSum_vonMangoldt`: `c(n) = log(n) = ∑_{d ∣ n} Λ(d)` (the standard `log = Λ ∗ 1` Dirichlet identity).
- `cocycle_at_prime_power`: `c(p^j) = j · log(p)` for prime `p`.
- `F_dilate_sub_prime_power`, `F_dilate_sub_divisor_sum`: F-identities expressed in `Λ` form.

The cocycle of the F-identity is the same `log = Λ ∗ 1` decomposition that drives the explicit formula in analytic number theory. The theorems here are structural — they identify the vocabulary, not the content.

#### `Characterization.lean` — Converse universal mechanism

The universal mechanism in `IdentitiesZoo` proves `F = g + α·log + const` is *sufficient* for the dilation cancellation. This file proves it is also *necessary*:
- `pure_log_characterization`: if `h(k·x) − h(x) = α·log(k)` for all positive `x, k`, then `h(x) = α·log(x) + h(1)`. A three-line proof via `k := x⁻¹`.
- `dilation_decomposition`: if `F(k·x) − F(x) − α·log(k) = g(k·x) − g(x)` for all positive `x, k`, then `F = g + α·log + (F(1) − g(1))`.
- `F_unique_up_to_constant`: specialization — the canonical `F = exp + log` is uniquely characterized (up to additive constant) by its dilation-cancellation behavior.

Combined with `F_dilate_sub` (existence direction), this gives a complete characterization of F by dilation differences.

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
