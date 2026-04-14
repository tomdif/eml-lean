# EML: All Elementary Functions from a Single Binary Operator

A Lean 4 + Mathlib formalization of the main results from:

> **Andrzej Odrzywołek**, *"All elementary functions from a single binary operator"*
> [arXiv:2603.21852](https://arxiv.org/abs/2603.21852) [cs.SC], April 2026.

The paper shows that a single binary operator

```
eml(x, y) = exp(x) - ln(y)
```

together with the constant **1**, generates the entire standard repertoire of a scientific calculator: arithmetic, exponentiation, logarithms, trigonometric and hyperbolic functions, their inverses, and fundamental constants like *e*, *pi*, and *i*.

This is the continuous analogue of the NAND gate in digital logic.

## What is proved

**130 definitions and theorems. 0 sorry. 10 Lean files.**

### Core identities (`Basic.lean`)
- `exp(x) = eml(x, 1)`
- `e = eml(1, 1)`
- `ln(z) = eml(1, eml(eml(1, z), 1))` for z > 0 (paper equation 5)
- `0 = eml(1, eml(eml(1, 1), 1))` (pure EML tree, K = 7)
- `-1` and `2` derivable via the exp-log chain

### All 36 calculator primitives (`Arithmetic.lean`, `Transcendental.lean`, `Complex.lean`)

Every primitive from the paper's Table 1 is shown to reduce to `{1, eml}`:

| Category | Primitives proved |
|---|---|
| **Constants** | 1, e, 0, -1, 2, pi, i |
| **Functions** | exp, ln, inv, half, minus, sqrt, sqr, sigma, sin, cos, tan, arcsin, arccos, arctan, sinh, cosh, tanh, arsinh, arcosh, artanh |
| **Operations** | +, -, x, /, x^y, log_b, avg, hypot |

Trigonometric functions and constants pi and i are proved over the complex numbers using Euler's formula and a complex EML operator `ceml(x,y) = exp(x) - log(y)`.

### EML grammar and expression trees (`Grammar.lean`)
- Inductive types `EmlTree`, `EmlExpr`, `EmlExpr2` formalizing the context-free grammar `S -> 1 | x | eml(S, S)`
- Verified tree evaluations matching Figure 2: exp (K=3), ln (K=7), identity (K=9), zero (K=7), e (K=3)
- Leaf count (= RPN code length K from Table 4)

### Compiler correctness (`Compile.lean`)
- An `ExpLogExpr` type for expressions built from `{1, x, exp, log}`
- A `compile` function converting exp-log expressions to EML trees
- **`compile_correct`**: the compiler preserves semantics for all exp-log expressions
- Verified for exp, log, double-exp, double-log, identity, and arbitrary n-fold compositions

### Exp-log pair (`ExpLog.lean`)
- Paper equation (1): `x * y = exp(ln x + ln y)` and `x + y = ln(exp x * exp y)`
- Subtraction, division, negation, reciprocal, integers via exp-log

### Operator variants (`Variants.lean`)
- EDL operator: `edl(x, y) = exp(x) / ln(y)` (paper equation 4b)
- Negated EML: `neml(x, y) = ln(x) - exp(y)` (paper equation 4c)
- Relationships between variants

### Master formula (`MasterFormula.lean`)
- Level-1 and level-2 parametrized master formulas (paper equation 6)
- Recovering `exp(x)`, `e`, and `exp(exp(x))` from specific parameter choices
- Parameter count formula: `5 * 2^n - 6`

### The suc/pre/inv identity (`SucPreInv.lean`)
- `suc(inv(pre(inv(suc(inv(x)))))) = -x` (paper Section 2, p.6)

## What is not proved

- **Minimal EML trees** for `-x` (K=15), `1/x` (K=15), `x*y` (K=17): these were found by the paper's exhaustive computer search over millions of trees. The compiler theorem proves *existence* of EML representations for these functions, but not *minimality*.
- **Table 4 optimality**: proving a K value is minimal requires enumerating all smaller trees.
- **EDL completeness**: the paper states EDL also generates all primitives, but provides no explicit constructions.
- **Symbolic regression convergence** (Section 4.3): an empirical result from training experiments.

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/) and [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

```bash
lake update
lake build
```

## License

MIT
