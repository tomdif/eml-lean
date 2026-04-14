# EML: Lean 4 Formalization

A Lean 4 + Mathlib formalization of the results in:

> **Andrzej Odrzywołek** (Institute of Theoretical Physics, Jagiellonian University),
> *"All elementary functions from a single binary operator"*,
> [arXiv:2603.21852](https://arxiv.org/abs/2603.21852) [cs.SC], April 2026.

**All mathematical results in this repository are due to Odrzywołek.** This project is solely a machine-checked formalization of his work in the Lean 4 theorem prover. The discovery of the EML operator, the exhaustive search methodology, the completeness proof strategy, and all identities originate from the paper above.

## The result

Odrzywołek discovered that a single binary operator

```
eml(x, y) = exp(x) - ln(y)
```

together with the constant **1**, generates the entire standard repertoire of a scientific calculator: arithmetic, exponentiation, logarithms, trigonometric and hyperbolic functions, their inverses, and fundamental constants like *e*, *π*, and *i*. This is the continuous analogue of the NAND gate in digital logic.

## What is formalized

**11 Lean files. 140+ definitions and theorems. 0 sorry.**

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

### Compiler correctness (`Compile.lean`)
- An `ExpLogExpr` type for expressions built from `{1, x, exp, log}`
- A `compile` function converting exp-log expressions to EML trees
- **`compile_correct`**: the compiler preserves semantics for all exp-log expressions

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

The mathematical content formalized here is entirely the work of **Andrzej Odrzywołek**. Please cite his paper:

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
