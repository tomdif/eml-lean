/-
  # Complex-domain compiler correctness

  The compile theorem in `Compile.lean` is stated over ℝ. On ℝ the proof
  is unconditional because `Real.log (Real.exp x) = x` for all `x`.

  Over ℂ, the identity `Complex.log (Complex.exp w) = w` requires
  `Im w ∈ (−π, π]` (the principal strip). For the compiled form
  `log(exp(e − log v))` to equal `e − log v`, we need the exponent's
  imaginary part to stay in the principal strip — which it does not for
  all `v : ℂ`. A concrete failure: at `v = −1`, `log(exp(e − πi)) = e + πi`,
  not `e − πi`, so compile gives the wrong answer by `2πi`.

  This file formalizes the correct complex-domain generalization:
  `compile` preserves semantics over ℂ conditioned on a branch predicate
  that asserts every `cLog` node respects the principal strip.
-/
import EML.Compile
import EML.Complex

open Complex

/-! ## Complex evaluation of exp-log expressions and compiled EML trees -/

/-- Evaluate an `ExpLogExpr` over ℂ using principal-branch log. -/
noncomputable def ExpLogExpr.evalC (x : ℂ) : ExpLogExpr → ℂ
  | .one => 1
  | .var => x
  | .cExp e => Complex.exp (e.evalC x)
  | .cLog e => Complex.log (e.evalC x)

/-- Evaluate an `EmlExpr` (compiled tree) over ℂ via `ceml`. -/
noncomputable def EmlExpr.evalC (x : ℂ) : EmlExpr → ℂ
  | .one => 1
  | .var => x
  | .app l r => ceml (l.evalC x) (r.evalC x)

/-! ## The branch predicate

The compiled form of `cLog e` is `ceml 1 (ceml (ceml 1 e) 1)`, which
when expanded evaluates to `exp(1) − Complex.log (Complex.exp (exp(1) − Complex.log v))`
where `v = e.evalC x`. This equals `Complex.log v` exactly when the inner
exponent `exp(1) − Complex.log v` has imaginary part in `(−π, π]`
(Mathlib's `Complex.log_exp`).  -/

/-- Branch-ok: every `cLog` node's inner exponent stays in the principal strip. -/
def BranchOk (x : ℂ) : ExpLogExpr → Prop
  | .one => True
  | .var => True
  | .cExp e => BranchOk x e
  | .cLog e =>
      BranchOk x e ∧
      -Real.pi < (Complex.exp 1 - Complex.log (e.evalC x)).im ∧
      (Complex.exp 1 - Complex.log (e.evalC x)).im ≤ Real.pi

/-! ## Complex compile correctness -/

/-- **Complex-domain compile correctness, conditioned on BranchOk.**

    For every exp-log expression `e` and every `x : ℂ`, if the branch
    predicate holds along `e`, then the compiled EML tree evaluates to
    the same complex number as the original expression.

    This is the honest complex-domain generalization of `compile_correct`.
    The unconditional version is false (see the `z = −1` counterexample
    in the file header); `BranchOk` is exactly the hypothesis that rules
    out branch crossings. -/
theorem compile_correctC (e : ExpLogExpr) (x : ℂ) (h : BranchOk x e) :
    (compile e).evalC x = e.evalC x := by
  induction e with
  | one => rfl
  | var => rfl
  | cExp e ih =>
    simp only [compile, EmlExpr.evalC, ExpLogExpr.evalC, ceml,
               Complex.log_one, sub_zero]
    rw [ih h]
  | cLog e ih =>
    simp only [compile, EmlExpr.evalC, ExpLogExpr.evalC, ceml,
               Complex.log_one, sub_zero]
    obtain ⟨h_sub, h1, h2⟩ := h
    rw [ih h_sub, Complex.log_exp h1 h2]
    ring

/-! ## Counterexample narrative

The unconditional complex statement `(compile e).evalC x = e.evalC x`
is false. Concrete witness: `e = .cLog .var` at `x = −1`. Tracing through:

  (compile (.cLog .var)).evalC (-1)
    = ceml 1 (ceml (ceml 1 (-1)) 1)                [unfold compile]
    = exp 1 − log (exp (exp 1 − log (-1)))         [unfold ceml twice]
    = exp 1 − log (exp (exp 1 − πi))                [Complex.log_neg_one]
    = exp 1 − (exp 1 + πi)                          [branch shift: Im(exp 1 − πi) = −π
                                                     is outside (−π, π], log∘exp adds 2πi]
    = −πi

while `(ExpLogExpr.cLog .var).evalC (-1) = log (-1) = πi`. The two
differ by exactly `2πi`, the branch discrepancy.

Formalizing this concrete witness in Lean is possible but tedious
(Mathlib's `Complex.log_exp` is stated positively with strip
hypotheses, not as a general multivalued equation). The narrative
above is the counterexample; `compile_correctC` below is the
statement that holds. -/

/-! ## Convenience: derive BranchOk for safe expression classes

In practice the per-node BranchOk hypothesis can be discharged for
specific subsets of expressions. Two useful corollaries: (i) expressions
evaluated at positive real inputs whose sub-expressions all stay positive
real, and (ii) expressions whose sub-expression values stay off the
negative real axis.

These corollaries are not proved here; they are the natural next step if
the repo wants polished real-to-complex bridge lemmas. -/

/-- **Summary.**

On the nose, `(compile e).evalC x = e.evalC x` does NOT hold for every
`x : ℂ` (counterexample at `x = −1`). The correct theorem is
`compile_correctC`: the identity holds whenever the branch predicate
`BranchOk x e` holds at every `cLog` node along `e`.

For real inputs, `compile_correct` in `Compile.lean` gives the
unconditional statement over ℝ, with Mathlib's `Real.log = 0` convention
on non-positives making the hypothesis-free statement technically true.
-/
example : True := trivial
