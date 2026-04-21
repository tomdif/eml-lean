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

/-! ## Corollary 1: expressions without cLog are unconditional

For any `e : ExpLogExpr` containing no `cLog` nodes, `BranchOk` is
trivially satisfied at every `x : ℂ`. No branch hypothesis is needed. -/

/-- Predicate: the expression contains no `cLog` nodes. -/
def NoCLog : ExpLogExpr → Prop
  | .one => True
  | .var => True
  | .cExp e => NoCLog e
  | .cLog _ => False

theorem branchOk_of_noCLog {x : ℂ} : ∀ {e : ExpLogExpr}, NoCLog e → BranchOk x e
  | .one, _ => trivial
  | .var, _ => trivial
  | .cExp e, h => branchOk_of_noCLog (e := e) h
  | .cLog _, h => (h : False).elim

/-- **Unconditional on ℂ for cLog-free expressions.** -/
theorem compile_correctC_noCLog {e : ExpLogExpr} (h : NoCLog e) (x : ℂ) :
    (compile e).evalC x = e.evalC x :=
  compile_correctC e x (branchOk_of_noCLog h)

/-! ## Corollary 2: positive-real evaluation domain

When `x : ℝ` is positive and every `cLog` node's sub-expression has a
positive real evaluation, `BranchOk` is automatically satisfied and the
complex identity follows. The branch exponent `exp 1 − log v` has
imaginary part `0` when `v` is positive real, and `0 ∈ (−π, π]`. -/

/-- Predicate: at a real input `x`, every `cLog` sub-expression has a
    positive real evaluation. -/
def SafeAtReal (x : ℝ) : ExpLogExpr → Prop
  | .one => True
  | .var => True
  | .cExp e => SafeAtReal x e
  | .cLog e => SafeAtReal x e ∧ 0 < e.eval x

/-- Under `SafeAtReal`, the complex evaluation at `↑x` equals the real
    evaluation coerced into ℂ. -/
theorem evalC_eq_ofReal_eval (x : ℝ) :
    ∀ (e : ExpLogExpr), SafeAtReal x e → e.evalC (↑x) = ((e.eval x : ℝ) : ℂ)
  | .one, _ => by simp [ExpLogExpr.evalC, ExpLogExpr.eval]
  | .var, _ => by simp [ExpLogExpr.evalC, ExpLogExpr.eval]
  | .cExp e, h => by
      simp only [ExpLogExpr.evalC, ExpLogExpr.eval]
      rw [evalC_eq_ofReal_eval x e h, ← Complex.ofReal_exp]
  | .cLog e, h => by
      obtain ⟨h_sub, h_pos⟩ := h
      simp only [ExpLogExpr.evalC, ExpLogExpr.eval]
      rw [evalC_eq_ofReal_eval x e h_sub]
      exact (Complex.ofReal_log h_pos.le).symm

/-- When `v : ℝ` is positive, `Im(exp 1 − log (↑v)) = 0`. -/
private theorem im_exp_one_sub_log_ofReal_eq_zero {v : ℝ} (hv : 0 < v) :
    (Complex.exp 1 - Complex.log (↑v : ℂ)).im = 0 := by
  have h_exp_one : Complex.exp 1 = ((Real.exp 1 : ℝ) : ℂ) := by
    have : (1 : ℂ) = ((1 : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_exp]
  have h_log_real : (Complex.log (↑v : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hv.le]
    exact Complex.ofReal_im _
  rw [Complex.sub_im, h_exp_one, Complex.ofReal_im, h_log_real]
  ring

/-- `BranchOk` is automatic under `SafeAtReal` at a real input. -/
theorem branchOk_of_safeAtReal (x : ℝ) :
    ∀ (e : ExpLogExpr), SafeAtReal x e → BranchOk (↑x) e
  | .one, _ => trivial
  | .var, _ => trivial
  | .cExp e, h => branchOk_of_safeAtReal x e h
  | .cLog e, h => by
      obtain ⟨h_sub, h_pos⟩ := h
      refine ⟨branchOk_of_safeAtReal x e h_sub, ?_, ?_⟩
      · rw [evalC_eq_ofReal_eval x e h_sub]
        rw [im_exp_one_sub_log_ofReal_eq_zero h_pos]
        exact neg_lt_zero.mpr Real.pi_pos
      · rw [evalC_eq_ofReal_eval x e h_sub]
        rw [im_exp_one_sub_log_ofReal_eq_zero h_pos]
        exact Real.pi_pos.le

/-- **Unconditional on ℂ for SafeAtReal expressions at positive reals.** -/
theorem compile_correctC_safeAtReal (x : ℝ) (e : ExpLogExpr) (h : SafeAtReal x e) :
    (compile e).evalC (↑x) = e.evalC (↑x) :=
  compile_correctC e (↑x) (branchOk_of_safeAtReal x e h)

/-! ## Summary.

`(compile e).evalC x = e.evalC x` is NOT unconditionally true over ℂ —
counterexample at `x = −1` for `e = cLog .var`. Three usable forms:

  1. `compile_correctC`: over ℂ, conditional on `BranchOk x e`.
  2. `compile_correctC_noCLog`: unconditional on ℂ when `e` has no `cLog`.
  3. `compile_correctC_safeAtReal`: unconditional at positive-real inputs
     when every sub-expression of `e` evaluates positively (real domain).

For real inputs and real evaluation, `Compile.lean`'s `compile_correct`
remains unconditional (via Mathlib's `Real.log = 0` convention on
non-positives). -/
example : True := trivial
