/-
  # The F-rational grammar: univariate Sheffer completeness

  The paper's main result is that the binary operator `eml(x, y) = exp(x) − log(y)`
  plus the constant `1` is Sheffer-complete for elementary functions.

  This file shows a different completeness result: the *univariate* function
  `F(x) = exp(x) + log(x)` plus rational arithmetic suffices to recover
  `exp` (and hence everything else through composition).

  ## The F-rational grammar

  An `FRationalExpr` is an expression tree built from:
    • leaves        : `x` (variable), constants from ℝ
    • unary nodes   : `F` (apply the anti-diagonal)
    • binary nodes  : `+, −, *, /`

  We compute the tree size and prove that the explicit "F-formula" tree

      ((F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2)) − 1

  has size 21 and evaluates to `exp(x)` for `x ≠ 0`.

  ## Significance

  This refines the EML Sheffer-completeness result: a *univariate* function
  is enough, at the cost of moving the work into the "background structure"
  (rational arithmetic + access to the constants `log 2, log 3`). Both
  results are completeness statements; they differ in what counts as a
  primitive operation.
-/
import EML.Identities

open Real

namespace EML.Identities.FRational

/-- The F-rational expression grammar. Leaves are `var` (the input `x`) or
    a constant from `ℝ`; unary nodes apply `F`; binary nodes are the
    four arithmetic operations. -/
inductive FExpr where
  | var      : FExpr
  | const    : ℝ → FExpr
  | F        : FExpr → FExpr
  | add      : FExpr → FExpr → FExpr
  | sub      : FExpr → FExpr → FExpr
  | mul      : FExpr → FExpr → FExpr
  | div      : FExpr → FExpr → FExpr

/-- Tree size: every node (leaf, unary, binary) counts as 1.
    `size(F(e))   = 1 + size(e)`,
    `size(e₁ ∘ e₂) = 1 + size(e₁) + size(e₂)` for binary `∘`. -/
def FExpr.size : FExpr → Nat
  | .var       => 1
  | .const _   => 1
  | .F e       => 1 + e.size
  | .add e₁ e₂ => 1 + e₁.size + e₂.size
  | .sub e₁ e₂ => 1 + e₁.size + e₂.size
  | .mul e₁ e₂ => 1 + e₁.size + e₂.size
  | .div e₁ e₂ => 1 + e₁.size + e₂.size

/-- Evaluator: `eval e x` evaluates the expression at the point `x`.
    The `FExpr.F` constructor maps to the real-valued anti-diagonal `F`
    from `Identities.lean`. -/
noncomputable def FExpr.eval : FExpr → ℝ → ℝ
  | .var,        x => x
  | .const c,    _ => c
  | .F e,        x => EML.Identities.F (e.eval x)
  | .add e₁ e₂,  x => e₁.eval x + e₂.eval x
  | .sub e₁ e₂,  x => e₁.eval x - e₂.eval x
  | .mul e₁ e₂,  x => e₁.eval x * e₂.eval x
  | .div e₁ e₂,  x => e₁.eval x / e₂.eval x

/-! ## The K=21 F-formula tree

We construct the F-formula tree node-by-node and verify both its size
(=21) and its evaluation (= `exp`). -/

/-- `3 * x` as a subtree: `mul (const 3) var`. Size = 3. -/
def threeX : FExpr := .mul (.const 3) .var

/-- `2 * x` as a subtree: `mul (const 2) var`. Size = 3. -/
def twoX : FExpr := .mul (.const 2) .var

/-- `F(3x)` = `F (mul (const 3) var)`. Size = 4. -/
def F_threeX : FExpr := .F threeX

/-- `F(2x)`. Size = 4. -/
def F_twoX : FExpr := .F twoX

/-- `F(x)`. Size = 2. -/
def F_x : FExpr := .F .var

/-- Numerator `(F(3x) - F(x)) - log 3`. Size = 9. -/
noncomputable def numerator : FExpr :=
  .sub (.sub F_threeX F_x) (.const (Real.log 3))

/-- Denominator `(F(2x) - F(x)) - log 2`. Size = 9. -/
noncomputable def denominator : FExpr :=
  .sub (.sub F_twoX F_x) (.const (Real.log 2))

/-- The full F-formula tree: `(numerator / denominator) - 1`. Size = 21. -/
noncomputable def fFormulaTree : FExpr :=
  .sub (.div numerator denominator) (.const 1)

/-- **Verifies the K count.** `fFormulaTree.size = 21`. -/
theorem fFormulaTree_size : fFormulaTree.size = 21 := by
  -- Unfold all definitions and compute by `decide`.
  unfold fFormulaTree numerator denominator F_threeX F_twoX F_x threeX twoX
  simp [FExpr.size]

/-- **Verifies the K=21 tree computes exp(x)** for `x ≠ 0`.

    Reduces to `exp_eq_F_quotient` from `Identities.lean` after unfolding
    the tree's evaluator. -/
theorem fFormulaTree_eval (x : ℝ) (hx : x ≠ 0) :
    fFormulaTree.eval x = Real.exp x := by
  unfold fFormulaTree numerator denominator F_threeX F_twoX F_x threeX twoX
  simp only [FExpr.eval]
  -- Goal reduces to:
  -- ((F (3*x) - F x - log 3) / (F (2*x) - F x - log 2)) - 1 = exp x
  -- which is the symmetric form of exp_eq_F_quotient.
  exact (exp_eq_F_quotient hx).symm

/-! ## A simpler F-construction: `e` via `F(1)`

    Independently of the K=21 result for `exp x`, there is a tiny
    F-expression for the constant `e = exp 1`:

      e = F(1) - log(1)·… = F(1)  (since log 1 = 0)

    so `e = F(1)`. -/

/-- The K=2 tree `F(1)` evaluates to `e`. -/
def eConst : FExpr := .F (.const 1)

theorem eConst_size : eConst.size = 2 := by
  unfold eConst; simp [FExpr.size]

theorem eConst_eval (x : ℝ) : eConst.eval x = Real.exp 1 := by
  unfold eConst
  simp only [FExpr.eval, F, Real.log_one, add_zero]

/-! ## Arity-reduction theorems: univariate F vs. binary EML

The paper's main result (`exp_eq_eml` in `Basic.lean`) says

    exp(x) = eml(x, 1)         (binary operator, arity 2)

is a 3-node `{1, eml}`-tree, the minimal pure-EML expression for `exp`.

The theorem `fFormulaTree_eval` above says

    exp(x) = ((F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2)) − 1     (univariate F, arity 1)

is a 21-node F-rational expression. Both routes recover `exp` — and hence,
through `exp_eq_F_quotient` plus the rest of the EML formalization, every
elementary function.

The trade-off is precise: dropping from arity 2 to arity 1 raises the
minimal-known node count from 3 to 21 (a 7× cost), in exchange for needing
*only a univariate function* as the non-arithmetic primitive. -/

/-- **Arity-1 completeness for exp.** There exists an `FExpr` (built from
    var, real constants, the univariate `F`, and rational arithmetic only)
    whose evaluation equals `exp` on `ℝ \ {0}`. -/
theorem exp_from_univariate :
    ∃ e : FExpr, ∀ x : ℝ, x ≠ 0 → e.eval x = Real.exp x :=
  ⟨fFormulaTree, fFormulaTree_eval⟩

/-- **K-cost of arity reduction.** The minimal-known F-rational expression
    for `exp` is the 21-node `fFormulaTree`. The minimal pure-EML expression
    for `exp` is 3 nodes (`exp_eq_eml`). -/
theorem exp_K_in_F_rational_at_most_21 :
    ∃ e : FExpr, e.size = 21 ∧ ∀ x : ℝ, x ≠ 0 → e.eval x = Real.exp x :=
  ⟨fFormulaTree, fFormulaTree_size, fFormulaTree_eval⟩

end EML.Identities.FRational
