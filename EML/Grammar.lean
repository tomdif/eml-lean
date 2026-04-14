/-
  # EML Grammar and Expression Trees

  The paper establishes that every EML expression is a binary tree
  of identical nodes, yielding the context-free grammar:
    S → 1 | eml(S, S)

  For functions of one variable x, the grammar extends to:
    S → 1 | x | eml(S, S)

  This file formalizes the grammar as an inductive type and proves
  that specific expression trees evaluate to known functions,
  matching the trees shown in Figure 2 of the paper.
-/
import EML.Basic

open Real

/-! ## EML expression trees -/

/-- An EML expression tree (constants only, no variables).
    Grammar: S → 1 | eml(S, S) -/
inductive EmlTree where
  | one : EmlTree
  | app : EmlTree → EmlTree → EmlTree
  deriving Repr

/-- Evaluate a constant EML tree to a real number. -/
noncomputable def EmlTree.eval : EmlTree → ℝ
  | .one => 1
  | .app l r => eml (l.eval) (r.eval)

/-- An EML expression tree with one variable.
    Grammar: S → 1 | x | eml(S, S) -/
inductive EmlExpr where
  | one : EmlExpr
  | var : EmlExpr
  | app : EmlExpr → EmlExpr → EmlExpr
  deriving Repr

/-- Evaluate a unary EML expression at a given value of x. -/
noncomputable def EmlExpr.eval (x : ℝ) : EmlExpr → ℝ
  | .one => 1
  | .var => x
  | .app l r => eml (l.eval x) (r.eval x)

/-- An EML expression tree with two variables.
    Grammar: S → 1 | x | y | eml(S, S) -/
inductive EmlExpr₂ where
  | one : EmlExpr₂
  | varX : EmlExpr₂
  | varY : EmlExpr₂
  | app : EmlExpr₂ → EmlExpr₂ → EmlExpr₂
  deriving Repr

/-- Evaluate a binary EML expression at given values of x and y. -/
noncomputable def EmlExpr₂.eval (x y : ℝ) : EmlExpr₂ → ℝ
  | .one => 1
  | .varX => x
  | .varY => y
  | .app l r => eml (l.eval x y) (r.eval x y)

/-! ## Tree size (leaf count = Kolmogorov complexity K from Table 4) -/

/-- Leaf count of a constant tree (= K from the paper's Table 4). -/
def EmlTree.leafCount : EmlTree → ℕ
  | .one => 1
  | .app l r => l.leafCount + r.leafCount + 1

/-- Leaf count of a unary expression tree. -/
def EmlExpr.leafCount : EmlExpr → ℕ
  | .one => 1
  | .var => 1
  | .app l r => l.leafCount + r.leafCount + 1

/-! ## Verified constant trees -/

/-- The tree for constant 1 is just the leaf: K = 1. -/
theorem EmlTree.eval_one : EmlTree.one.eval = 1 := rfl

/-- The tree for e = eml(1, 1): K = 3. -/
noncomputable def eml_tree_e : EmlTree := .app .one .one

theorem eml_tree_e_eval : eml_tree_e.eval = exp 1 := by
  simp [eml_tree_e, EmlTree.eval, eml, log_one, sub_zero]

theorem eml_tree_e_leafCount : eml_tree_e.leafCount = 3 := rfl

/-- The tree for 0 = eml(1, eml(eml(1,1), 1)): K = 7.
    Paper Table 4: constant 0 has K = 7. -/
noncomputable def eml_tree_zero : EmlTree :=
  .app .one (.app (.app .one .one) .one)

theorem eml_tree_zero_eval : eml_tree_zero.eval = 0 := by
  simp [eml_tree_zero, EmlTree.eval, eml, log_one, sub_zero, log_exp]

theorem eml_tree_zero_leafCount : eml_tree_zero.leafCount = 7 := rfl

/-! ## Verified function trees from Figure 2 -/

/-- The tree for exp(x) = eml(x, 1): K = 3.
    Figure 2, simplest function. -/
noncomputable def eml_expr_exp : EmlExpr := .app .var .one

theorem eml_expr_exp_eval (x : ℝ) : eml_expr_exp.eval x = exp x := by
  simp only [eml_expr_exp, EmlExpr.eval, eml, log_one, sub_zero]

/-- The tree for ln(x) = eml(1, eml(eml(1, x), 1)): K = 7.
    Figure 2, top tree.
    Paper equation (5). -/
noncomputable def eml_expr_log : EmlExpr :=
  .app .one (.app (.app .one .var) .one)

theorem eml_expr_log_eval (x : ℝ) :
    eml_expr_log.eval x = eml 1 (eml (eml 1 x) 1) := by
  simp [eml_expr_log, EmlExpr.eval]

theorem eml_expr_log_eq_log (x : ℝ) (hx : 0 < x) :
    eml_expr_log.eval x = log x := by
  rw [eml_expr_log_eval]
  exact (log_eq_eml x hx).symm

/-- The tree for identity x = eml(1, eml(eml(1, eml(x, 1)), 1)): K = 9.
    Figure 2, second tree.
    This is ln(exp(x)) = x. -/
noncomputable def eml_expr_id : EmlExpr :=
  .app .one (.app (.app .one (.app .var .one)) .one)

theorem eml_expr_id_eval (x : ℝ) : eml_expr_id.eval x = x := by
  simp [eml_expr_id, EmlExpr.eval, eml, log_one, sub_zero, log_exp]

theorem eml_expr_id_leafCount : eml_expr_id.leafCount = 9 := rfl

/-! ## Number of trees -/

/-- A constant EML tree with n internal (eml) nodes has exactly
    n + 1 leaves (all valued 1). The number of such trees
    is the Catalan number C_n.

    We don't prove the Catalan counting here (it would require
    a bijection with Dyck paths or similar), but we verify the
    leaf count formula. -/
theorem EmlTree.leafCount_app (l r : EmlTree) :
    (EmlTree.app l r).leafCount = l.leafCount + r.leafCount + 1 := rfl
