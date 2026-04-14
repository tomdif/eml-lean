/-
  # Constructive EML trees for -x, 1/x, x-y, x*y

  These are the pure EML trees found by exhaustive computer search
  (reproducing the paper's Table 4 / Figure 2). Each tree uses only
  the grammar S → 1 | x | y | eml(S, S).
-/
import EML.Grammar

open Real

/-! ## Subtraction: x - y (K = 11, 5 eml nodes)

  Tree: eml(eml(1, eml(eml(1, x), 1)), eml(y, 1))
  Chain: eml(log(x), exp(y)) = x - y
-/

theorem eml_sub {x : ℝ} (hx : 0 < x) (y : ℝ) :
    eml (log x) (exp y) = x - y := by
  simp [eml, exp_log hx, log_exp]

noncomputable def eml_expr_sub : EmlExpr₂ :=
  .app (.app .one (.app (.app .one .varX) .one))
       (.app .varY .one)

theorem eml_expr_sub_eval {x : ℝ} (hx : 0 < x) (y : ℝ) :
    eml_expr_sub.eval x y = x - y := by
  simp only [eml_expr_sub, EmlExpr₂.eval]
  -- goal: eml 1 (eml (eml 1 x) 1) evaluates, then eml with eml(y,1)
  -- Unfold to exp/log and simplify all log(exp(...)) pairs
  simp only [eml, log_one, sub_zero, log_exp]
  -- Now: exp(exp 1 - (exp 1 - log x)) - y = x - y
  -- Simplify exp 1 - (exp 1 - log x) = log x
  have : exp 1 - (exp 1 - log x) = log x := by ring
  rw [this, exp_log hx]

/-! ## Negation: -x (K = 17, 8 eml nodes)

  Tree: eml(eml(1, eml(eml(1, eml(1, eml(x, 1))), 1)),
            eml(eml(1, 1), 1))

  Chain:
  1. eml(x,1) = exp(x)
  2. eml(1,exp(x)) = e - x       (using log(exp(x)) = x)
  3. eml(1, e-x) = e - ln(e-x)
  4. eml(e - ln(e-x), 1) = exp(e - ln(e-x))
  5. eml(1, exp(e-ln(e-x))) = e - (e - ln(e-x)) = ln(e-x)
  6. eml(eml(1,1), 1) = exp(e)
  7. eml(ln(e-x), exp(e)) = (e-x) - e = -x
-/

noncomputable def eml_expr_neg : EmlExpr :=
  .app (.app .one (.app (.app .one
    (.app .one (.app .var .one))) .one))
       (.app (.app .one .one) .one)

theorem eml_expr_neg_eval {x : ℝ} (_hx : 0 < x) (hxe : x < exp 1) :
    eml_expr_neg.eval x = -x := by
  have hex : 0 < exp 1 - x := by linarith
  simp only [eml_expr_neg, EmlExpr.eval, eml, log_one, sub_zero, log_exp]
  have h1 : exp 1 - (exp 1 - log (exp 1 - x)) = log (exp 1 - x) := by
    ring
  rw [h1, exp_log hex]
  ring

/-! ## Reciprocal: 1/x (K = 17, 8 eml nodes)

  Tree: eml(eml(eml(1, eml(eml(1, eml(1, x)), 1)),
                eml(eml(1, 1), 1)),
            1)

  Chain:
  1. eml(1, x) = e - ln(x)
  2. eml(1, e-ln(x)) = e - ln(e - ln(x))
  3. eml(e-ln(e-ln(x)), 1) = exp(e - ln(e-ln(x)))
  4. eml(1, exp(...)) = e - (e - ln(e-ln(x))) = ln(e - ln(x))
  5. eml(eml(1,1), 1) = exp(e)
  6. eml(ln(e-ln(x)), exp(e)) = (e-ln(x)) - e = -ln(x)
  7. eml(-ln(x), 1) = exp(-ln(x)) = 1/x
-/

noncomputable def eml_expr_inv : EmlExpr :=
  .app (.app (.app .one (.app (.app .one (.app .one .var)) .one))
             (.app (.app .one .one) .one))
       .one

theorem eml_expr_inv_eval {x : ℝ} (hx : 0 < x)
    (hlx : log x < exp 1) :
    eml_expr_inv.eval x = x⁻¹ := by
  have helx : 0 < exp 1 - log x := by linarith
  simp only [eml_expr_inv, EmlExpr.eval, eml, log_one, sub_zero,
             log_exp]
  have h1 : exp 1 - (exp 1 - log (exp 1 - log x)) =
      log (exp 1 - log x) := by ring
  rw [h1, exp_log helx]
  rw [show exp 1 - log x - exp 1 = -log x from by ring]
  rw [exp_neg, exp_log hx]

/-! ## Multiplication: x * y (K = 17, 8 eml nodes)

  Tree: eml(eml(1, eml(eml(eml(1, eml(eml(1, eml(1, x)), 1)),
                             y), 1)),
            1)

  Chain:
  1-4. Same as 1/x → ln(e - ln(x))
  5. eml(ln(e-ln(x)), y) = (e-ln(x)) - ln(y) = e - ln(xy)
  6. eml(e-ln(xy), 1) = exp(e - ln(xy))
  7. eml(1, exp(e-ln(xy))) = e - (e - ln(xy)) = ln(xy)
  8. eml(ln(xy), 1) = exp(ln(xy)) = xy
-/

noncomputable def eml_expr_mul : EmlExpr₂ :=
  .app (.app .one
    (.app (.app (.app .one
      (.app (.app .one (.app .one .varX)) .one))
      .varY) .one))
    .one

theorem eml_expr_mul_eval {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlx : log x < exp 1) :
    eml_expr_mul.eval x y = x * y := by
  have helx : 0 < exp 1 - log x := by linarith
  have hxy : 0 < x * y := mul_pos hx hy
  simp only [eml_expr_mul, EmlExpr₂.eval, eml, log_one, sub_zero,
             log_exp]
  have h1 : exp 1 - (exp 1 - log (exp 1 - log x)) =
      log (exp 1 - log x) := by ring
  rw [h1, exp_log helx]
  have h2 : exp 1 - log x - log y =
      exp 1 - (log x + log y) := by ring
  rw [h2, ← log_mul hx.ne' hy.ne']
  have h3 : exp 1 - (exp 1 - log (x * y)) = log (x * y) := by ring
  rw [h3, exp_log hxy]
