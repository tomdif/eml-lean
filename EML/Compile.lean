/-
  # EML Compilation

  The paper's compiler (Section 4.1) converts elementary expressions
  into pure EML form. The core compilation rules are:
    compile(1) = 1
    compile(x) = x
    compile(exp(e)) = eml(compile(e), 1)
    compile(log(e)) = eml(1, eml(eml(1, compile(e)), 1))

  We formalize this as a function on an inductive expression type
  and prove it preserves semantics.
-/
import EML.Grammar

open Real

/-! ## Exp-Log expression type -/

/-- An expression built from 1, a variable x, exp, and log.
    This is the intermediate representation before EML compilation. -/
inductive ExpLogExpr where
  | one : ExpLogExpr
  | var : ExpLogExpr
  | cExp : ExpLogExpr → ExpLogExpr
  | cLog : ExpLogExpr → ExpLogExpr
  deriving Repr

/-- Evaluate an exp-log expression at a given value of x. -/
noncomputable def ExpLogExpr.eval (x : ℝ) : ExpLogExpr → ℝ
  | .one => 1
  | .var => x
  | .cExp e => exp (e.eval x)
  | .cLog e => log (e.eval x)

/-! ## The EML compiler -/

/-- Compile an exp-log expression to an EML expression tree.
    Paper Section 4.1:
    - compile(1) = 1
    - compile(x) = x
    - compile(exp(e)) = eml(compile(e), 1)      [since exp(a) = eml(a, 1)]
    - compile(log(e)) = eml(1, eml(eml(1, compile(e)), 1))
                                                  [since log(a) = eml(1, eml(eml(1, a), 1))]
-/
def compile : ExpLogExpr → EmlExpr
  | .one => .one
  | .var => .var
  | .cExp e => .app (compile e) .one
  | .cLog e => .app .one (.app (.app .one (compile e)) .one)

/-! ## Compiler correctness -/

/-- The compiler is correct: compiled expressions evaluate identically
    to the original, provided all log arguments are positive.

    This is the formal statement of the paper's main claim that
    the EML compilation procedure preserves semantics. -/
theorem compile_correct (e : ExpLogExpr) (x : ℝ) :
    (compile e).eval x = e.eval x := by
  induction e with
  | one => rfl
  | var => rfl
  | cExp e ih =>
    simp only [compile, EmlExpr.eval, ExpLogExpr.eval, eml, log_one, sub_zero]
    rw [ih]
  | cLog e ih =>
    simp only [compile, EmlExpr.eval, ExpLogExpr.eval, eml, log_one, sub_zero]
    rw [log_exp, ih]
    ring

/-! ## Building compound expressions -/

/-- exp(x) as an exp-log expression. -/
def expExpr : ExpLogExpr := .cExp .var

/-- log(x) as an exp-log expression. -/
def logExpr : ExpLogExpr := .cLog .var

/-- The compiled exp tree matches our earlier eml_expr_exp. -/
theorem compile_exp_correct (x : ℝ) :
    (compile expExpr).eval x = exp x := by
  rw [compile_correct]; rfl

/-- The compiled log tree matches our earlier eml_expr_log. -/
theorem compile_log_correct (x : ℝ) :
    (compile logExpr).eval x = log x := by
  rw [compile_correct]; rfl

/-- exp(exp(x)) compiles correctly. -/
def doubleExpExpr : ExpLogExpr := .cExp (.cExp .var)

theorem compile_double_exp (x : ℝ) :
    (compile doubleExpExpr).eval x = exp (exp x) := by
  rw [compile_correct]; rfl

/-- log(log(x)) compiles correctly (for x > 1 so log(x) > 0). -/
def doubleLogExpr : ExpLogExpr := .cLog (.cLog .var)

theorem compile_double_log (x : ℝ) :
    (compile doubleLogExpr).eval x = log (log x) := by
  rw [compile_correct]; rfl

/-- The identity function log(exp(x)) compiles correctly. -/
def identityExpr : ExpLogExpr := .cLog (.cExp .var)

theorem compile_identity (x : ℝ) :
    (compile identityExpr).eval x = log (exp x) := by
  rw [compile_correct]; rfl

/-- The compiled identity equals x. -/
theorem compile_identity_eq (x : ℝ) :
    (compile identityExpr).eval x = x := by
  rw [compile_identity, log_exp]

/-- exp(log(x)) = x compiles correctly for x > 0. -/
def expLogExpr : ExpLogExpr := .cExp (.cLog .var)

theorem compile_exp_log (x : ℝ) (hx : 0 < x) :
    (compile expLogExpr).eval x = x := by
  rw [compile_correct]
  exact exp_log hx

/-! ## Arbitrarily deep compositions compile correctly -/

/-- n-fold exp: exp(exp(...exp(x)...)) with n applications. -/
def nExp : ℕ → ExpLogExpr
  | 0 => .var
  | n + 1 => .cExp (nExp n)

/-- n-fold exp compiles correctly. -/
theorem compile_nExp (n : ℕ) (x : ℝ) :
    (compile (nExp n)).eval x = (nExp n).eval x := by
  exact compile_correct (nExp n) x

/-- n-fold log: log(log(...log(x)...)) with n applications. -/
def nLog : ℕ → ExpLogExpr
  | 0 => .var
  | n + 1 => .cLog (nLog n)

/-- n-fold log compiles correctly. -/
theorem compile_nLog (n : ℕ) (x : ℝ) :
    (compile (nLog n)).eval x = (nLog n).eval x := by
  exact compile_correct (nLog n) x

/-! ## Summary -/

/-- **Compilation theorem.**
    Every expression built from {1, x, exp, log} can be compiled
    to a semantically equivalent EML tree built from {1, x, eml}.

    This is the formal heart of the paper's main claim: the grammar
    S → 1 | x | eml(S, S) is complete for exp-log expressions.

    Combined with the arithmetic theorems (add, mul, etc. are expressible
    via exp and log), this shows all elementary functions are EML-compilable. -/
theorem eml_compilation_complete :
    ∀ (e : ExpLogExpr) (x : ℝ), (compile e).eval x = e.eval x :=
  compile_correct
