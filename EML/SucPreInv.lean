/-
  # The suc/pre/inv negation identity

  From paper Section 2 (p.6):
  "Given only the three operations: suc(x) = x + 1 (successor),
   pre(x) = x - 1 (predecessor), and inv(x) = 1/x (reciprocal/inverse),
   let us compute negation, i.e., -x. The non-obvious solution is:

     suc(inv(pre(inv(suc(inv(x)))))) = 1/(1/(1/x + 1) - 1) + 1 = -x."

  This illustrates the kind of nested expressions encountered in the
  EML search at depth 5-9.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

open Real

/-! ## Definitions -/

/-- Successor: suc(x) = x + 1 -/
def suc (x : ℝ) : ℝ := x + 1

/-- Predecessor: pre(x) = x - 1 -/
def pre (x : ℝ) : ℝ := x - 1

/-- Reciprocal/inverse: rinv(x) = 1/x -/
noncomputable def rinv (x : ℝ) : ℝ := 1 / x

/-! ## The negation identity -/

/-- `suc(inv(pre(inv(suc(inv(x)))))) = -x` for x ≠ 0 and x ≠ -1.

    Step by step:
    1. inv(x) = 1/x
    2. suc(1/x) = 1/x + 1 = (1 + x)/x
    3. inv((1 + x)/x) = x/(1 + x)
    4. pre(x/(1 + x)) = x/(1 + x) - 1 = -1/(1 + x)
    5. inv(-1/(1 + x)) = -(1 + x)
    6. suc(-(1 + x)) = -(1 + x) + 1 = -x
-/
theorem suc_inv_pre_inv_suc_inv_eq_neg (x : ℝ) (hx : x ≠ 0) (hx1 : 1 + x ≠ 0) :
    suc (rinv (pre (rinv (suc (rinv x))))) = -x := by
  unfold suc pre rinv
  have h1 : x * (1 + x) ≠ 0 := mul_ne_zero hx hx1
  have h2 : 1 / x + 1 = (1 + x) / x := by field_simp
  rw [h2]
  have h3 : 1 / ((1 + x) / x) = x / (1 + x) := by field_simp
  rw [h3]
  have h4 : x / (1 + x) - 1 = -1 / (1 + x) := by field_simp; ring
  rw [h4]
  have h5 : 1 / (-1 / (1 + x)) = -(1 + x) := by field_simp
  rw [h5]
  ring
