/-
  # Iterated log breaks the anti-diagonal mechanism

  The companion negative result to `IdentitiesZoo`: while the anti-diagonal
  cancellation `F_g(k·x) − F_g(x) − log(k) = g(k·x) − g(x)` works for ANY `g`
  paired with a single `log(x)`, it **fails** if we replace `log(x)` by
  `log(log(x))`.

  This singles out log as uniquely positioned at "depth 1" in the mechanism:
  no iterated log substitutes.

  ## Concrete witness

  At `x = e` and `k = e` (so `k·x = e²`), the would-be cancellation

      F_loglog(k·x) − F_loglog(x) − log(k) = exp(k·x) − exp(x)

  with `F_loglog(x) := exp(x) + log(log(x))` fails: the residual is
  `log 2 − 1`, which is negative (since `log 2 < log e = 1`).
-/
import EML.Identities

open Real

namespace EML.Identities.LogLogBreaks

/-- `F_loglog(x) := exp(x) + log(log(x))`. Same shape as the working
    anti-diagonal `F` from `Identities.lean`, but with an iterated log. -/
noncomputable def F_loglog (x : ℝ) : ℝ := exp x + log (log x)

/-- **Negative result.** The function `F_loglog` does NOT satisfy the
    anti-diagonal cancellation that `F = exp + log` enjoys. Concretely,
    at `x = e` and `k·x = e²`, the would-be identity

        F_loglog(e²) − F_loglog(e) − log(e) = exp(e²) − exp(e)

    is FALSE. The residual is `log 2 − 1 < 0`.

    Proof: simplifies to `log 2 = 1`, which contradicts `log 2 < log e = 1`
    (since `2 < e` by `add_one_lt_exp` at `x = 1`). -/
theorem F_loglog_breaks :
    F_loglog (exp 1 * exp 1) - F_loglog (exp 1) - log (exp 1) ≠
      exp (exp 1 * exp 1) - exp (exp 1) := by
  intro h
  -- Bookkeeping: exp 1 * exp 1 = exp 2.
  have hee : exp 1 * exp 1 = exp 2 := by rw [← exp_add]; norm_num
  -- Unfold F_loglog and extract the iterated-log residual.
  have hkey : log (log (exp 1 * exp 1)) - log (log (exp 1)) - log (exp 1) = 0 := by
    simp only [F_loglog] at h; linarith
  rw [hee] at hkey
  simp only [Real.log_exp, Real.log_one] at hkey
  -- hkey : log 2 - 0 - 1 = 0, i.e. log 2 = 1.
  -- Contradiction: log 2 < 1.
  have h_two_lt_e : (2 : ℝ) < exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero)
    linarith
  have h_log_two_lt_one : Real.log 2 < 1 :=
    calc Real.log 2 < Real.log (Real.exp 1) :=
            Real.log_lt_log (by norm_num) h_two_lt_e
      _ = 1 := Real.log_exp 1
  linarith

/-- Restatement: the iterated-log residual `log(log(k·x)) − log(log(x)) − log(k)`
    is genuinely x-dependent (it does not vanish identically the way
    `log(k·x) − log(x) − log(k) = 0` does). -/
theorem loglog_residual_nonzero_at_e :
    Real.log (Real.log (Real.exp 1 * Real.exp 1))
      - Real.log (Real.log (Real.exp 1)) - Real.log (Real.exp 1) ≠ 0 := by
  intro h
  have hee : exp 1 * exp 1 = exp 2 := by rw [← exp_add]; norm_num
  rw [hee] at h
  simp only [Real.log_exp, Real.log_one] at h
  have h_two_lt_e : (2 : ℝ) < exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero)
    linarith
  have h_log_two_lt_one : Real.log 2 < 1 :=
    calc Real.log 2 < Real.log (Real.exp 1) :=
            Real.log_lt_log (by norm_num) h_two_lt_e
      _ = 1 := Real.log_exp 1
  linarith

end EML.Identities.LogLogBreaks
