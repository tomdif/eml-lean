/-
  # The dilation cocycle and the von Mangoldt function

  This file connects the dilation cocycle of the anti-diagonal `F`-identity
  (see `EML.Identities` and `EML.IdentitiesFamily`) to the von Mangoldt
  function `Λ` of analytic number theory.

  ## The mechanism

  Recall (from `EML.Identities`, `F_dilate_sub`) that for `x ≠ 0` and `k > 0`,

      F(k·x) − F(x) − log(k) = exp(k·x) − exp(x).

  The constant `log(k)` is the *dilation cocycle*: it is the term that must
  be subtracted from the F-difference in order to cancel the additive
  `log(k·x) − log(x) = log(k)` shift contributed by the `log` half of
  `F = exp + log`. We denote it

      c(k) := log(k).

  This cocycle is multiplicative-additive: `c(a·b) = c(a) + c(b)`. When
  restricted to natural-number dilations `k ∈ ℕ, k ≥ 1`, it admits a
  canonical decomposition into the von Mangoldt function `Λ`:

      log(n) = ∑_{d | n} Λ(d)        (Mathlib: `vonMangoldt_sum`)

  This identity is the bridge between the additive cocycle `c(k) = log k`
  on the multiplicative group `ℝ_{>0}` and the prime-power data carried by
  `Λ`. The `Λ` decomposition is the content of the explicit formula in
  analytic number theory.

  ## Main results

  * `cocycle_eq_logSum_vonMangoldt` — for natural `n ≥ 1`,
    `c(n) = log(n) = ∑_{d | n} Λ(d)`.

  * `cocycle_at_prime_power` — for prime `p` and `j ≥ 1`,
    `c(p^j) = log(p^j) = j · log(p) = j · Λ(p)`.

  * `cocycle_eq_jay_vonMangoldt_at_prime_power` — restated form,
    using the Mathlib convention `Λ(p^j) = log(p)`:
    `log(p^j) = j · Λ(p^j)`.

  * `F_dilate_sub_prime_power` — the structural theorem packaged with
    the F-identity: for `x ≠ 0`, prime `p`, and `j ≥ 1`,
    `F(p^j · x) − F(x) − j · Λ(p) = exp(p^j · x) − exp(x)`.

  ## Significance

  Every modern approach to the Riemann hypothesis (Bombieri-Lagarias, Li,
  Connes-Consani-Moscovici) routes through the explicit formula, which
  expresses sums over zeros of `ζ` in terms of sums of `Λ(n)` over integers.
  This file provides a precise, machine-checked statement that the dilation
  cocycle of the F-identity *is* the same `log n = ∑ Λ d` decomposition that
  drives the explicit formula, evaluated at prime-power integer dilations.

  The theorems here are *purely structural* — they do not by themselves
  imply or approach RH. They establish vocabulary: the F-identity's cocycle
  is the standard Mertens-Mangoldt object, not a new one.
-/
import EML.IdentitiesFamily
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Real
open scoped ArithmeticFunction

namespace EML.Identities

/-! ## The dilation cocycle as a function of `ℝ_{>0}` -/

/-- The **dilation cocycle** of the F-identity: `c(k) = log(k)`. This is the
    constant that must be subtracted from `F(k·x) − F(x)` to obtain the
    pure exponential difference `exp(k·x) − exp(x)` (cf. `F_dilate_sub`). -/
noncomputable def cocycle (k : ℝ) : ℝ := log k

/-- Evaluating the cocycle reproduces the dilation-cancellation identity. -/
theorem F_dilate_sub_cocycle {x k : ℝ} (hx : x ≠ 0) (hk : 0 < k) :
    F (k * x) - F x - cocycle k = exp (k * x) - exp x := by
  unfold cocycle
  exact F_dilate_sub hx hk

/-- The cocycle is additive under multiplication: `c(a·b) = c(a) + c(b)` for
    positive arguments. This is the 1-cocycle property in additive form. -/
theorem cocycle_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    cocycle (a * b) = cocycle a + cocycle b := by
  unfold cocycle
  exact Real.log_mul ha.ne' hb.ne'

/-- Trivial value: `c(1) = 0`. -/
@[simp] theorem cocycle_one : cocycle 1 = 0 := by
  unfold cocycle
  exact Real.log_one

/-! ## Restriction to natural-number dilations and the Λ-decomposition -/

/-- **Structural theorem (cocycle ↔ Λ decomposition).** For every natural
    number `n ≥ 1`, the dilation cocycle evaluated at `n` equals the sum of
    `Λ(d)` over divisors `d` of `n`:

      c(n) = log(n) = ∑_{d | n} Λ(d).

    This is the standard identity `log n = ∑_{d | n} Λ d` (Mertens, 1874),
    obtained as `Λ ∗ 1 = log` in the Dirichlet-convolution algebra and
    proved in Mathlib as `ArithmeticFunction.vonMangoldt_sum`. We restate
    it here in the form of the F-identity's dilation cocycle to make the
    bridge explicit.

    The hypothesis `n ≥ 1` is needed because the empty sum at `n = 0` is
    `0`, while `log 0 = 0` in the Mathlib convention; the equality holds
    at `n = 0` trivially but the cocycle interpretation is meaningful only
    for positive `n`. -/
theorem cocycle_eq_logSum_vonMangoldt (n : ℕ) (_hn : 1 ≤ n) :
    cocycle (n : ℝ) = ∑ d ∈ n.divisors, Λ d := by
  unfold cocycle
  exact (ArithmeticFunction.vonMangoldt_sum (n := n)).symm

/-- The same statement, but at `n = 0` for completeness (both sides equal `0`). -/
theorem cocycle_eq_logSum_vonMangoldt_zero :
    cocycle ((0 : ℕ) : ℝ) = ∑ d ∈ (0 : ℕ).divisors, Λ d := by
  unfold cocycle
  simp [Nat.divisors_zero]

/-! ## Prime-power dilations: where `Λ` is supported -/

/-- The cocycle at a natural-number power: `c(n^j) = j · log(n)` for `n ≥ 1`.
    This is the multiplicative-to-additive transport via `Real.log_pow`. -/
theorem cocycle_pow (n : ℕ) (j : ℕ) :
    cocycle ((n ^ j : ℕ) : ℝ) = j * cocycle (n : ℝ) := by
  unfold cocycle
  rw [Nat.cast_pow]
  exact Real.log_pow n j

/-- **Cocycle at a prime power, raw form.** For prime `p` and `j ≥ 1`,

      c(p^j) = log(p^j) = j · log(p).

    The factor `j` is the exponent; `log p` is what `Λ` returns on the
    prime power (Mathlib convention: `Λ(p^j) = log p`, a single factor). -/
theorem cocycle_at_prime_power {p : ℕ} (_hp : p.Prime) {j : ℕ} (_hj : 1 ≤ j) :
    cocycle ((p ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log p := by
  rw [cocycle_pow]
  rfl

/-- **Cocycle at a prime power, in `Λ` form (Mathlib convention).** For prime
    `p` and `j ≥ 1`,

      log(p^j) = j · Λ(p^j).

    The Mathlib convention is `Λ(p^j) = log p` — a single factor of `log p`,
    independent of `j`. The number-theoretic identity `log(p^j) = j · log p`
    therefore reads `log(p^j) = j · Λ(p^j)` in this convention.

    This is the cleanest statement of the structural connection. The cocycle
    of the F-identity at integer prime-power dilations is exactly `j` copies
    of the von Mangoldt value `Λ(p^j)`. -/
theorem cocycle_eq_jay_vonMangoldt_at_prime_power
    {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : 1 ≤ j) :
    cocycle ((p ^ j : ℕ) : ℝ) = (j : ℝ) * Λ (p ^ j) := by
  have hLam : Λ (p ^ j) = Real.log p := by
    have hjne : j ≠ 0 := Nat.one_le_iff_ne_zero.mp hj
    rw [ArithmeticFunction.vonMangoldt_apply_pow hjne,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [cocycle_at_prime_power hp hj, hLam]

/-- **Equivalent form via the divisor sum.** For prime `p` and `j ≥ 1`,
    the cocycle decomposes term-by-term over the `j+1` divisors `1, p, …, p^j`:

      log(p^j) = ∑_{i = 0}^{j} Λ(p^i) = 0 + log p + log p + … + log p  (j copies).

    This makes the structural content fully explicit: the cocycle is the
    sum of `Λ` over divisors, and only the prime-power divisors `p^1, …, p^j`
    contribute (each contributing `log p`), giving `j · log p` total. -/
theorem cocycle_at_prime_power_divisor_sum
    {p : ℕ} (hp : p.Prime) {j : ℕ} (_hj : 1 ≤ j) :
    cocycle ((p ^ j : ℕ) : ℝ) = ∑ d ∈ (p ^ j).divisors, Λ d := by
  have hpos : 1 ≤ p ^ j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  exact cocycle_eq_logSum_vonMangoldt (p ^ j) hpos

/-! ## The F-identity at prime-power dilations -/

/-- **Structural theorem packaged with the F-identity.** For `x ≠ 0`,
    prime `p`, and integer `j ≥ 1`,

      F(p^j · x) − F(x) − j · Λ(p) = exp(p^j · x) − exp(x).

    The dilation-cancellation term `log(p^j)` in `F_dilate_sub` is rewritten
    using the von Mangoldt structure: at a prime-power dilation, the cocycle
    is `j` copies of `Λ(p) = log p`. -/
theorem F_dilate_sub_prime_power
    {x : ℝ} (hx : x ≠ 0) {p : ℕ} (hp : p.Prime) {j : ℕ} (_hj : 1 ≤ j) :
    F ((p ^ j : ℕ) * x) - F x - (j : ℝ) * Λ p
      = exp ((p ^ j : ℕ) * x) - exp x := by
  have hp_pos : (0 : ℝ) < (p ^ j : ℕ) := by
    have : 0 < p ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)
    exact_mod_cast this
  have h := F_dilate_sub hx hp_pos
  -- h : F (p^j * x) - F x - log (p^j) = exp (p^j * x) - exp x
  have hlog : Real.log ((p ^ j : ℕ) : ℝ) = (j : ℝ) * Λ p := by
    rw [Nat.cast_pow, Real.log_pow, ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hlog] at h
  exact h

/-- **Same statement, expanded form using the divisor sum.** This is the
    most explicit "explicit-formula-flavored" statement: the cocycle is
    expanded fully as a sum of `Λ` over divisors of the dilation. -/
theorem F_dilate_sub_divisor_sum
    {x : ℝ} (hx : x ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    F ((n : ℝ) * x) - F x - (∑ d ∈ n.divisors, Λ d)
      = exp ((n : ℝ) * x) - exp x := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h := F_dilate_sub hx hn_pos
  -- h : F (n * x) - F x - log n = exp (n * x) - exp x
  rw [← ArithmeticFunction.vonMangoldt_sum (n := n)] at h
  exact h

/-! ## Summary

  The four results above (`cocycle_eq_logSum_vonMangoldt`,
  `cocycle_at_prime_power`, `cocycle_eq_jay_vonMangoldt_at_prime_power`,
  `F_dilate_sub_prime_power`, `F_dilate_sub_divisor_sum`) together
  constitute the *von Mangoldt structural theorem* for the F-identity:

  * The cocycle `c(k) = log k` of the F-identity, restricted to natural
    `k`, is exactly the divisor-sum of `Λ`.
  * At prime powers `p^j`, the cocycle is `j` copies of the von Mangoldt
    value, exhibiting the `j · log p` explicit-formula structure.
  * The F-identity itself can therefore be rewritten with `Λ` in place of
    the cocycle, making the bridge to the explicit formula manifest.

  No new mathematics is introduced; the work is to spell out the precise
  identification of the F-identity's dilation cocycle with the standard
  `log = Λ ∗ 1` decomposition of analytic number theory.
-/

end EML.Identities
