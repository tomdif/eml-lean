/-
  # Trig from F at imaginary argument

  The complex anti-diagonal `F_C(z) := exp(z) + log(z)` evaluated at `z = i·x`
  encodes the real trig functions in its real and imaginary parts.

  For `x > 0`:
    Re(F_C(i·x)) = cos(x) + log(x)        (since |i·x| = x, so log|i·x| = log x)
    Im(F_C(i·x)) = sin(x) + π/2           (since arg(i·x) = π/2)

  Rearranging:
    cos(x) = Re(F_C(i·x)) − log(x)
    sin(x) = Im(F_C(i·x)) − π/2

  This closes the real/complex loop: trigonometric functions are extractable
  from the complex anti-diagonal F, completing the picture begun in `Identities.lean`
  for exp/log and `IdentitiesFamily.lean` for sinh/cosh.
-/
import EML.Identities
import EML.Complex

open Real Complex

namespace EML.Identities.Complex

/-- The complex anti-diagonal: `F_C(z) = exp(z) + log(z)`. -/
noncomputable def F_C (z : ℂ) : ℂ := Complex.exp z + Complex.log z

/-! ## Real and imaginary parts of F_C at the imaginary axis -/

/-- `Re(F_C(i·x)) = cos(x) + log(x)` for `x > 0`. -/
theorem F_C_imag_re (x : ℝ) (hx : 0 < x) :
    (F_C ((x : ℂ) * Complex.I)).re = Real.cos x + Real.log x := by
  simp only [F_C, Complex.add_re]
  -- exp(x*I).re = cos x via Euler's formula
  have h_exp : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
    rw [Complex.exp_ofReal_mul_I]
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  -- log(x*I).re = log ‖x*I‖ = log x for x > 0
  have h_log : (Complex.log ((x : ℂ) * Complex.I)).re = Real.log x := by
    rw [Complex.log_re]
    have : ‖((x : ℂ) * Complex.I)‖ = x := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
          abs_of_pos hx]
    rw [this]
  rw [h_exp, h_log]

/-- `Im(F_C(i·x)) = sin(x) + π/2` for `x > 0`. -/
theorem F_C_imag_im (x : ℝ) (hx : 0 < x) :
    (F_C ((x : ℂ) * Complex.I)).im = Real.sin x + Real.pi / 2 := by
  simp only [F_C, Complex.add_im]
  -- exp(x*I).im = sin x via Euler's formula
  have h_exp : (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := by
    rw [Complex.exp_ofReal_mul_I]
    simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  -- log(x*I).im = arg(x*I) = π/2 for x > 0 (since x*I has re=0, im=x>0)
  have h_log : (Complex.log ((x : ℂ) * Complex.I)).im = Real.pi / 2 := by
    rw [Complex.log_im]
    -- arg(x*I) = π/2 iff (x*I).re = 0 and 0 < (x*I).im
    rw [Complex.arg_eq_pi_div_two_iff]
    refine ⟨?_, ?_⟩
    · simp
    · simp [hx]
  rw [h_exp, h_log]

/-! ## Trig extraction from F_C -/

/-- **Cosine from F_C.** For `x > 0`,

      cos(x) = Re(F_C(i·x)) − log(x). -/
theorem cos_eq_F_C_re (x : ℝ) (hx : 0 < x) :
    Real.cos x = (F_C ((x : ℂ) * Complex.I)).re - Real.log x := by
  rw [F_C_imag_re x hx]; ring

/-- **Sine from F_C.** For `x > 0`,

      sin(x) = Im(F_C(i·x)) − π/2. -/
theorem sin_eq_F_C_im (x : ℝ) (hx : 0 < x) :
    Real.sin x = (F_C ((x : ℂ) * Complex.I)).im - Real.pi / 2 := by
  rw [F_C_imag_im x hx]; ring

end EML.Identities.Complex
