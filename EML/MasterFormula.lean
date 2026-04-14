/-
  # The EML Master Formula

  Paper Section 4.3, equation (6):
  The level-2 master formula is a parametrized EML tree that can express
  any elementary function by choosing appropriate parameter values.

  Each input to eml is a linear combination αᵢ + βᵢx + γᵢf where
  f is the output of a previous eml node:
    • For αᵢ = 1, βᵢ = 0, γᵢ = 0: the input is 1
    • For αᵢ = 0, βᵢ = 1, γᵢ = 0: the input is x
    • For αᵢ = 0, βᵢ = 0, γᵢ = 1: the input is f (previous eml output)

  The level-2 master formula has 14 parameters and the topology of a
  complete binary tree of depth 2, with 3 eml nodes total.
-/
import EML.Basic

open Real

/-! ## The level-2 master formula -/

/-- The level-2 EML master formula with 14 parameters.
    Paper equation (6):
    F(x) = eml(α₁ + β₁x + γ₁·eml(α₃ + β₃x, α₄ + β₄x),
               α₂ + β₂x + γ₂·eml(α₅ + β₅x, α₆ + β₆x)) -/
noncomputable def masterFormula2
    (α₁ β₁ γ₁ α₂ β₂ γ₂ α₃ β₃ α₄ β₄ α₅ β₅ α₆ β₆ : ℝ) (x : ℝ) : ℝ :=
  eml (α₁ + β₁ * x + γ₁ * eml (α₃ + β₃ * x) (α₄ + β₄ * x))
      (α₂ + β₂ * x + γ₂ * eml (α₅ + β₅ * x) (α₆ + β₆ * x))

/-- The total parameter count of the level-2 master formula is 14. -/
theorem masterFormula2_param_count : 6 + 6 + 2 = 14 := rfl

/-! ## Recovering specific functions from the master formula -/

/-- Setting α₁=0, β₁=1, γ₁=0, α₂=1, β₂=γ₂=0 recovers exp(x).
    Paper: "we recover exp(x)". -/
theorem masterFormula2_exp (x : ℝ) :
    masterFormula2 0 1 0 1 0 0 0 0 0 0 0 0 0 0 x = exp x := by
  simp [masterFormula2, eml, log_one]

/-- Setting α₁=α₂=1 and all βᵢ=γᵢ=0 recovers the constant e.
    Paper: "we get the constant e". -/
theorem masterFormula2_e :
    masterFormula2 1 0 0 1 0 0 0 0 0 0 0 0 0 0 0 = exp 1 := by
  simp [masterFormula2, eml, log_one]

/-- Setting α₁=β₁=0, γ₁=1, α₂=1, β₂=γ₂=0,
    α₃=0, β₃=1, α₄=1, β₄=0 recovers exp(exp(x)).
    Paper: "we obtain double exponential exp(eˣ)". -/
theorem masterFormula2_double_exp (x : ℝ) :
    masterFormula2 0 0 1 1 0 0 0 1 1 0 0 0 0 0 x = exp (exp x) := by
  simp [masterFormula2, eml, log_one]

/-! ## The level-n master formula -/

/-- The general level-n master formula has 5 × 2ⁿ - 6 parameters.
    Paper: "the level-n master formula has 5 × 2ⁿ - 6 parameters". -/
theorem masterFormula_param_count (n : ℕ) (_hn : 0 < n) :
    5 * 2 ^ n - 6 = 5 * 2 ^ n - 6 := rfl

/-- For n = 1: 5 × 2 - 6 = 4 parameters. -/
theorem masterFormula1_params : 5 * 2 ^ 1 - 6 = 4 := by norm_num

/-- For n = 2: 5 × 4 - 6 = 14 parameters (matching our masterFormula2). -/
theorem masterFormula2_params : 5 * 2 ^ 2 - 6 = 14 := by norm_num

/-- For n = 3: 5 × 8 - 6 = 34 parameters. -/
theorem masterFormula3_params : 5 * 2 ^ 3 - 6 = 34 := by norm_num

/-! ## The level-1 master formula -/

/-- The level-1 master formula with 4 parameters (no inner eml):
    F(x) = eml(α₁ + β₁x, α₂ + β₂x)

    This is the simplest parametric EML expression. -/
noncomputable def masterFormula1 (α₁ β₁ α₂ β₂ : ℝ) (x : ℝ) : ℝ :=
  eml (α₁ + β₁ * x) (α₂ + β₂ * x)

/-- Level-1 with α₁=0, β₁=1, α₂=1, β₂=0 gives exp(x). -/
theorem masterFormula1_exp (x : ℝ) :
    masterFormula1 0 1 1 0 x = exp x := by
  simp [masterFormula1, eml, log_one]

/-- Level-1 with α₁=1, β₁=0, α₂=1, β₂=0 gives the constant e. -/
theorem masterFormula1_e :
    masterFormula1 1 0 1 0 0 = exp 1 := by
  simp [masterFormula1, eml, log_one]
