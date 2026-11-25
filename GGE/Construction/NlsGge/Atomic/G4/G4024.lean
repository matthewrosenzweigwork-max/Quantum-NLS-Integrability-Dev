import Mathlib
import NlsGge.GK38.StdRootBranchesScalar

                                                                                                                                                                                      
                                                                                                                                     
                                                                                                                
                                                                                                                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open scoped ENNReal

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The infinity-normalized root off [-1,1]; the value at zero merely fills
one chosen boundary sheet. Its squared identity holds everywhere. -/
def slitRoot (ρ : ℂ) : ℂ :=
  if ρ = 0 then Complex.I else stdRoot38 0 4 ρ

/-- Principal, bounded-imaginary-part representative of the elementary primitive.
The exponent, not this additive representative, is globally single-valued. -/
def slitPrimitive (ρ : ℂ) : ℂ := Complex.log (-ρ - slitRoot ρ)

theorem G4024 (ρ : ℂ) (hρ : ρ ∉ segment ℝ (-1 : ℂ) 1)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
  slitRoot ρ ^ 2 = ρ ^ 2 - 1 ∧ -ρ - slitRoot ρ ≠ 0 ∧
  Complex.exp ((s : ℂ) * slitPrimitive ρ) = -ρ - (s : ℂ) * slitRoot ρ := by
  have hsq : slitRoot ρ ^ 2 = ρ ^ 2 - 1 := by
    by_cases h0 : ρ = 0
    · simp [slitRoot, h0]
    · have h : (0 : ℂ) - ρ ≠ 0 := by simpa using h0
      have := stdRoot_sq_of_ne38 (τ := 0) (g2 := 4) (z := ρ) h
      simp only [slitRoot, if_neg h0]
      rw [this]; ring
  have hne : -ρ - slitRoot ρ ≠ 0 := by
    intro h
    have hr : slitRoot ρ = -ρ := by linear_combination -h
    rw [hr] at hsq
    have : (1 : ℂ) = 0 := by linear_combination hsq
    exact one_ne_zero this
  refine ⟨hsq, hne, ?_⟩
  have hlog : Complex.exp (slitPrimitive ρ) = -ρ - slitRoot ρ := Complex.exp_log hne
  rcases hs with rfl | rfl
  · simpa using hlog
  · have hinv : (-ρ - slitRoot ρ)⁻¹ = -ρ + slitRoot ρ := by
      apply inv_eq_of_mul_eq_one_right
      linear_combination (-1 : ℂ) * hsq
    have : Complex.exp (((-1 : ℤ) : ℂ) * slitPrimitive ρ) = (Complex.exp (slitPrimitive ρ))⁻¹ := by
      rw [Int.cast_neg, Int.cast_one, neg_one_mul, Complex.exp_neg]
    rw [this, hlog, hinv]
    push_cast
    ring


end
end NlsGge.GKDefinitionDesign
