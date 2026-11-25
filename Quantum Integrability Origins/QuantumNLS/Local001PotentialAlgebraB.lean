import QuantumNLS.Local001SourceB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable {L : ℝ}

theorem lopPt_free_add_potential (κ : ℝ) (w : ℂ) (d g : E2) :
    lopPt κ w d g = (2 * Complex.I) • Jm d + potentialPt κ w g := rfl

#print axioms lopPt_free_add_potential

theorem potentialPt_add (κ : ℝ) (w : ℂ) (g h : E2) :
    potentialPt κ w (g + h) = potentialPt κ w g + potentialPt κ w h := by
  ext j
  fin_cases j <;> simp [potentialPt, LocalSpectral.vec2, PiLp.add_apply] <;> ring


#print axioms potentialPt_add

theorem potentialPt_smul (κ : ℝ) (w c : ℂ) (g : E2) :
    potentialPt κ w (c • g) = c • potentialPt κ w g := by
  ext j
  fin_cases j <;> simp [potentialPt, LocalSpectral.vec2, PiLp.smul_apply] <;> ring

#print axioms potentialPt_smul

theorem continuous_potentialPt (κ : ℝ) :
    Continuous (fun p : ℂ × E2 => potentialPt κ p.1 p.2) := by
  fun_prop [potentialPt, LocalSpectral.vec2]


#print axioms continuous_potentialPt

def potentialResolventFn (κ : ℝ) (u : ScalarInterval L)
    (g : VectorInterval L) (x : ℝ) : E2 := potentialPt κ (u x) (g x)


#print axioms potentialResolventFn


end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
