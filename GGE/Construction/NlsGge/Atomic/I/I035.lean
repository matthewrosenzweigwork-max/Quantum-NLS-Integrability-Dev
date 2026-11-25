import Mathlib
import NlsGge.Birkhoff.S05FreeEnergy38b
import NlsGge.Measure.CountableGaussian
import NlsGge.Measure.FourierGaussian

                                                                                                                   
                                                                                                                          
                                                                                                                         
                                                                                                                          
                                                                                   

set_option autoImplicit false
open NlsGge.Measure ProbabilityTheory

namespace NlsGge.Atomic.I035

theorem gaussian_quadraticEnergy_infinite
    (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) :
    iIndepFun (fun (k : ℕ) (z : ℤ → ℂ) =>
      fullWeightRate c (k+1 : ℕ) * ‖z (k+1 : ℕ)‖^2)
      (fullWeightSequenceGaussian c) ∧
    (∀ k : ℕ, (fullWeightSequenceGaussian c).map
      (fun z : ℤ → ℂ => fullWeightRate c (k+1 : ℕ) * ‖z (k+1 : ℕ)‖^2) =
        expMeasure 1) ∧
    (∀ᵐ z ∂fullWeightSequenceGaussian c,
      (∑' n : ℤ, ENNReal.ofReal (fullWeightRate c n * ‖z n‖^2)) = ⊤) := by
  have hq : ∀ n : ℤ, 0 < fullWeightRate c n :=
    fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  refine ⟨?_, ?_, tsum_fullWeight_sqNorm_eq_top_ae38 lower upper c hlower hbound hupper⟩
  · exact (iIndep_rateSqNorm_exp38 (fullWeightRate c) hq).1.precomp
      (g := fun k : ℕ => ((k+1 : ℕ) : ℤ)) (by intro a b hab; simpa using hab)
  · intro k
    exact (iIndep_rateSqNorm_exp38 (fullWeightRate c) hq).2 ((k+1 : ℕ) : ℤ)

end NlsGge.Atomic.I035
