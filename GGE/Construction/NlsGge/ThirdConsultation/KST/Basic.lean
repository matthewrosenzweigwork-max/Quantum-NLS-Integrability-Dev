import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.KST.KST018

                                                                               
                                                                                                                 
                                                                                                                          
                                                         
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open NlsGge.Atomic.DM046

namespace NlsGge.ThirdConsultation.KST

def AdmissibleWeight (ω : ℤ → ℝ) : Prop :=
  (∀ k, 1 ≤ ω k) ∧ (∀ k, ω (-k) = ω k) ∧
  (∀ j k : ℤ, j.natAbs ≤ k.natAbs → ω j ≤ ω k)

/-- RHS of Corollary 4.1 after the constant-weight reduction. -/
def sourceCorollary41RHS (w A : ℤ → ℝ) (N : ℕ) : ℝ :=
  4 * ((scalarTailEnergy w A N).toReal +
    (scalarEnergy w A).toReal / Real.sqrt (N : ℝ))

def SecondaryWeight (v : ℤ → ℝ) : Prop :=
  AdmissibleWeight v ∧ SubmultiplicativeWeight v

end NlsGge.ThirdConsultation.KST
