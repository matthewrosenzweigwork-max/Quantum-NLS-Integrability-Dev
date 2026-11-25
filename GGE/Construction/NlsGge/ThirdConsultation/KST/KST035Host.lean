import Mathlib
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST034Host

                                                                                                                          
                                                                                                         
                                                                                                                      
                                                                                                                       
                                                                                                       
                                                                                                                
                                                               
                                                                                                                 
                                                                     
set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

def rawEnergy (ω : ℤ → ℝ) (r : RawPair) : ℝ≥0∞ :=
  ∑' m : ℤ, ENNReal.ofReal
    (ω (2*m)^2 * (‖r true m‖^2 + ‖r false m‖^2))

def adaptedCutoffCondition (w : ℤ → ℝ) (M : ℝ) (N : ℕ) : Prop :=
  diagonalThreshold w M ≤ N ∧
  ∀ v : ℤ → ℝ, SecondaryWeight v →
    ∀ φ ∈ physicalComponentBall (productWeight w v) (2*M),
      rawEnergy (productWeight w v) (adaptedCoefficients N φ-rawFourier φ) ≤
        ENNReal.ofReal ((M/16)^2)

def adaptedThreshold (w : ℤ → ℝ) (M : ℝ) : ℕ :=
  if h : ∃ N : ℕ, adaptedCutoffCondition w M N then Nat.find h
  else diagonalThreshold w M

end NlsGge.ThirdConsultation.KST
end
