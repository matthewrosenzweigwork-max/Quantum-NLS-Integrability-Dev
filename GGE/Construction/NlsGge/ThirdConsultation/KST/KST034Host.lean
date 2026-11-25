import Mathlib
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.KST032Host

                                                                                                                          
                                                                                                         
                                                                                                                      
                                                                                                             
                                                                                                              
                                                                                                                    
                                                                                                                              
                                                                                   
                                                                                                                             
                                                                                                                          
                                                                                                                     
                                               
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

abbrev RawPair := Bool → ℤ → ℂ

def rawFourier (φ : Potential) : RawPair :=
  fun channel m => physicalFourier (φ channel) m

def weightedCoeffs (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : Weighted ω) : RawPair := fun channel m => x channel m

def weightedLift (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (r : RawPair) : Weighted ω :=
  if h : ∃ x : Weighted ω, weightedCoeffs ω x = r then Classical.choose h else 0

def adaptedCoefficients (N : ℕ) (φ : Potential) : RawPair :=
  fun channel m => if m.natAbs ≤ N then rawFourier φ channel m
    else if channel then c φ (-m) (diagonalZero (-m) φ)
    else b φ m (diagonalZero m φ)

def adaptedFourier (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (N : ℕ)
    (x : Weighted ω) : Weighted ω :=
  weightedLift ω (adaptedCoefficients N (weightedPotential ω hω x))

end NlsGge.ThirdConsultation.KST
end
