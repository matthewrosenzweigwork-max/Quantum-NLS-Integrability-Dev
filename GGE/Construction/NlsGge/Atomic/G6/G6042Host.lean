import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38

                                                                                                                
                                                                                               
                                                                                                                
                                                                                                                         
                                                                                                                           
                                                                                               
                                                                                                          
                                                                                                                         
                                                                                     
                                                                                                                      
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem coordinateDirection_mem (n : ℤ) (a : ℂ) :
  Pi.single n a ∈ seqSobolev38 (1 : ℝ) := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  refine summable_of_ne_finset_zero (s := {n}) (fun m hm => ?_)
  rw [Finset.mem_singleton] at hm
  simp [Pi.single_apply, hm]

def coordinateDirection (n : ℤ) (a : ℂ) : SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierMk38 ((1 : ℕ) : ℝ) (Pi.single n a) (by rw [Nat.cast_one]; exact coordinateDirection_mem n a)

/-- Coordinate of the Hamiltonian vector field; it need not assemble to h^1. -/
def coordinateHamiltonianField (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ)
    (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) : ℂ :=
  -(Complex.I / 2) *
    ((fderiv ℝ H z (coordinateDirection n 1) : ℝ) +
      Complex.I * (fderiv ℝ H z (coordinateDirection n Complex.I) : ℝ))

def coordinatePoisson (n : ℤ) (f g : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ)
    (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  (1 / 2 : ℝ) *
    (fderiv ℝ f z (coordinateDirection n 1) *
      fderiv ℝ g z (coordinateDirection n Complex.I) -
     fderiv ℝ f z (coordinateDirection n Complex.I) *
      fderiv ℝ g z (coordinateDirection n 1))

def coordinateAction (n : ℤ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2

end
end NlsGge.GKDefinitionDesign
