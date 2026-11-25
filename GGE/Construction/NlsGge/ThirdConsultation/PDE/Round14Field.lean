import Mathlib
import NlsGge.ThirdConsultation.PDE.Round4
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.ThirdConsultation.Sobolev.Round5

                                                                                                                      
                                                                                                                         
                                                                                                                               
                                                                                              
                                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.NLS38 NlsGge.GKDefinitionDesign NlsGge.Atomic.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def physicalCoreFourier
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) : HamiltonianCore38 :=
  Eq.mp
    (congrArg SobolevCarrier38
      (show ((3 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) + 2 by norm_num))
    (physicalSobolevFourierEquiv38 ((3 : ℕ) : ℝ) u)

def physicalCoreBase
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) :
    PhysicalSobolev38 ((1 : ℕ) : ℝ) :=
  (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm
    (hamiltonianBase (physicalCoreFourier u))

/-- Actual -i(-u_xx+2|u|^2u), with an H1 target at every H3 datum. -/
def nlsVectorField
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) :
    PhysicalSobolev38 ((1 : ℕ) : ℝ) :=
  let x : HamiltonianCore38 := physicalCoreFourier u
  (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm
    (lam ((1 : ℕ) : ℝ) x -
      J38 ((1 : ℕ) : ℝ)
        (nonlinC 1 (show 1 ≤ (1 : ℕ) from le_rfl) (hamiltonianBase x)))

theorem carrierCoe38_cast_eq (r s : ℝ) (h : r = s) (y : SobolevCarrier38 r)
    (n : ℤ) :
    carrierCoe38 s (Eq.mp (congrArg SobolevCarrier38 h) y) n =
      carrierCoe38 r y n := by
  subst h; rfl

theorem carrierCoe38_physicalCoreFourier
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) (n : ℤ) :
    carrierCoe38 (((1 : ℕ) : ℝ) + 2) (physicalCoreFourier u) n =
      carrierCoe38 ((3 : ℕ) : ℝ)
        (physicalSobolevFourierEquiv38 ((3 : ℕ) : ℝ) u) n :=
  carrierCoe38_cast_eq _ _ (show ((3 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) + 2 by norm_num) _ n

theorem nlsVectorField_coefficient
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) (n : ℤ) :
  fourierSeq38 (physicalSobolevEmbed 1 (nlsVectorField u)) n =
    -Complex.I *
      (((disp n : ℝ) : ℂ) *
          fourierSeq38 (physicalSobolevEmbed 3 u) n +
        nonlin (fourierSeq38 (physicalSobolevEmbed 3 u)) n) := by
  have hc : ∀ k : ℤ, carrierCoe38 (((1 : ℕ) : ℝ) + 2) (physicalCoreFourier u) k =
      fourierSeq38 (physicalSobolevEmbed 3 u) k := fun k => by
    rw [carrierCoe38_physicalCoreFourier, physicalSobolevEmbed_fourier]
  have hc' : carrierCoe38 (((1 : ℕ) : ℝ) + 2) (physicalCoreFourier u) =
      fourierSeq38 (physicalSobolevEmbed 3 u) := funext hc
  rw [physicalSobolevEmbed_fourier]
  unfold nlsVectorField
  simp only [LinearIsometryEquiv.apply_symm_apply]
  have hb : carrierCoe38 ((1 : ℕ) : ℝ) (hamiltonianBase (physicalCoreFourier u)) =
      fourierSeq38 (physicalSobolevEmbed 3 u) := by
    rw [hamiltonianBase, carrierCoe38_incl38]
    exact hc'
  have e1 : carrierCoe38 ((1 : ℕ) : ℝ)
      (lam ((1 : ℕ) : ℝ) (physicalCoreFourier u) -
        J38 ((1 : ℕ) : ℝ)
          (nonlinC 1 (show 1 ≤ (1 : ℕ) from le_rfl)
            (hamiltonianBase (physicalCoreFourier u)))) n =
      carrierCoe38 ((1 : ℕ) : ℝ) (lam ((1 : ℕ) : ℝ) (physicalCoreFourier u)) n -
        carrierCoe38 ((1 : ℕ) : ℝ) (J38 ((1 : ℕ) : ℝ)
          (nonlinC 1 (show 1 ≤ (1 : ℕ) from le_rfl)
            (hamiltonianBase (physicalCoreFourier u)))) n := rfl
  rw [e1, carrierCoe38_lam, carrierCoe38_J38, carrierCoe38_nonlinC, hb, hc]
  ring

theorem physicalCoreBase_embed
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ)) :
  physicalSobolevEmbed 1 (physicalCoreBase u) = physicalSobolevEmbed 3 u := by
  apply reflectedFourierL2.injective
  apply lp.ext
  funext n
  have h1 := physicalSobolevEmbed_fourier 1 (physicalCoreBase u) n
  have h2 := physicalSobolevEmbed_fourier 3 u n
  change fourierSeq38 _ n = fourierSeq38 _ n
  rw [h1, h2]
  unfold physicalCoreBase
  rw [LinearIsometryEquiv.apply_symm_apply, hamiltonianBase, carrierCoe38_incl38,
    carrierCoe38_physicalCoreFourier]

end
end NlsGge.ThirdConsultation.PDE
