import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTopCore
import NlsGge.ThirdConsultation.PDE.BirkhoffCarrier
import NlsGge.ThirdConsultation.PDE.BirkhoffLevelZero
import NlsGge.ThirdConsultation.PDE.BirkhoffRawG6
import NlsGge.ThirdConsultation.PDE.BirkhoffRawInv
import NlsGge.Atomic.G6.G6027

/- BKTOP PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/ThirdConsultation/PDE/BirkhoffTop.lean, namespace NlsGge.ThirdConsultation.PDE.
   Pro r15 Q6 steps 4-5 (followup13 DEFINITIONS/BIRKHOFF_REALIZATION.lean.md + STATEMENTS/BIRKHOFF_REALIZATION.md), in Pro's
   order: (i) the all-level raw analytic/continuous fields actualT38_analytic, actualTinv38_analytic, actualT38_continuous,
   actualTinv38_continuous (heads verbatim; positive levels = landed G6027 transported through the landed raw carrier
   equalities and the Fourier equivalence, level zero = landed BirkhoffLevelZero); (ii) the records actualBirkhoffTop38 and
   actualBirkhoffAnalytic38 (bodies verbatim); (iii) only then the projection equalities actualBirkhoffTop38_Phi /
   _cleanPhiInv / _TC / _TinvC (heads verbatim); (iv) canonicity: actualBirkhoffTop38_canonical / _fderiv_zero (heads
   verbatim; landed actualT38_canonical_zero / actualT38_fderiv_zero, definitionally on TC 0) and actualBirkhoffCanonical38
   (body verbatim). NOT included (step 6, M-049 chain not landed): actualBirkhoffTop38_inverse_polynomial,
   actualBirkhoffMolnar38, actualBirkhoffInput38. grep NlsGge/ (2026-11-02): none of these names exists. -/
set_option autoImplicit false
open Set
open scoped Classical ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actualT38_analytic (m : ℕ) :
    AnalyticOnNhd ℝ
      (carrierMap38 (m : ℝ) (m : ℝ) actualT38 (actualT38_mapsTo m)) Set.univ :=
  NlsGge.ThirdConsultation.PDE.BirkhoffTopCore.T_analytic_of actualT38_mapsTo actualT38_carrier_eq actualT38_analytic_zero
    (fun m hm => (G6027 m hm).1) m

theorem actualTinv38_analytic (m : ℕ) :
    AnalyticOnNhd ℝ
      (carrierMap38 (m : ℝ) (m : ℝ) actualTinv38 (actualTinv38_mapsTo m)) Set.univ :=
  NlsGge.ThirdConsultation.PDE.BirkhoffTopCore.Tinv_analytic_of actualTinv38_mapsTo actualTinv38_carrier_eq actualTinv38_analytic_zero
    (fun m hm => (G6027 m hm).2.1) m

theorem actualT38_continuous (m : ℕ) :
    Continuous
      (carrierMap38 (m : ℝ) (m : ℝ) actualT38 (actualT38_mapsTo m)) :=
  NlsGge.ThirdConsultation.PDE.BirkhoffTopCore.continuous_of_analytic (actualT38_analytic m)

theorem actualTinv38_continuous (m : ℕ) :
    Continuous
      (carrierMap38 (m : ℝ) (m : ℝ) actualTinv38 (actualTinv38_mapsTo m)) :=
  NlsGge.ThirdConsultation.PDE.BirkhoffTopCore.continuous_of_analytic (actualTinv38_analytic m)

def actualBirkhoffTop38 : BirkhoffTop38 where
  T := actualT38
  Tinv := actualTinv38
  mapsTo_T := actualT38_mapsTo
  mapsTo_Tinv := actualTinv38_mapsTo
  left_inv := actualT38_left_inv
  right_inv := actualT38_right_inv
  continuous_T := actualT38_continuous
  continuous_Tinv := actualTinv38_continuous
  action_L2 := actualT38_action

def actualBirkhoffAnalytic38 :
    BirkhoffAnalytic38 actualBirkhoffTop38 Set.univ where
  analytic_T := fun m _ => actualT38_analytic m
  analytic_Tinv := fun m _ => actualTinv38_analytic m

theorem actualBirkhoffTop38_Phi (u : PhysicalL2) (n : ℤ) :
    actualBirkhoffTop38.Φ u n = actualPhi u n := by
  show actualT38 (fourierSeq38 u) n = _
  rw [actualT38_fourierSeq38]

theorem actualBirkhoffTop38_cleanPhiInv
    (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) :
    actualBirkhoffTop38.cleanΦinv z = actualPhiInv (seqToLp38 z hz) := by
  rw [actualBirkhoffTop38.cleanΦinv_of_mem z hz]
  exact NlsGge.ThirdConsultation.PDE.BirkhoffTopCore.physInv_Tinv z hz _

theorem actualBirkhoffTop38_TC (m : ℕ) :
    actualBirkhoffTop38.TC m = actualTC38 m :=
  actualT38_carrier_eq m

theorem actualBirkhoffTop38_TinvC (m : ℕ) :
    actualBirkhoffTop38.TinvC m = actualTinvC38 m :=
  actualTinv38_carrier_eq m

theorem actualBirkhoffTop38_canonical
    (x ξ η : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    stdSymplectic38
      (carrierCoe38 ((0 : ℕ) : ℝ)
        (fderiv ℝ (actualBirkhoffTop38.TC 0) x ξ))
      (carrierCoe38 ((0 : ℕ) : ℝ)
        (fderiv ℝ (actualBirkhoffTop38.TC 0) x η)) =
    stdSymplectic38
      (carrierCoe38 ((0 : ℕ) : ℝ) ξ)
      (carrierCoe38 ((0 : ℕ) : ℝ) η) :=
  actualT38_canonical_zero x ξ η

theorem actualBirkhoffTop38_fderiv_zero :
    fderiv ℝ (actualBirkhoffTop38.TC 0) 0 =
      ContinuousLinearMap.id ℝ (SobolevCarrier38 ((0 : ℕ) : ℝ)) :=
  actualT38_fderiv_zero

def actualBirkhoffCanonical38 :
    BirkhoffCanonical38 actualBirkhoffTop38 where
  canonical := actualBirkhoffTop38_canonical
  fderiv_zero := actualBirkhoffTop38_fderiv_zero

end
end NlsGge.ThirdConsultation.PDE
