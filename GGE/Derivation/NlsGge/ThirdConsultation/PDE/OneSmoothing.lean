import Mathlib
import NlsGge.ThirdConsultation.PDE.InverseSmoothingFields
import NlsGge.ThirdConsultation.PDE.ForwardSmoothingHeads
import NlsGge.Atomic.KSN.KSN021

/- ONE SMOOTHING PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet increment;
   root-owned BIRKHOFF_REALIZATION endpoint), target NlsGge/ThirdConsultation/PDE/OneSmoothing.lean. Printed VERBATIM
   (Pro r16 L1256-1316): actualTinv38_smooth, actualTinv38_analytic_smooth (proofs: InverseSmoothingFields `_top` with
   hK21 := KSN021_main), actualOneSmoothingInput38 (body), actual_birkhoff_inputs (head + term). Needs ROOT MAIN PROBE
   (after InverseSmoothingFields lands, q239). -/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actualTinv38_smooth
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ z ∈ seqSobolev38 (r : ℝ),
      actualBirkhoffInput38.Tinv z - z ∈
        seqSobolev38 ((r + 1 : ℕ) : ℝ) :=
  actualTinv38_smooth_top (fun N hN => NlsGge.GKDefinitionDesign.KSN021_main N hN) r hr

theorem actualTinv38_analytic_smooth
    (r : ℕ) (hr : 1 ≤ r) :
    AnalyticOnNhd ℝ
      (carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun z => actualBirkhoffInput38.Tinv z - z)
        (actualTinv38_smooth r hr)) Set.univ :=
  actualTinv38_analytic_smooth_top (fun N hN => NlsGge.GKDefinitionDesign.KSN021_main N hN) r hr

def actualOneSmoothingInput38 :
    OneSmoothingInput38 actualBirkhoffInput38 where
  smooth_T := actualT38_smooth
  smooth_Tinv := actualTinv38_smooth
  analytic_smooth_T := actualT38_analytic_smooth
  analytic_smooth_Tinv := actualTinv38_analytic_smooth

theorem actual_birkhoff_inputs :
    BirkhoffAnalytic38 actualBirkhoffTop38 Set.univ ∧
    BirkhoffCanonical38 actualBirkhoffTop38 ∧
    BirkhoffMolnar38 actualBirkhoffTop38 ∧
    OneSmoothingInput38 actualBirkhoffInput38 ∧
    actualBirkhoffInput38.toBirkhoffTop38 = actualBirkhoffTop38 ∧
    (∀ (u : PhysicalL2) (n : ℤ),
      actualBirkhoffTop38.Φ u n = actualPhi u n) ∧
    (∀ (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0),
      actualBirkhoffTop38.cleanΦinv z = actualPhiInv (seqToLp38 z hz)) := by
  exact ⟨actualBirkhoffAnalytic38, actualBirkhoffCanonical38,
    actualBirkhoffMolnar38, actualOneSmoothingInput38,
    actualBirkhoffInput38_top, actualBirkhoffTop38_Phi,
    actualBirkhoffTop38_cleanPhiInv⟩

end
end NlsGge.ThirdConsultation.PDE
