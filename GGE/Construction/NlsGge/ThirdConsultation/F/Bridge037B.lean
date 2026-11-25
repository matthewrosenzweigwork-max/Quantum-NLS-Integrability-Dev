import Mathlib
import NlsGge.Hierarchy.RiccatiQ6Negative38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38
import NlsGge.Hierarchy.F03Spectral38
import NlsGge.Birkhoff.F05Identity38
import NlsGge.ThirdConsultation.F.Bridge037A

                                                                         
                                                                          
                                                                                        
                                                                                         
                                                                                            
                                                                                                     
                                                                                          
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.F
namespace Bridge037B

/-- The Fourier remainder depends only on the field (proof arguments are irrelevant). -/
theorem remainderV38_congr037 (M : ℕ) (β : ℕ → ℝ) {u v : ℝ → ℂ} (h : u = v)
    (hu : ContDiff ℝ ∞ u) (hpu : Function.Periodic u 1)
    (hv : ContDiff ℝ ∞ v) (hpv : Function.Periodic v 1) :
    remainderV38 M β u hu hpu = remainderV38 M β v hv hpv := by
  subst h
  rfl

/-- (b) On the degree-2 Sobolev element of a Fourier-plane field, `Vm38 3` is the realized
local remainder `vLocal38 3` of that field. -/
theorem Vm38_planeElement037 (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) :
    Vm38 3 β (planeElement38 (2 : ℝ) N z) = vLocal38 3 β (planeReal N z) := by
  rw [← vSobolev_plane38 3 (by norm_num) β N z]
  rfl

/-- (a, plane form): on Fourier-plane fields the realized local remainder is the Fourier
remainder `remainderV38 3 β` (smooth periodic field, degree `M = 3`). -/
theorem vLocal_planeReal037 (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) :
    vLocal38 3 β (planeReal N z) =
      remainderV38 3 β (planeReal N z) (planeReal_smooth38 N z) (planeReal_periodic N z) := by
  rw [← vSobolev_plane38 3 (by norm_num) β N z]
  unfold vSobolev38
  rw [(localRemainderSobolev38_smooth_spectral 3 (by norm_num) β (planeReal N z)
    (planeReal_smooth38 N z) (planeReal_periodic N z)
    (planeElement38 ((3 - 1 : ℕ) : ℝ) N z) (planeElement_hsource38 _ N z)).2]
  unfold remainderV38
  rw [localEnergy38_eq_spectralEnergy38]

/-- (a, trigonometric form): for every real trigonometric polynomial `P`, the realized local
remainder of `x ↦ (P x : ℂ)` is the Fourier remainder of the same field. -/
theorem vLocal_trig037 (β : ℕ → ℝ) (P : ℝ → ℝ) (hP : IsRealTrigPoly38 P) :
    vLocal38 3 β (fun x => (P x : ℂ)) =
      remainderV38 3 β (fun x => (P x : ℂ))
        (Complex.ofRealCLM.contDiff.comp hP.contDiff)
        (fun y => by simp only [hP.periodic y]) := by
  obtain ⟨N, z, hz⟩ := Bridge037A.trig_realize037 P hP
  have hfun : (fun x => (P x : ℂ)) = planeReal N z := funext fun x => (hz x).symm
  have hu : ContDiff ℝ ∞ (fun x => (P x : ℂ)) := Complex.ofRealCLM.contDiff.comp hP.contDiff
  have hp : Function.Periodic (fun x => (P x : ℂ)) 1 := fun y => by simp only [hP.periodic y]
  calc vLocal38 3 β (fun x => (P x : ℂ)) = vLocal38 3 β (planeReal N z) :=
        congrArg (vLocal38 3 β) hfun
    _ = remainderV38 3 β (planeReal N z) (planeReal_smooth38 N z) (planeReal_periodic N z) :=
        vLocal_planeReal037 β N z
    _ = remainderV38 3 β (fun x => (P x : ℂ)) hu hp :=
        (remainderV38_congr037 3 β hfun hu hp (planeReal_smooth38 N z)
          (planeReal_periodic N z)).symm

end Bridge037B
end NlsGge.ThirdConsultation.F
end

