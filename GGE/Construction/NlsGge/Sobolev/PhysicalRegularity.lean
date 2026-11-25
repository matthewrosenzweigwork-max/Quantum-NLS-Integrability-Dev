import NlsGge.Sobolev.PhysicalWeighted
import NlsGge.Sobolev.SourceReflection

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Pilot

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem physicalWeighted_sobolev_reflected (u : PhysicalWeighted c s) (r : ℝ) :
    SobolevSquareSummable r (reflectedFourier u.field) :=
  sourceWeightedSquareSummable_sobolev c s r (reflectedFourier u.field) u.membership

theorem physicalWeighted_sobolev (u : PhysicalWeighted c s) (r : ℝ) :
    SobolevSquareSummable r (physicalFourier u.field) := by
  have h := sobolevSquareSummable_reflection r (reflectedFourier u.field)
    (physicalWeighted_sobolev_reflected c s u r)
  simpa only [reflectedFourier, neg_neg] using h

/-- Actual Sobolev encoding of an already physical L2 class. -/
def physicalWeightedSobolevL2 (u : PhysicalWeighted c s) (r : ℝ) : lp (fun _ : ℤ => ℂ) 2 :=
  physicalSobolevL2 r u.field (physicalWeighted_sobolev c s u r)

theorem physicalWeightedSobolevL2_norm_sq (u : PhysicalWeighted c s) (r : ℝ) :
    ‖physicalWeightedSobolevL2 c s u r‖ ^ 2 =
      ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * r) * ‖physicalFourier u.field n‖ ^ 2 :=
  physicalSobolevL2_norm_sq r u.field (physicalWeighted_sobolev c s u r)

theorem physicalWeighted_ordinaryWeightedMembership (u : PhysicalWeighted c s) :
    WeightedSquareSummable (sourceRate c) s (physicalFourier u.field) := by
  have h := weightedSquareSummable_reflection (sourceRate c) (sourceRate_neg c) s
    (reflectedFourier u.field) u.membership
  simpa only [reflectedFourier, neg_neg] using h

theorem physicalWeighted_ordinary_hasSum (u : PhysicalWeighted c s) :
    HasSum (fun n : ℤ => fullModeWeight c s n * ‖physicalFourier u.field n‖ ^ 2) (‖u‖ ^ 2) := by
  have h := weightedHilbert_hasSum (fullModeWeight c s)
    (show WeightedHilbert (fullModeWeight c s) from physicalWeightedFourier c s u)
  change HasSum (fun n : ℤ => fullModeWeight c s n * ‖reflectedFourier u.field n‖ ^ 2)
    (‖u‖ ^ 2) at h
  have hcomp := ((Equiv.neg ℤ).hasSum_iff).2 h
  change HasSum (fun n : ℤ => fullModeWeight c s (-n) *
    ‖reflectedFourier u.field (-n)‖ ^ 2) (‖u‖ ^ 2) at hcomp
  exact hcomp.congr (fun n => by
    simp only [fullModeWeight_neg, reflectedFourier, neg_neg, norm_neg])

theorem physicalWeighted_ordinary_norm_sq (u : PhysicalWeighted c s) :
    ‖u‖ ^ 2 = ∑' n : ℤ, fullModeWeight c s n * ‖physicalFourier u.field n‖ ^ 2 :=
  (physicalWeighted_ordinary_hasSum c s u).tsum_eq.symm

end NlsGge.Pilot
