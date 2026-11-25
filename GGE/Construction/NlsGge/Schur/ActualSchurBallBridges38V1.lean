import NlsGge.Schur.ActualSchurBallMap38V1
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Schur.ActualSchurE02Identification38V1

/-!
# NEW-F05 interface bridges

* `planeField38_eq_planeL2`: the Schur-side plane field (H¹ carrier image) is the canonical
  finite-plane `L²` field `planeL2 N z` used by the hierarchy's trace identity (W2).
* `boundedCoefficients_bounds38`: a `BoundedCoefficients lo up` gives the explicit
  lower/upper bounds used on the Schur side.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

theorem planeField38_eq_planeL2 (N : ℕ) (z : FourierPlane N) :
    planeField38 N z = planeL2 N z := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext k
  rw [physicalFourierL2_apply, physicalFourierL2_apply, planeField38,
    physicalH1ComplexCarrierToL2Actual22_fourier, physicalFourier_planeL2]
  by_cases h : ∃ i, modeIndex N i = k
  · obtain ⟨i, rfl⟩ := h
    rw [planeH1Embedding38_modeIndex, physicalFourier_planeField]
  · rw [planeH1Embedding38_off N z k (fun i hi => h ⟨i, hi.symm⟩)]
    have hout : k < -(N : ℤ) ∨ (N : ℤ) < k := by
      by_contra hc
      push_neg at hc
      exact h (modeIndex_covers N k hc.1 hc.2)
    exact (physicalFourier_planeField_outside N z k hout).symm

theorem boundedCoefficients_bounds38 {lo up : ℝ} (c : BoundedCoefficients lo up) :
    0 < lo ∧ lo ≤ up ∧ (∀ j, lo ≤ c.val j) ∧ (∀ j, c.val j ≤ up) :=
  ⟨c.property.1, c.property.2.1, fun j => (c.property.2.2 j).1, fun j => (c.property.2.2 j).2⟩

/-- The plane H¹ norm equals the `physicalSobolevL2 1` norm of the canonical plane field
(the norm used by the hierarchy's `fullEnergy38_ge_gapSum_window_uniform`). -/
theorem planeH1Norm38_eq_physicalSobolev (N : ℕ) (z : FourierPlane N)
    (hu : SobolevSquareSummable 1 (physicalFourier (planeL2 N z))) :
    planeH1Norm38 N z = ‖physicalSobolevL2 1 (planeL2 N z) hu‖ := by
  have key : ∀ (u v : PhysicalL2) (_ : u = v) (hu' : SobolevSquareSummable 1 (physicalFourier u))
      (hv : SobolevSquareSummable 1 (physicalFourier v)),
      ‖physicalSobolevL2 1 u hu'‖ = ‖physicalSobolevL2 1 v hv‖ := by
    intro u v h hu' hv; subst h; rfl
  rw [planeH1Norm38, ← physicalSobolevL2_norm_h1Carrier38 (planeH1Embedding38 N z)]
  exact key _ _ (planeField38_eq_planeL2 N z) _ _

end NlsGge.Schur
