import NlsGge.Birkhoff.SignedMoments38g
open NlsGge.Birkhoff NlsGge.Pilot NlsGge.HierarchyRiccati.Core NlsGge.Measure NlsGge.Sobolev38
open scoped ContDiff

/-! SIGNED-MOMENTS bridge on the `ν_{W,N}` side (review REVIEW_SIGNED_MOMENTS finding N2). -/

local instance : MeasureTheory.IsProbabilityMeasure spatialMeasure := by unfold spatialMeasure; infer_instance
namespace NlsGge.Birkhoff

/-- SIGNED-MOMENTS (review N2): on every Fourier plane the continuous signed charge is the spectral
moment `C_k` of the trigonometric polynomial. -/
theorem signedChargeFn38_planeL2 (m k N : ℕ) (hm : 2 ≤ m) (hk : k ≤ 2*m-2) (z : FourierPlane N) :
    signedChargeFn38 m k (planeL2 N z) = signedSpectralMoment38 (planeL2 N z) k := by
  have hU : ContDiff ℝ ∞ (planeReal N z) := (contDiff_planeReal N z).of_le le_top
  refine signedChargeFn38_smooth m k hm hk (planeL2 N z)
    (fun r => (mem_seqSobolev38_iff _ _).1 (physicalFourier_planeL2_mem38 r N z))
    (planeReal N z) hU (planeReal_periodic N z) ?_
  have e := lift_planeReal_F11_38 N z
  show ContinuousMap.toLp 2 spatialMeasure ℂ _ = _
  rw [e]; rfl

end NlsGge.Birkhoff
