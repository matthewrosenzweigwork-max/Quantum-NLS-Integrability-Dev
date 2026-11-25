import NlsGge.GK38.EigenvalueCompactnessHomotopyDefs
import NlsGge.GK38.EigenvalueCompactnessEigenPhaseLimit

/-! # S7: singleton endpoint phase continuity along the actual norm homotopy -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gapLower_norm_path_continuous38 (u : PhysicalL2) (n : ℤ) :
    ContinuousOn (fun t : ℝ => actualGapLowerAllE02_38 (t • u) n) (Icc 0 1) := by
  have he : (fun t : ℝ => actualGapLowerAllE02_38 (t • u) n) =
      fun t : ℝ => (lamSeq (realSlice (t • u)) (2*n)).re := by
    funext t
    exact (congrArg Complex.re (lamPlus_real (t • u) n).2).symm
  rw [he]
  exact Complex.continuous_re.comp_continuousOn (periodic_real_path_continuous38 u (2*n))

theorem gapUpper_norm_path_continuous38 (u : PhysicalL2) (n : ℤ) :
    ContinuousOn (fun t : ℝ => actualGapUpperAllE02_38 (t • u) n) (Icc 0 1) := by
  have he : (fun t : ℝ => actualGapUpperAllE02_38 (t • u) n) =
      fun t : ℝ => (lamSeq (realSlice (t • u)) (2*n+1)).re := by
    funext t
    exact (congrArg Complex.re (lamPlus_real (t • u) n).1).symm
  rw [he]
  exact Complex.continuous_re.comp_continuousOn (periodic_real_path_continuous38 u (2*n+1))

theorem periodicEndpoint_path_continuous38 (u : PhysicalL2) (n : ℤ) (upper : Bool) :
    Continuous (fun t : Time38 => periodicEndpoint38 ((t : ℝ) • u) n upper) := by
  cases upper
  · exact continuousOn_iff_continuous_domRestrict.mp (gapLower_norm_path_continuous38 u n)
  · exact continuousOn_iff_continuous_domRestrict.mp (gapUpper_norm_path_continuous38 u n)

theorem periodicEndpointPhase_path_continuous38 (u : PhysicalL2) (n : ℤ) (upper : Bool) :
    Continuous (fun t : Time38 => periodicEndpointPhase38 ((t : ℝ) • u) n upper) := by
  apply continuous_iff_seqContinuous.mpr
  intro t t₀ ht
  have hU : Tendsto (fun k => (t k : ℝ) • u) atTop (𝓝 ((t₀ : ℝ) • u)) :=
    (continuous_subtype_val.continuousAt.tendsto.comp ht).smul tendsto_const_nhds
  have hX := (periodicEndpoint_path_continuous38 u n upper).continuousAt.tendsto.comp ht
  have hP := periodicPhase_eigen_tendsto38 (IsWeakLim.of_tendsto hU) hX
    (fun k => periodicEndpointDirection_spec38 ((t k : ℝ) • u) n upper)
    (periodicEndpointDirection_spec38 ((t₀ : ℝ) • u) n upper)
  simpa only [periodicEndpointPhase38, Function.comp_def] using! hP

end
end NlsGge.GK38
