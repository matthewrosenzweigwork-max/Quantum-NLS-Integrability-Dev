import NlsGge.GK38.AbelianFixedGapRowEnvelope
import NlsGge.GK38.AbelianCompactRatioBound
import NlsGge.GK38.AbelianFullRealSpace

/-! UNCOMPILED genuine complex image of the fixed actual full REAL gap cube.
The missing coordinate is never overwritten by the counting center. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p6ComplexFullGapCube38 (u : PhysicalL2) : Set Lib.L2Seq :=
  p6RealInclude38 '' p5FullRealGapCube38 u

theorem p6ComplexFullGapCube_isCompact38 (u : PhysicalL2) :
    IsCompact (p6ComplexFullGapCube38 u) :=
  (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous

theorem p6ComplexFullGapCube_actual_gaps38 (u : PhysicalL2) (s : Lib.L2Seq)
    (hs : s ∈ p6ComplexFullGapCube38 u) :
    ∀ m : ℤ, Lib.sigmaOf s m ∈
      segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m) := by
  obtain ⟨t,ht,rfl⟩ := hs
  intro m
  simpa only [Lib.sigmaOf,p6RealInclude_apply38,countingCenter38,add_comm] using ht m

theorem p6ComplexFullGapCube_original_placement38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : Lib.L2Seq)
    (hs : s ∈ p6ComplexFullGapCube38 u) :
    ∀ m : ℤ, Lib.sigmaOf s m ∈ closedBall (C m) (R m) := by
  obtain ⟨c,N,hg,hsp⟩ := hfam
  intro m
  exact ball_subset_closedBall ((hsp.1 m).1 (p6ComplexFullGapCube_actual_gaps38 u s hs m))

theorem p6ComplexFullGapCube_common_ratio38 (u : PhysicalL2) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ s ∈ p6ComplexFullGapCube38 u, ∀ m : ℤ,
      ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
        ‖p2OmittedRatio38 m ((realSlice u,s),z)‖ ≤ H :=
  p6OmittedRatio_compact_input_bound38 (realSlice u) (realSlice_mem_gkW u)
    (p6ComplexFullGapCube38 u) (p6ComplexFullGapCube_isCompact38 u)

end
end NlsGge.GK38
