import NlsGge.Spectral.ActualPhysicalL2UnitEndpointRealityV1
import NlsGge.Spectral.ActualPhysicalL2ZsFullTraceEntireV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Half the actual UNIT-period full trace. The doubled trace is a different
function; this definition retains the manuscript quasimomentum normalization. -/
def actualPhysicalUnitHalfTrace32 (u : PhysicalL2) (z : ℂ) : ℂ :=
  Matrix.trace (actualComplexZsDysonTsum
    (fun t => naturalPhysicalCoverL2 u (t : SpectralCircle)) z 1) / 2

/-- The actual unit half trace is entire for every rough physical potential. -/
theorem analyticOnNhd_actualPhysicalUnitHalfTrace32 (u : PhysicalL2) :
    AnalyticOnNhd ℂ (actualPhysicalUnitHalfTrace32 u) Set.univ := by
  intro z hz
  exact (analyticOnNhd_actualPhysicalL2ZsFullTrace u 1 (by norm_num) z hz).div_const

theorem analyticOnNhd_actualPhysicalUnitBranchRadicand32 (u : PhysicalL2) :
    AnalyticOnNhd ℂ (fun z => actualPhysicalUnitHalfTrace32 u z ^ 2 - 1) Set.univ := by
  exact ((analyticOnNhd_actualPhysicalUnitHalfTrace32 u).pow 2).sub analyticOnNhd_const

/-- A zero of the unit branch radicand is an actual signed trace endpoint,
so its spectral parameter is real by the already realized source graph symmetry.
No compactness, ordered labels, chosen square root or asymptotics are assumed. -/
theorem actualPhysicalUnitBranchRadicand_eq_zero_im32
    (u : PhysicalL2) (z : ℂ)
    (hz : actualPhysicalUnitHalfTrace32 u z ^ 2 - 1 = 0) : z.im = 0 := by
  let d : ℂ := Matrix.trace (actualComplexZsDysonTsum
    (fun t => naturalPhysicalCoverL2 u (t : SpectralCircle)) z 1)
  have hs : (d / 2) ^ 2 - 1 = 0 := hz
  have hf : (d - 2) * (d + 2) = 0 := by linear_combination 4 * hs
  rcases mul_eq_zero.mp hf with hp | hm
  · have ht : d = 2 := sub_eq_zero.mp hp
    apply actualPhysicalL2UnitTrace_endpoint_im_eq_zero 0 u z
    simpa [spectralSign, d] using ht
  · have ht : d = -2 := add_eq_zero_iff_eq_neg.mp hm
    apply actualPhysicalL2UnitTrace_endpoint_im_eq_zero 1 u z
    simpa [spectralSign, d] using ht

theorem actualPhysicalUnitBranchRadicand_nonzero_of_im_ne32
    (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    actualPhysicalUnitHalfTrace32 u z ^ 2 - 1 ≠ 0 := by
  intro h
  exact hz (actualPhysicalUnitBranchRadicand_eq_zero_im32 u z h)

theorem actualPhysicalUnitBranchRadicand_upperHalfPlane_nonzero32
    (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    actualPhysicalUnitHalfTrace32 u z ^ 2 - 1 ≠ 0 :=
  actualPhysicalUnitBranchRadicand_nonzero_of_im_ne32 u z (ne_of_gt hz)

end NlsGge.SpectralFoundations
end
