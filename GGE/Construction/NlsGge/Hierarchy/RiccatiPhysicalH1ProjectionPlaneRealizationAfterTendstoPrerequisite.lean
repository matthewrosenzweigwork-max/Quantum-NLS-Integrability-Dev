import NlsGge.Hierarchy.RiccatiPhysicalH1CarrierAfterUnweightedCoordinateSecond
import NlsGge.Hierarchy.RiccatiWeightedRealProjectionTendstoPrerequisite
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.PhysicalProjection
import Mathlib.Tactic
import Mathlib.Topology.Basic

set_option autoImplicit false
noncomputable section

/-! The symmetric weighted Fourier projections of the actual H¹ carrier are
the existing finite Fourier planes on the actual period-one physical L²
space. This is the density bridge needed before applying the source Q₂
integration-by-parts identity to approximants. -/

namespace NlsGge.Pilot

open NlsGge.Analysis

local notation "H1Weight" => (sobolevModeWeight (1 : ℝ))
local instance : Fact (∀ n : ℤ, 0 < H1Weight n) := ⟨by
  intro n
  change 0 < Real.rpow (japaneseBracket n) (2 * (1 : ℝ))
  exact Real.rpow_pos_of_pos (japaneseBracket_pos n) _⟩

def physicalH1FiniteProjection (N : ℕ) (x : SobolevHilbert 1) :
    SobolevHilbert 1 :=
  weightedRealProjectionContinuous H1Weight (symmetricModes N) x

def physicalH1FiniteProjectionPlane (N : ℕ) (x : SobolevHilbert 1) :
    FourierPlane N :=
  fun i => (show WeightedHilbert H1Weight from x)
    (modeIndex N i)

theorem physicalH1FiniteProjection_fourier (N : ℕ) (x : SobolevHilbert 1)
    (n : ℤ) :
    physicalFourier
      (physicalH1CarrierToL2AfterAcceptedCoordinate (physicalH1FiniteProjection N x)) n =
        if n ∈ symmetricModes N then
          (show WeightedHilbert H1Weight from x) n else 0 := by
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  change (show WeightedHilbert H1Weight from
      weightedRealProjectionContinuous H1Weight (symmetricModes N) x) n = _
  exact weightedRealProjection_apply H1Weight (symmetricModes N) x n

theorem physicalH1FiniteProjection_realizesPlane (N : ℕ)
    (x : SobolevHilbert 1) :
    physicalH1CarrierToL2AfterAcceptedCoordinate (physicalH1FiniteProjection N x) =
      planeL2 N (physicalH1FiniteProjectionPlane N x) := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  rw [physicalH1FiniteProjection_fourier]
  by_cases hn : n ∈ symmetricModes N
  · have hn' : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by
      simpa only [symmetricModes, Finset.mem_Icc] using hn
    obtain ⟨i, hi⟩ := modeIndex_covers N n hn'.1 hn'.2
    rw [if_pos hn, physicalFourier_planeL2, ← hi,
      physicalFourier_planeField N (physicalH1FiniteProjectionPlane N x) i]
    rfl
  · have hout : n < -(N : ℤ) ∨ (N : ℤ) < n := by
      simp only [symmetricModes, Finset.mem_Icc] at hn
      omega
    rw [if_neg hn, physicalFourier_planeL2,
      physicalFourier_planeField_outside N (physicalH1FiniteProjectionPlane N x) n hout]

theorem physicalH1FiniteProjection_tendsto (x : SobolevHilbert 1) :
    Filter.Tendsto (fun N : ℕ => physicalH1FiniteProjection N x)
      Filter.atTop (nhds x) := by
  exact weightedRealProjection_tendsto_actual x

end NlsGge.Pilot
