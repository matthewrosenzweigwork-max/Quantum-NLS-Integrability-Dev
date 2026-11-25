import NlsGge.Ramer.TruncatedDivergenceLimit
import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Ramer.ClosedDivergenceProductRule

/-!
# Bounded `C²` fields with convergent truncated divergences are closed-divergence fields

If `G : E_s → H` is `C²` with `‖G‖ ≤ B`, `‖DG‖ ≤ B` and the cylindrical divergences of the
truncated fields `G_N = P_N G(P_N ·)` converge in `L²(γ)` to `η`, then `G ∘ R` has closed
divergence `η` in the sense of `IsClosedDiv` (witness `N k = k`, `g k = G_k`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

/-- A bounded `C²` field with bounded derivative whose truncated cylindrical divergences
converge to `η` in `L²(γ)` has closed divergence `η`. -/
theorem isClosedDiv_of_tendsto_truncField {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : 1 / 2 < s)
    (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (η : (ℤ → ℂ) → ℝ) (hη : MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hlim : Tendsto (fun N => eLpNorm (fun z => cylDiv c N (truncField c s G N) z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith : (0:ℝ) < s)
  refine ⟨hη, fun k => k, fun k => truncField c s G k, fun _ => B, fun _ => 0,
    fun k => contDiff_truncField c s G hG k, ?_, ?_, ?_, hlim⟩
  · intro k v
    rw [pow_zero, mul_one]
    exact norm_truncField_le c s G B hB k v
  · intro k v
    rw [pow_zero, mul_one]
    exact norm_fderiv_truncField_le c s hs0 G hG B hDB k v
  · exact tendsto_eLpNorm_truncatedField c s hs G hG.continuous B hB

/-- Existence of the closed divergence of a bounded `C²` field with bounded derivative. -/
theorem exists_isClosedDiv_of_bounded {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : 1 / 2 < s)
    (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    ∃ η : (ℤ → ℂ) → ℝ,
      IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η := by
  obtain ⟨η, hη, hlim⟩ := exists_tendsto_cylDiv_truncField c s hs G hG B hB hDB
  exact ⟨η, isClosedDiv_of_tendsto_truncField c s hs G hG B hB hDB η hη hlim⟩

end NlsGge.Ramer
