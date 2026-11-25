import NlsGge.Ramer.General.TruncatedDivergenceLimitG
import NlsGge.Ramer.General.TruncatedFieldConvergenceG
import NlsGge.Ramer.General.ClosedDivergenceProductRuleGa

/-!
# Bounded `C²` fields with convergent truncated divergences are closed-divergence fields (general setting)

If `G : S.E → S.H` is `C²` with `‖G‖ ≤ B`, `‖DG‖ ≤ B` and the cylindrical divergences of the
truncated fields `G_N = P_N G(P_N ·)` converge in `L²(γ)` to `η`, then `G ∘ S.R` has closed
divergence `η` in the sense of `S.IsClosedDiv` (witness `N k = k`, `g k = G_k`).
Anisotropy only changes the constant: the derivative of `G_k` is bounded by `B √ratioSup`, so
the growth constant is `B (1 + √ratioSup)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- A bounded `C²` field with bounded derivative whose truncated cylindrical divergences
converge to `η` in `L²(γ)` has closed divergence `η`. -/
theorem isClosedDiv_of_tendsto_truncField
    (G : S.E → S.H)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (η : (ℤ → ℂ) → ℝ) (hη : MemLp η 2 S.γ)
    (hlim : Tendsto (fun N => eLpNorm (fun z => S.cylDiv N (S.truncField G N) z - η z) 2
      S.γ) atTop (𝓝 0)) :
    S.IsClosedDiv (fun z => G (S.R z)) η := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hκ0 : 0 ≤ Real.sqrt S.ratioSup := Real.sqrt_nonneg _
  have hBC : B ≤ B * (1 + Real.sqrt S.ratioSup) := by nlinarith
  have hκC : B * Real.sqrt S.ratioSup ≤ B * (1 + Real.sqrt S.ratioSup) := by nlinarith
  refine ⟨hη, fun k => k, fun k => S.truncField G k, fun _ => B * (1 + Real.sqrt S.ratioSup),
    fun _ => 0, fun k => S.contDiff_truncField G hG k, ?_, ?_, ?_, hlim⟩
  · intro k v
    rw [pow_zero, mul_one]
    exact (S.norm_truncField_le G B hB k v).trans hBC
  · intro k v
    rw [pow_zero, mul_one]
    exact (S.norm_fderiv_truncField_le G hG B hDB k v).trans hκC
  · exact S.tendsto_eLpNorm_truncatedField G hG.continuous B hB

/-- Existence of the closed divergence of a bounded `C²` field with bounded derivative. -/
theorem exists_isClosedDiv_of_bounded
    (G : S.E → S.H)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    ∃ η : (ℤ → ℂ) → ℝ, S.IsClosedDiv (fun z => G (S.R z)) η := by
  obtain ⟨η, hη, hlim⟩ := S.exists_tendsto_cylDiv_truncField G hG B hB hDB
  exact ⟨η, S.isClosedDiv_of_tendsto_truncField G hG B hB hDB η hη hlim⟩

end NlsGge.Ramer.General.RamerSetting
