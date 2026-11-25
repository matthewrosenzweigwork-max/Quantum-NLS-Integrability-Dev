import NlsGge.Ramer.General.TruncatedDivergenceLimitG
import NlsGge.Ramer.General.RamerApproximantLimitGb

/-!
# Identification of Ramer's and v2's divergences, bounded fields (GB9)

Generalization of `NlsGge/Ramer/DivergenceIdentificationBounded.lean` to a `RamerSetting S`.
`G : S.E → S.H`, `γ = S.γ`, `ξ = S.R`. Hypotheses `‖G‖ ≤ B`, `‖DG‖ ≤ B` are unchanged (the
anisotropy constants are absorbed in GB3/GB5).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

/-- `L²` limits are unique up to null sets. -/
theorem ae_eq_of_tendsto_eLpNorm_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {η η' : α → ℝ}
    (h : Tendsto (fun k => eLpNorm (fun z => f k z - η z) 2 μ) atTop (𝓝 0))
    (h' : Tendsto (fun k => eLpNorm (fun z => f k z - η' z) 2 μ) atTop (𝓝 0)) :
    η =ᵐ[μ] η' := by
  have hle : ∀ k, eLpNorm (fun z => η z - η' z) 2 μ ≤
      eLpNorm (fun z => f k z - η z) 2 μ + eLpNorm (fun z => f k z - η' z) 2 μ := by
    intro k
    have e : (fun z => η z - η' z) =
        (-(fun z => f k z - η z)) + (fun z => f k z - η' z) := by
      funext z; simp only [Pi.add_apply, Pi.neg_apply]; ring
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_neg]
  have hsum := h.add h'
  rw [add_zero] at hsum
  have h0 : eLpNorm (fun z => η z - η' z) 2 μ = 0 :=
    le_antisymm (ge_of_tendsto' hsum hle) bot_le
  have := (eLpNorm_eq_zero_iff (by norm_num)).1 h0
  filter_upwards [this] with z hz
  exact sub_eq_zero.1 hz

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- **Divergence identification (ID) for globally bounded fields.** v2's truncated-field
divergences and Ramer's approximants converge in `L²(γ)` to the same limit. -/
theorem divergence_identification_bounded (G : S.E → S.H) (hG : ContDiff ℝ 2 G)
    (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    ∃ η : (ℤ → ℂ) → ℝ, MemLp η 2 S.γ ∧
      Tendsto (fun N => eLpNorm (fun z => S.cylDiv N (S.truncField G N) z - η z) 2 S.γ)
        atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => S.ramerA n G z - η z) 2 S.γ) atTop (𝓝 0) := by
  obtain ⟨η, hη, hv2⟩ := S.exists_tendsto_cylDiv_truncField G hG B hB hDB
  exact ⟨η, hη, hv2, S.tendsto_eLpNorm_ramerA G hG B hB hDB η hη hv2⟩

/-- **Localized identification (R5).** If `K = G` on an open `U ⊆ E` and `η` is the common
limit for `G`, then Ramer's approximants of `K` converge to `η` in `L²(γ)` on `R⁻¹(U)`. -/
theorem tendsto_eLpNorm_indicator_ramerA_of_eqOn (G K : S.E → S.H)
    {U : Set S.E} (hU : IsOpen U) (hGK : Set.EqOn G K U)
    (η : (ℤ → ℂ) → ℝ)
    (hR : Tendsto (fun n => eLpNorm (fun z => S.ramerA n G z - η z) 2 S.γ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      ((S.R ⁻¹' U).indicator (fun z => S.ramerA n K z - η z)) 2 S.γ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR
    (fun _ => bot_le) (fun n => ?_)
  have heq : (S.R ⁻¹' U).indicator (fun z => S.ramerA n K z - η z) =
      (S.R ⁻¹' U).indicator (fun z => S.ramerA n G z - η z) := by
    funext z
    by_cases hz : z ∈ S.R ⁻¹' U
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        S.ramerA_congr_of_eqOn G K hU hGK n z hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  rw [heq]
  exact eLpNorm_indicator_le (fun z => S.ramerA n G z - η z)
    (S.measurable_R hU.measurableSet)

end NlsGge.Ramer.General.RamerSetting
