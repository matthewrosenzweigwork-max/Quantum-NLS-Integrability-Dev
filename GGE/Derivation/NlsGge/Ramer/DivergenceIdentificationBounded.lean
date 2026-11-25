import NlsGge.Ramer.TruncatedDivergenceLimit
import NlsGge.Ramer.RamerApproximantLimit

/-!
# Identification of Ramer's and v2's divergences (globally bounded fields; obligation (ID))

Let `1/2 < s` and `G : E_s → H` be `C²` with `‖G‖ ≤ B` and `‖DG‖ ≤ B`. This is v2's localized
field `G = ηK`; see `exists_bumped_field`. There is a single `η ∈ L²(γ)` such that:

* v2's route: `δ_cyl(P_N G(P_N ·)) → η` in `L²(γ)` (`exists_tendsto_cylDiv_truncField`);
* Ramer's route: `a_n(G) = ⟨P_n G x, x⟩ − tr(P_n D_H G(x)) → η` in `L²(γ)`
  (`tendsto_eLpNorm_ramerA`);
* `η` is unique up to `γ`-null sets (`ae_eq_of_tendsto_eLpNorm_two`).

**Localization (R5).** If an unbounded `K` agrees with `G` on an open `U ⊆ E_s`, then
Ramer's approximants of `K` converge to the same `η` in `L²(γ)` restricted to `R⁻¹(U)`
(`tendsto_eLpNorm_indicator_ramerA_of_eqOn`). Here `R` is the realization of samples in `E_s`.
So on each ball where v2 defines its local divergence by a bump, v2's and Ramer's local
divergences coincide `γ`-a.e.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

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

/-- **Divergence identification (ID) for globally bounded fields.** v2's truncated-field
divergences and Ramer's approximants converge in `L²(γ)` to the same limit. -/
theorem divergence_identification_bounded (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G)
    (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    ∃ η : (ℤ → ℂ) → ℝ, MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
      Tendsto (fun N => eLpNorm (fun z => cylDiv c N (truncField c s G N) z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => ramerA c s (le_of_lt (by linarith : 0 < s)) n G z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  obtain ⟨η, hη, hv2⟩ := exists_tendsto_cylDiv_truncField c s hs G hG B hB hDB
  exact ⟨η, hη, hv2, tendsto_eLpNorm_ramerA c s hs G hG B hB hDB η hη hv2⟩

/-- **Localized identification (R5).** If `K = G` on an open `U ⊆ E_s` and `η` is the common
limit for `G`, then Ramer's approximants of `K` converge to `η` in `L²(γ)` on `R⁻¹(U)`. -/
theorem tendsto_eLpNorm_indicator_ramerA_of_eqOn (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs0 : 0 ≤ s) (G K : FullWeightedHilbert c s → ActualCM c)
    {U : Set (FullWeightedHilbert c s)} (hU : IsOpen U) (hGK : Set.EqOn G K U)
    (η : (ℤ → ℂ) → ℝ)
    (hR : Tendsto (fun n => eLpNorm (fun z => ramerA c s hs0 n G z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      ((NlsGge.Measure.fullWeightedSequenceRealization c s ⁻¹' U).indicator
        (fun z => ramerA c s hs0 n K z - η z)) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR
    (fun _ => bot_le) (fun n => ?_)
  have heq : (NlsGge.Measure.fullWeightedSequenceRealization c s ⁻¹' U).indicator
      (fun z => ramerA c s hs0 n K z - η z) =
      (NlsGge.Measure.fullWeightedSequenceRealization c s ⁻¹' U).indicator
        (fun z => ramerA c s hs0 n G z - η z) := by
    funext z
    by_cases hz : z ∈ NlsGge.Measure.fullWeightedSequenceRealization c s ⁻¹' U
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        ramerA_congr_of_eqOn c s hs0 G K hU hGK n z hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
  rw [heq]
  exact eLpNorm_indicator_le (fun z => ramerA c s hs0 n G z - η z)
    (NlsGge.Measure.measurable_fullWeightedSequenceRealization c s hU.measurableSet)

end NlsGge.Ramer
