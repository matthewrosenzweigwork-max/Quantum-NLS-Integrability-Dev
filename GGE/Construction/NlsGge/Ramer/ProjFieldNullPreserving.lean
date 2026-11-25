import NlsGge.Ramer.RamerLocalLowerBound
import NlsGge.Ramer.RamerLocalTools
import NlsGge.Ramer.RamerLemma54Eventually

/-!
# R10-P5: null preservation for the truncated maps `I + i P_k K` near `x₀`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- Null preservation on a ball for a C² field that is uniformly GL on the ball. -/
theorem nullPres_ball_of_isUnit (hs : (1 : ℝ) / 2 < s)
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M)
    (x₀ : FullWeightedHilbert c s) (r : ℝ)
    (hU : ∀ x ∈ ball x₀ r, IsUnit (1 + (hsDerivH c s hs M x).toCLM)) :
    ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (ball x₀ r ∩ TM c s hs M ⁻¹' N) = 0 := by
  intro N hN
  choose V hVo hxV _ _ hVN using fun x : ball x₀ r =>
    ramer_local_lower_bound c s hs M hM x.1 (hU x.1 x.2)
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hsub : ball x₀ r ∩ TM c s hs M ⁻¹' N ⊆
      ⋃ i ∈ T, (V i ∩ (fun y => y + inclE c s hs (M y)) ⁻¹' N) := by
    rintro y ⟨hy, hyN⟩
    have : y ∈ ⋃ i, V i := mem_iUnion.2 ⟨⟨y, hy⟩, hxV _⟩
    rw [← hTeq] at this
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 this
    exact mem_iUnion₂.2 ⟨i, hi, hyi, hyN⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff hT).2 fun i _ => hVN i N hN)

/-- P5: eventually in `k`, the truncated map `TM (P_k K)` preserves null sets on a ball. -/
theorem projField_nullPres_eventually (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (x₀ : FullWeightedHilbert c s)
    (hU : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM)) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (ball x₀ r ∩ TM c s hs (projField k K) ⁻¹' N) = 0 := by
  obtain ⟨r, hr, k₀, hk⟩ := eventually_uniform_isUnit c s hs K (hK.of_le (by norm_num)) x₀ hU
  refine ⟨r, hr, eventually_atTop.2 ⟨k₀, fun k hk0 => ?_⟩⟩
  exact nullPres_ball_of_isUnit c s hs _ (contDiff_projField k K hK) x₀ r
    (fun x hx => (hk x hx).2 k hk0)


end NlsGge.Ramer
