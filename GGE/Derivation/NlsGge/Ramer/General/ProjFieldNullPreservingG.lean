import Mathlib
import NlsGge.Ramer.General.RamerLocalLowerBoundG
import NlsGge.Ramer.General.RamerLocalToolsG
import NlsGge.Ramer.General.RamerLemma54EventuallyG

/-!
# R10-P5: null preservation for the truncated maps `I + i P_k K` near `x₀`, generalized (GE9)

Adapted from `NlsGge/Ramer/ProjFieldNullPreserving.lean` over a `RamerSetting S`.
Dictionary: `FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `hsDerivH c s hs ↦ S.hsDerivH`,
`TM c s hs ↦ S.TM`, `projField ↦ S.projField`, `fullWeightedSequenceGaussian c s ↦ S.γE`,
`inclE c s hs ↦ S.incl`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- Null preservation on a ball for a C² field that is uniformly GL on the ball.
(Old: `nullPres_ball_of_isUnit`.) -/
theorem nullPres_ball_of_isUnit
    (M : S.E → S.H) (hM : ContDiff ℝ 2 M)
    (x₀ : S.E) (r : ℝ)
    (hU : ∀ x ∈ ball x₀ r, IsUnit (1 + (S.hsDerivH M x).toCLM)) :
    ∀ N : Set S.E,
      S.γE N = 0 →
      S.γE (ball x₀ r ∩ S.TM M ⁻¹' N) = 0 := by
  intro N hN
  choose V hVo hxV _ _ hVN using fun x : ball x₀ r =>
    S.ramer_local_lower_bound M hM x.1 (hU x.1 x.2)
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hsub : ball x₀ r ∩ S.TM M ⁻¹' N ⊆
      ⋃ i ∈ T, (V i ∩ (fun y => y + S.incl (M y)) ⁻¹' N) := by
    rintro y ⟨hy, hyN⟩
    have : y ∈ ⋃ i, V i := mem_iUnion.2 ⟨⟨y, hy⟩, hxV _⟩
    rw [← hTeq] at this
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 this
    exact mem_iUnion₂.2 ⟨i, hi, hyi, hyN⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff hT).2 fun i _ => hVN i N hN)

/-- P5: eventually in `k`, the truncated map `TM (P_k K)` preserves null sets on a ball.
(Old: `projField_nullPres_eventually`.) -/
theorem projField_nullPres_eventually
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K)
    (x₀ : S.E)
    (hU : IsUnit (1 + (S.hsDerivH K x₀).toCLM)) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, ∀ N : Set S.E,
      S.γE N = 0 →
      S.γE (ball x₀ r ∩ S.TM (S.projField k K) ⁻¹' N) = 0 := by
  obtain ⟨r, hr, k₀, hk⟩ := S.eventually_uniform_isUnit K (hK.of_le (by norm_num)) x₀ hU
  refine ⟨r, hr, eventually_atTop.2 ⟨k₀, fun k hk0 => ?_⟩⟩
  exact S.nullPres_ball_of_isUnit _ (S.contDiff_projField k K hK) x₀ r
    (fun x hx => (hk x hx).2 k hk0)

end NlsGge.Ramer.General.RamerSetting
