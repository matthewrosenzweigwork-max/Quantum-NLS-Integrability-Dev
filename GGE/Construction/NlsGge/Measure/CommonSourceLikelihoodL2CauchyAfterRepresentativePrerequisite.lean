import NlsGge.Measure.CommonSourceLikelihoodL2Definitions
import NlsGge.Measure.RealLp2RepresentativeCalculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace NlsGge.Measure

variable {lower upper : ℝ}

private theorem coefficient_bounds_from_subtype
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) :
    0 < lower ∧ (∀ j : ℕ, lower ≤ c.val j) ∧ (∀ j : ℕ, c.val j ≤ upper) := by
  exact ⟨c.property.1, (fun j => (c.property.2.2 j).1),
    (fun j => (c.property.2.2 j).2)⟩

theorem actualSourceCMSequenceEnergySummable
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)) :
    Summable (fun n : ℤ =>
      NlsGge.Pilot.cmModeWeight c n *
        ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) := by
  let xw : NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.cmModeWeight c) := x
  have hs := (NlsGge.Pilot.weightedHilbert_hasSum
    (NlsGge.Pilot.cmModeWeight c) xw).summable
  simpa [NlsGge.Measure.actualSourceCMSequence, xw] using hs

theorem actualSourceCMPartialEnergyTendsto
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)) :
    Tendsto
      (fun N : ℕ =>
        NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c N
          (NlsGge.Measure.actualSourceCMSequence c x))
      atTop
      (nhds (∑' n : ℤ,
        NlsGge.Pilot.cmModeWeight c n *
          ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2)) := by
  let f : ℤ → ℝ := fun n =>
    NlsGge.Pilot.cmModeWeight c n *
      ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2
  have hs : Summable f := by
    simpa [f] using actualSourceCMSequenceEnergySummable c x
  have hhas : HasSum f (∑' n : ℤ, f n) := hs.hasSum
  have ht := hhas.comp NlsGge.Pilot.symmetricModes_tendsto
  simpa [Function.comp_def, f, NlsGge.Measure.commonSourceLikelihoodEnergy,
    NlsGge.Measure.actualSourceCMSequence, NlsGge.Pilot.cmModeWeight,
    NlsGge.Pilot.sourceRate, NlsGge.Measure.fullWeightRate] using ht

theorem memLp_commonSourceLikelihoodReal
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ) (h : ℤ → ℂ) :
    MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  let μ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  have hmeas : Measurable (fun z : ℤ → ℂ =>
      NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z) := by
    unfold NlsGge.Measure.commonSourceLikelihoodReal
      NlsGge.Measure.commonSourceLikelihoodExponent
    fun_prop
  have hb := coefficient_bounds_from_subtype c
  have hsq := NlsGge.Measure.integrable_and_integral_sq_commonSourceLikelihoodReal
    lower upper c hb.1 hb.2.1 hb.2.2 N h
  have hsq' : Integrable
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z ^ 2) μ := by
    simpa [μ] using hsq.1
  exact (MeasureTheory.memLp_two_iff_integrable_sq
    hmeas.aestronglyMeasurable).2 hsq'

private theorem measurable_commonSourceLikelihoodReal
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N : ℕ) (h : ℤ → ℂ) :
    Measurable (fun z : ℤ → ℂ =>
      NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z) := by
  unfold NlsGge.Measure.commonSourceLikelihoodReal
    NlsGge.Measure.commonSourceLikelihoodExponent
  fun_prop

theorem normSq_commonSourceLikelihoodLpOfMemLp_sub
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (N M : ℕ) (hNM : N ≤ M) (h : ℤ → ℂ)
    (hmemM : MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c M h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hmemN : MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    ‖NlsGge.Measure.commonSourceLikelihoodLpOfMemLp
        lower upper c M h hmemM -
      NlsGge.Measure.commonSourceLikelihoodLpOfMemLp
        lower upper c N h hmemN‖ ^ 2 =
      Real.exp (NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c M h) -
        Real.exp (NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c N h) := by
  let μ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  let fM : (ℤ → ℂ) → ℝ := fun z =>
    NlsGge.Measure.commonSourceLikelihoodReal lower upper c M h z
  let fN : (ℤ → ℂ) → ℝ := fun z =>
    NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z
  let d : (ℤ → ℂ) → ℝ := fun z => fM z - fN z
  have hmeasM : AEStronglyMeasurable fM μ := by
    exact (measurable_commonSourceLikelihoodReal c M h).aestronglyMeasurable
  have hmeasN : AEStronglyMeasurable fN μ := by
    exact (measurable_commonSourceLikelihoodReal c N h).aestronglyMeasurable
  have hmeasD : AEStronglyMeasurable d μ := hmeasM.sub hmeasN
  have hb := coefficient_bounds_from_subtype c
  have hfinite :=
    NlsGge.Measure.integrable_sq_sub_and_integral_commonSourceLikelihoodReal
      lower upper c hb.1 hb.2.1 hb.2.2 N M hNM h
  have hIntD : Integrable (fun z => d z ^ 2) μ := by
    simpa [μ, d, fM, fN] using hfinite.1
  have hmemD : MeasureTheory.MemLp d 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmeasD).2 hIntD
  have hrep :
      hmemM.toLp fM - hmemN.toLp fN = hmemD.toLp d := by
    simpa [d] using NlsGge.Measure.toLp_sub_eq_of_memLp
      hmemM hmemN hmemD
  have hnorm : ‖hmemD.toLp d‖ ^ 2 = ∫ z, d z ^ 2 ∂μ := by
    simpa [d] using NlsGge.Measure.norm_sq_toLp_eq_integral_sq hmemD
  rw [show NlsGge.Measure.commonSourceLikelihoodLpOfMemLp
      lower upper c M h hmemM = hmemM.toLp fM by rfl,
    show NlsGge.Measure.commonSourceLikelihoodLpOfMemLp
      lower upper c N h hmemN = hmemN.toLp fN by rfl,
    hrep, hnorm]
  simpa [μ, d, fM, fN] using hfinite.2

theorem actualSourceCMCommonLikelihoodCauchy
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)) :
    CauchySeq (NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
      lower upper c (NlsGge.Measure.actualSourceCMSequence c x)
      (fun N => memLp_commonSourceLikelihoodReal c N
        (NlsGge.Measure.actualSourceCMSequence c x))) := by
  let hmem : ∀ N : ℕ, MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N
          (NlsGge.Measure.actualSourceCMSequence c x) z)
      2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
    fun N => memLp_commonSourceLikelihoodReal c N
      (NlsGge.Measure.actualSourceCMSequence c x)
  change CauchySeq (NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
    lower upper c (NlsGge.Measure.actualSourceCMSequence c x) hmem)
  let u := NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
    lower upper c (NlsGge.Measure.actualSourceCMSequence c x) hmem
  let F : ℕ → ℝ := fun N => Real.exp
    (NlsGge.Measure.commonSourceLikelihoodEnergy lower upper c N
      (NlsGge.Measure.actualSourceCMSequence c x))
  let L : ℝ := Real.exp (∑' n : ℤ,
    NlsGge.Pilot.cmModeWeight c n *
      ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2)
  have henergy := actualSourceCMPartialEnergyTendsto c x
  have hF : Tendsto F atTop (nhds L) := by
    have h := (Real.continuous_exp.continuousAt.tendsto.comp henergy)
    simpa [Function.comp_def, F, L] using h
  rw [Metric.cauchySeq_iff']
  intro ε hε
  let δ : ℝ := ε ^ 2 / 8
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ k : ℕ in atTop, dist (F k) L < δ :=
    hF.eventually (Metric.ball_mem_nhds L hδ)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K, ?_⟩
  intro n hn
  have hFn : dist (F n) L < δ := hK n hn
  have hFK : dist (F K) L < δ := hK K le_rfl
  have hAbsFn : |F n - L| < δ := by simpa [Real.dist_eq] using hFn
  have hAbsFK : |L - F K| < δ := by
    simpa [Real.dist_eq, abs_sub_comm] using hFK
  have hAbsDiff : |F n - F K| < 2 * δ := by
    calc
      |F n - F K| = |(F n - L) + (L - F K)| := by congr 1 <;> ring
      _ ≤ |F n - L| + |L - F K| := abs_add_le _ _
      _ < δ + δ := add_lt_add hAbsFn hAbsFK
      _ = 2 * δ := by ring
  have hdistSq : dist (u n) (u K) ^ 2 = F n - F K := by
    rw [dist_eq_norm]
    simpa [u, F, NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp] using
      normSq_commonSourceLikelihoodLpOfMemLp_sub c K n hn
        (NlsGge.Measure.actualSourceCMSequence c x) (hmem n) (hmem K)
  have hdistSqLt : dist (u n) (u K) ^ 2 < ε ^ 2 := by
    calc
      dist (u n) (u K) ^ 2 = F n - F K := hdistSq
      _ ≤ |F n - F K| := le_abs_self _
      _ < 2 * δ := hAbsDiff
      _ = ε ^ 2 / 4 := by simp [δ]; ring
      _ < ε ^ 2 := by nlinarith
  have hdist : dist (u n) (u K) < ε := by
    have hnonneg : 0 ≤ dist (u n) (u K) :=
      (show 0 ≤ dist (u n) (u K) from dist_nonneg)
    nlinarith [sq_nonneg (dist (u n) (u K) - ε)]
  exact hdist

end NlsGge.Measure
