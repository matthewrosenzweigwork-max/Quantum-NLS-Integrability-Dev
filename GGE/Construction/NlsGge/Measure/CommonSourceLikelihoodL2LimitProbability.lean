import NlsGge.Measure.CommonSourceLikelihoodL2Limit
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace NlsGge.Measure

variable {lower upper : ℝ}

/-- The actual CM likelihood limit is nonnegative and has mass one. This
identifies a probability density in `L²`; it does not yet assert the translated
sequence law is its `withDensity` measure. -/
theorem exists_actualSourceCMCommonLikelihoodL2Limit_probability
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert
      (NlsGge.Pilot.cmModeWeight c)) :
    ∃ L : MeasureTheory.Lp ℝ 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto
        (NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp
          lower upper c (NlsGge.Measure.actualSourceCMSequence c x)
          (fun N => NlsGge.Measure.memLp_commonSourceLikelihoodReal c N
            (NlsGge.Measure.actualSourceCMSequence c x)))
        atTop (nhds L) ∧
      (∀ᵐ z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val, 0 ≤ L z) ∧
      (∫ z : ℤ → ℂ, L z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) = 1 := by
  obtain ⟨L, hL⟩ :=
    NlsGge.Measure.exists_actualSourceCMCommonLikelihoodL2Limit c x
  let μ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  let h : ℤ → ℂ := NlsGge.Measure.actualSourceCMSequence c x
  let hmem : ∀ N : ℕ, MeasureTheory.MemLp
      (fun z : ℤ → ℂ =>
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c N h z)
      2 μ := fun N => NlsGge.Measure.memLp_commonSourceLikelihoodReal c N h
  let u : ℕ → MeasureTheory.Lp ℝ 2 μ :=
    NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp lower upper c h hmem
  have hconv : Tendsto u atTop (nhds L) := by
    simpa [u, hmem, h, μ] using hL
  have hmeasure :
      MeasureTheory.TendstoInMeasure μ (fun n => u n) atTop L :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hconv
  obtain ⟨ns, hns, hseq⟩ := hmeasure.exists_seq_tendsto_ae
  have hrepr : ∀ n : ℕ, ∀ᵐ z ∂μ,
      u n z = NlsGge.Measure.commonSourceLikelihoodReal lower upper c n h z := by
    intro n
    filter_upwards [(hmem n).coeFn_toLp] with z hz
    simpa [u, NlsGge.Measure.commonSourceLikelihoodLpSequenceOfMemLp,
      NlsGge.Measure.commonSourceLikelihoodLpOfMemLp] using hz
  have hnonneg : ∀ᵐ z ∂μ, 0 ≤ L z := by
    filter_upwards [hseq, ae_all_iff.mpr hrepr] with z hz hvalues
    apply isClosed_Ici.mem_of_tendsto hz
    filter_upwards with i
    rw [hvalues (ns i)]
    exact Real.exp_nonneg _
  let oneMem : MeasureTheory.MemLp (fun _ : ℤ → ℂ => (1 : ℝ)) 2 μ :=
    MeasureTheory.memLp_const (1 : ℝ)
  let oneLp : MeasureTheory.Lp ℝ 2 μ := oneMem.toLp _
  have hone : ∀ᵐ z ∂μ, oneLp z = (1 : ℝ) := by
    simpa [oneLp, oneMem] using
      (MeasureTheory.MemLp.coeFn_toLp oneMem)
  have hfiniteIntegral (n : ℕ) :
      (∫ z : ℤ → ℂ,
        NlsGge.Measure.commonSourceLikelihoodReal lower upper c n h z ∂μ) = 1 := by
    have hb := NlsGge.Measure.integrable_and_integral_commonSourceLikelihoodReal
      lower upper c c.property.1 (fun j => (c.property.2.2 j).1)
      (fun j => (c.property.2.2 j).2) n h
    simpa [μ] using hb.2
  have hinnerSeq (n : ℕ) : inner ℝ (u n) oneLp = 1 := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ z : ℤ → ℂ, inner ℝ (u n z) (oneLp z) ∂μ) =
          ∫ z : ℤ → ℂ,
            NlsGge.Measure.commonSourceLikelihoodReal lower upper c n h z ∂μ := by
              apply integral_congr_ae
              filter_upwards [hrepr n, hone] with z hz hzero
              simp [hz, hzero]
      _ = 1 := hfiniteIntegral n
  have hinnerLimit :
      Tendsto (fun n : ℕ => inner ℝ (u n) oneLp) atTop
        (nhds (inner ℝ L oneLp)) := by
    exact hconv.inner (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => oneLp) atTop (nhds oneLp))
  have hinnerOne : inner ℝ L oneLp = 1 := by
    have hseqOne : Tendsto
        (fun n : ℕ => inner ℝ (u n) oneLp) atTop (nhds 1) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
      funext n
      exact hinnerSeq n
    exact tendsto_nhds_unique hinnerLimit hseqOne
  have hlimitIntegral :
      inner ℝ L oneLp = ∫ z : ℤ → ℂ, L z ∂μ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hone] with z hz
    simp [hz]
  refine ⟨L, hconv, ?_, ?_⟩
  · simpa [μ] using hnonneg
  · rw [← hlimitIntegral, hinnerOne]

end NlsGge.Measure
