import Mathlib
import NlsGge.Atomic.I.I023Core
import NlsGge.GK38.EigenvalueCompactnessStrong
import NlsGge.Birkhoff.S04Moments38

                                                                                                                 
                                                                                  
                                                                                                                      
                                                                                                            
                                                                
                                                                                                                           
                                                                                                                      
                                                                                                                    
                                                                                             
                                                                                                                
                                                                                              
                                                                                                                
                                                                                              
                                                                                                             
                                                                                                           
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I025C

/-- Each gap remainder term is continuous on the physical `L²`. -/
theorem continuous_gapRemainderTerm_L2 (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Continuous (fun u : PhysicalL2 => gapRemainderTermE02_38 W u n) := by
  set f : PhysicalL2 → ℝ → ℝ := fun u x => (W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x
    with hf
  have hfc : Continuous (Function.uncurry f) := by
    have h1 : Continuous (fun p : PhysicalL2 × ℝ => W (2 * p.2) - W (2 * Real.pi * n)) :=
      (hW.comp (continuous_const.mul continuous_snd)).sub continuous_const
    exact h1.mul NlsGge.GK38.gapHeight_joint_continuous_L2_38
  have hP : Continuous (fun p : PhysicalL2 × ℝ => ∫ x in (0 : ℝ)..p.2, f p.1 x) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous hfc
  obtain ⟨hl, hu⟩ := NlsGge.GK38.gapEndpoints_L2_continuous38 n
  have he : ∀ u : PhysicalL2, gapRemainderTermE02_38 W u n = (2 / Real.pi) *
      ((∫ x in (0 : ℝ)..actualGapUpperAllE02_38 u n, f u x) -
        ∫ x in (0 : ℝ)..actualGapLowerAllE02_38 u n, f u x) := by
    intro u
    have hi : ∀ a b : ℝ, IntervalIntegrable (f u) volume a b := fun a b =>
      (((hW.comp (continuous_const.mul continuous_id)).sub continuous_const).mul
        (continuous_actualGapHeightE02_38 u)).intervalIntegrable a b
    unfold gapRemainderTermE02_38
    rw [intervalIntegral.integral_interval_sub_left (hi 0 _) (hi 0 _)]
  refine Continuous.congr ?_ (fun u => (he u).symm)
  exact ((hP.comp (continuous_id.prodMk hu)).sub (hP.comp (continuous_id.prodMk hl))).const_mul _

/-- A real `ℤ`-series of measurable functions has a measurable (totalized) sum. -/
theorem measurable_tsum_real {α : Type*} [MeasurableSpace α] (f : ℤ → α → ℝ)
    (hf : ∀ n, Measurable (f n)) : Measurable (fun a => ∑' n, f n a) := by
  classical
  set S : Set α := {a | ∑' n, (‖f n a‖₊ : ℝ≥0∞) ≠ ⊤} with hSdef
  have hS : MeasurableSet S :=
    (Measurable.ennreal_tsum (fun n => (hf n).nnnorm.coe_nnreal_ennreal))
      (measurableSet_singleton (⊤ : ℝ≥0∞)).compl
  have hSum : ∀ a, a ∈ S ↔ Summable (fun n => f n a) := by
    intro a
    rw [hSdef, Set.mem_setOf_eq, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    simp only [coe_nnnorm]
    exact summable_norm_iff
  refine measurable_of_tendsto_metrizable (f := fun M : ℕ => fun a : α =>
    if a ∈ S then ∑ n ∈ stdExh38 M, f n a else 0) (fun M => ?_) ?_
  · exact Measurable.ite hS (Finset.measurable_sum _ (fun n _ => hf n)) measurable_const
  · rw [tendsto_pi_nhds]
    intro a
    by_cases ha : a ∈ S
    · simp only [ha, ↓reduceIte]
      exact ((hSum a).1 ha).hasSum.comp isExhaustion_stdExh38.tendsto_atTop
    · simp only [ha, ↓reduceIte]
      rw [tsum_eq_zero_of_not_summable (fun h => ha ((hSum a).2 h))]
      exact tendsto_const_nhds

theorem measurable_remainderForWeight (W : ℝ → ℝ) (hW : Continuous W) :
    Measurable (remainderForWeight W) := by
  unfold remainderForWeight
  exact measurable_tsum_real (fun n u => gapRemainderTermE02_38 W u n)
    (fun n => (continuous_gapRemainderTerm_L2 W hW n).measurable)

theorem i025_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    let W := weight c.val
    let γ := fullWeightSequenceGaussian c.val
    Measurable physicalOfSequence ∧ Measurable (sequenceRemainder W) ∧
    Integrable (fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z)) γ ∧
    (∀ᵐ z ∂γ, sequenceRemainder W z = remainder38 c.val (physicalOfSequence z) ∧
      0 < Real.exp (-sequenceRemainder W z) ∧ Real.exp (-sequenceRemainder W z) ≤ 1) ∧
    0 < limitNormalizer W ∧ limitNormalizer W ≤ 1 ∧
    weightedSequenceLaw W = γ.withDensity
      (fun z => ENNReal.ofReal (Real.exp (-sequenceRemainder W z) / limitNormalizer W)) ∧
    IsProbabilityMeasure (weightedSequenceLaw W) ∧ IsProbabilityMeasure (physicalLaw W) ∧
    weightedSequenceLaw W ≪ γ ∧ γ ≪ weightedSequenceLaw W ∧
    (∀ᵐ z ∂weightedSequenceLaw W, z ∈ goodGaussianSet c.val) := by
  dsimp only
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hW := weight_continuous38 hl hb' hu'
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hRm : Measurable (sequenceRemainder (weight c.val)) := by
    unfold sequenceRemainder
    exact measurable_const.max ((measurable_remainderForWeight _ hW).comp hPm)
  have h0 : ∀ z, 0 ≤ sequenceRemainder (weight c.val) z := fun z => le_max_left _ _
  have hle1 : ∀ z, Real.exp (-sequenceRemainder (weight c.val) z) ≤ 1 := fun z =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 (h0 z))
  have hZdef : limitNormalizer (weight c.val) =
      ∫ z, Real.exp (-sequenceRemainder (weight c.val) z) ∂(fullWeightSequenceGaussian c.val) := rfl
  have hLaw : weightedSequenceLaw (weight c.val) = (fullWeightSequenceGaussian c.val).withDensity
      (fun z => ENNReal.ofReal (Real.exp (-sequenceRemainder (weight c.val) z) /
        limitNormalizer (weight c.val))) := rfl
  obtain ⟨hZpos, hZle⟩ := exp_neg_integral_pos_le_one38 (fullWeightSequenceGaussian c.val)
    (sequenceRemainder (weight c.val)) hRm h0
  rw [← hZdef] at hZpos hZle
  have hprob : IsProbabilityMeasure (weightedSequenceLaw (weight c.val)) := by
    rw [hLaw, hZdef]
    exact isProbabilityMeasure_withDensity_exp_neg38 _ _ hRm h0
  have hdm : Measurable (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-sequenceRemainder (weight c.val) z) /
      limitNormalizer (weight c.val))) :=
    ((Real.measurable_exp.comp hRm.neg).div_const _).ennreal_ofReal
  have hac : weightedSequenceLaw (weight c.val) ≪ fullWeightSequenceGaussian c.val := by
    rw [hLaw]; exact withDensity_absolutelyContinuous _ _
  have hΩ := ae_mem_Omega038 lower upper c.val hl hb' hu'
  refine ⟨hPm, hRm, ?_, ?_, hZpos, hZle, hLaw, hprob, ?_, hac, ?_, hac.ae_le hΩ⟩
  · exact Integrable.of_bound (Real.measurable_exp.comp hRm.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hle1 z)
  · filter_upwards [hΩ] with z hz
    have h24 := (NlsGge.ThirdConsultation.I023C.i024_of Bk hB lower upper c z hz).2.2.1
    refine ⟨?_, Real.exp_pos _, hle1 z⟩
    rw [h24, NlsGge.ThirdConsultation.I017C.remainderForWeight_eq c.val hW]
  · unfold physicalLaw
    exact (Measure.isProbabilityMeasure_map_iff hPm.aemeasurable).2 hprob
  · rw [hLaw]
    refine withDensity_absolutelyContinuous' hdm.aemeasurable (Filter.Eventually.of_forall fun z => ?_)
    exact (ENNReal.ofReal_pos.2 (div_pos (Real.exp_pos _) hZpos)).ne'

end NlsGge.ThirdConsultation.I025C
