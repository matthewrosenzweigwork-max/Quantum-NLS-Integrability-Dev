import NlsGge.Birkhoff.S03Measure38
import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted

/- I-019 PROOF01 (proof development, author). Statement: defs3 STATEMENTS/I.md "## I-019" (verbatim).
   Design abbrevs (DEFINITIONS/I.lean.md:51-52, copied byte-identically): tailWeight := NlsGge.Birkhoff.tailWeight38,
   goodGaussianSet := NlsGge.Birkhoff.Omega038.
   Reuse: NlsGge.Birkhoff.measurableSet_Omega038, fullWeightSequenceGaussian_Omega038_compl, summable_tailWeight_div38,
   tailWeight38_nonneg; NlsGge.Measure.lintegral_sequenceEnergy, lintegral_sequenceEnergy_ne_top; prob_compl_eq_zero_iff. -/

set_option autoImplicit false

open NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff MeasureTheory
open scoped ENNReal

namespace NlsGge.ThirdConsultation.I
noncomputable section

abbrev tailWeight := NlsGge.Birkhoff.tailWeight38
abbrev goodGaussianSet := NlsGge.Birkhoff.Omega038

theorem i019 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    MeasurableSet (goodGaussianSet c.val) ∧
    fullWeightSequenceGaussian c.val (goodGaussianSet c.val) = 1 ∧
    (∫⁻ z : ℤ → ℂ, sequenceEnergy (tailWeight c.val) z
      ∂fullWeightSequenceGaussian c.val) =
      ∑' n : ℤ, ENNReal.ofReal (japaneseBracket n ^ (-3 / 2 : ℝ)) ∧
    (∫⁻ z : ℤ → ℂ, sequenceEnergy (tailWeight c.val) z
      ∂fullWeightSequenceGaussian c.val) < ⊤ := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hq : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fun n => fullWeightRate_pos lower upper c.val hl hb' hu' n
  have hw : ∀ n : ℤ, 0 ≤ tailWeight c.val n :=
    fun n => tailWeight38_nonneg lower upper c.val hl hb' hu' n
  have hs : Summable (fun n : ℤ => tailWeight c.val n / fullWeightRate c.val n) :=
    summable_tailWeight_div38 lower upper c.val hl hb' hu'
  have hdiv : ∀ n : ℤ, tailWeight c.val n / fullWeightRate c.val n =
      japaneseBracket n ^ (-3 / 2 : ℝ) := by
    intro n
    unfold tailWeight NlsGge.Birkhoff.tailWeight38
    rw [mul_div_cancel_left₀ _ (hq n).ne']
    norm_num
  refine ⟨measurableSet_Omega038 lower upper c.val hl hb' hu', ?_, ?_, ?_⟩
  · exact (prob_compl_eq_zero_iff (measurableSet_Omega038 lower upper c.val hl hb' hu')).1
      (fullWeightSequenceGaussian_Omega038_compl lower upper c.val hl hb' hu')
  · unfold fullWeightSequenceGaussian
    rw [lintegral_sequenceEnergy _ _ hq hw]
    exact tsum_congr fun n => by rw [hdiv n]
  · unfold fullWeightSequenceGaussian
    exact lt_top_iff_ne_top.2 (lintegral_sequenceEnergy_ne_top _ _ hq hw hs)

end
end NlsGge.ThirdConsultation.I
