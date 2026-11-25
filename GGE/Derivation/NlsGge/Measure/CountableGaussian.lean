import NlsGge.Measure.FourierGaussian
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

/-- Actual countable product law with centered proper complex Gaussian factors. -/
def countableComplexGaussian (q : ℤ → ℝ) : MeasureTheory.Measure (ℤ → ℂ) :=
  Measure.infinitePi (fun n : ℤ => complexGaussian (q n))

instance countableComplexGaussian_probability (q : ℤ → ℝ) :
    IsProbabilityMeasure (countableComplexGaussian q) := by
  unfold countableComplexGaussian
  infer_instance

/-- Full entire source rate series, with every integer coordinate retained. -/
def fullWeightSequenceGaussian (c : ℕ → ℝ) : MeasureTheory.Measure (ℤ → ℂ) :=
  countableComplexGaussian (fullWeightRate c)

instance fullWeightSequenceGaussian_probability (c : ℕ → ℝ) :
    IsProbabilityMeasure (fullWeightSequenceGaussian c) := by
  unfold fullWeightSequenceGaussian
  infer_instance

lemma countableComplexGaussian_map_eval (q : ℤ → ℝ) (n : ℤ) :
    (countableComplexGaussian q).map (fun z : ℤ → ℂ => z n) = complexGaussian (q n) :=
  Measure.infinitePi_map_eval (fun k : ℤ => complexGaussian (q k)) n

lemma integrable_countableComplexGaussian_sqNorm (q : ℤ → ℝ) (n : ℤ) :
    Integrable (fun z : ℤ → ℂ => ‖z n‖ ^ 2) (countableComplexGaussian q) := by
  have h := (measurePreserving_eval_infinitePi
    (fun k : ℤ => complexGaussian (q k)) n).integrable_comp_of_integrable
      (integrable_complexGaussian_sqNorm (q n))
  simpa only [countableComplexGaussian, Function.comp_def, Function.eval] using h

lemma integral_countableComplexGaussian_sqNorm (q : ℤ → ℝ)
    (hq : ∀ n : ℤ, 0 < q n) (n : ℤ) :
    (∫ z : ℤ → ℂ, ‖z n‖ ^ 2 ∂countableComplexGaussian q) = 1 / q n := by
  have _hi := integrable_countableComplexGaussian_sqNorm q n
  have h := integral_complexGaussian_sqNorm (q n) (hq n)
  rw [← countableComplexGaussian_map_eval q n] at h
  rw [integral_map (measurable_pi_apply n).aemeasurable (by fun_prop)] at h
  exact h

/-- Actual finite signed-mode marginal, with the true zero mode retained. -/
lemma countableComplexGaussian_map_modes (N : ℕ) (q : ℤ → ℝ) :
    (countableComplexGaussian q).map
      (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (NlsGge.Pilot.modeIndex N i)) =
      fourierPlaneGaussian N q := by
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun n : ℤ => complexGaussian (q n)) (NlsGge.Pilot.modeIndex_injective N)
  simpa only [countableComplexGaussian, fourierPlaneGaussian, finiteComplexGaussian,
    Measure.infinitePi_eq_pi] using h

lemma fullWeightSequenceGaussian_map_eval (c : ℕ → ℝ) (n : ℤ) :
    (fullWeightSequenceGaussian c).map (fun z : ℤ → ℂ => z n) =
      complexGaussian (fullWeightRate c n) :=
  countableComplexGaussian_map_eval (fullWeightRate c) n

lemma integrable_fullWeightSequenceGaussian_sqNorm (c : ℕ → ℝ) (n : ℤ) :
    Integrable (fun z : ℤ → ℂ => ‖z n‖ ^ 2) (fullWeightSequenceGaussian c) :=
  integrable_countableComplexGaussian_sqNorm (fullWeightRate c) n

lemma integral_fullWeightSequenceGaussian_sqNorm (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (n : ℤ) :
    (∫ z : ℤ → ℂ, ‖z n‖ ^ 2 ∂fullWeightSequenceGaussian c) = 1 / fullWeightRate c n :=
  integral_countableComplexGaussian_sqNorm (fullWeightRate c)
    (fun k => fullWeightRate_pos lower upper c hlower hbound hupper k) n

lemma fullWeightSequenceGaussian_map_modes (N : ℕ) (c : ℕ → ℝ) :
    (fullWeightSequenceGaussian c).map
      (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (NlsGge.Pilot.modeIndex N i)) =
      fullWeightFourierGaussian N c :=
  countableComplexGaussian_map_modes N (fullWeightRate c)

end NlsGge.Measure

namespace NlsGge.Measure

/-- Extended nonnegative weighted square energy, retaining infinity. -/
def sequenceEnergy (w : ℤ → ℝ) (z : ℤ → ℂ) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (w n * ‖z n‖ ^ 2)

lemma measurable_sequenceEnergy (w : ℤ → ℝ) : Measurable (sequenceEnergy w) := by
  unfold sequenceEnergy
  exact Measurable.tsum (fun n => by fun_prop)

lemma lintegral_sequenceEnergy (q w : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (hw : ∀ n : ℤ, 0 ≤ w n) :
    (∫⁻ z : ℤ → ℂ, sequenceEnergy w z ∂countableComplexGaussian q) =
      ∑' n : ℤ, ENNReal.ofReal (w n / q n) := by
  have hm : ∀ n : ℤ, Measurable
      (fun z : ℤ → ℂ => ENNReal.ofReal (w n * ‖z n‖ ^ 2)) := fun n =>
    (((measurable_pi_apply n).norm.pow_const 2).const_mul (w n)).ennreal_ofReal
  unfold sequenceEnergy
  rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
  apply tsum_congr
  intro n
  have hi : Integrable (fun z : ℤ → ℂ => w n * ‖z n‖ ^ 2)
      (countableComplexGaussian q) :=
    (integrable_countableComplexGaussian_sqNorm q n).const_mul (w n)
  have hn : ∀ z : ℤ → ℂ, 0 ≤ w n * ‖z n‖ ^ 2 :=
    fun z => mul_nonneg (hw n) (sq_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn),
    integral_const_mul, integral_countableComplexGaussian_sqNorm q hq n]
  congr 1
  ring

lemma sequenceEnergy_ne_top_iff (w : ℤ → ℝ) (hw : ∀ n : ℤ, 0 ≤ w n) (z : ℤ → ℂ) :
    sequenceEnergy w z ≠ ⊤ ↔ Summable (fun n : ℤ => w n * ‖z n‖ ^ 2) := by
  constructor
  · intro hz
    have hs := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp
      (show (∑' n : ℤ, ((w n * ‖z n‖ ^ 2).toNNReal : ℝ≥0∞)) ≠ ⊤ from hz)
    exact hs.congr (fun n => Real.coe_toNNReal _ (mul_nonneg (hw n) (sq_nonneg _)))
  · intro hs
    exact hs.tsum_ofReal_ne_top

lemma measurableSet_sequenceSummable (w : ℤ → ℝ) (hw : ∀ n : ℤ, 0 ≤ w n) :
    MeasurableSet {z : ℤ → ℂ | Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)} := by
  simp_rw [← sequenceEnergy_ne_top_iff w hw]
  exact (measurable_sequenceEnergy w) ((measurableSet_singleton (⊤ : ℝ≥0∞)).compl)

lemma lintegral_sequenceEnergy_ne_top (q w : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (hw : ∀ n : ℤ, 0 ≤ w n) (hsum : Summable (fun n : ℤ => w n / q n)) :
    (∫⁻ z : ℤ → ℂ, sequenceEnergy w z ∂countableComplexGaussian q) ≠ ⊤ := by
  rw [lintegral_sequenceEnergy q w hq hw]
  exact hsum.tsum_ofReal_ne_top

lemma ae_sequenceEnergy_lt_top (q w : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (hw : ∀ n : ℤ, 0 ≤ w n) (hsum : Summable (fun n : ℤ => w n / q n)) :
    ∀ᵐ z ∂countableComplexGaussian q, sequenceEnergy w z < ⊤ :=
  ae_lt_top (measurable_sequenceEnergy w) (lintegral_sequenceEnergy_ne_top q w hq hw hsum)

lemma ae_sequenceSummable (q w : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (hw : ∀ n : ℤ, 0 ≤ w n) (hsum : Summable (fun n : ℤ => w n / q n)) :
    ∀ᵐ z ∂countableComplexGaussian q, Summable (fun n : ℤ => w n * ‖z n‖ ^ 2) := by
  filter_upwards [ae_sequenceEnergy_lt_top q w hq hw hsum] with z hz
  exact (sequenceEnergy_ne_top_iff w hw z).1 hz.ne

lemma integrable_sequenceEnergy_toReal (q w : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (hw : ∀ n : ℤ, 0 ≤ w n) (hsum : Summable (fun n : ℤ => w n / q n)) :
    Integrable (fun z : ℤ → ℂ => (sequenceEnergy w z).toReal) (countableComplexGaussian q) :=
  integrable_toReal_of_lintegral_ne_top (measurable_sequenceEnergy w).aemeasurable
    (lintegral_sequenceEnergy_ne_top q w hq hw hsum)

lemma integral_sequenceEnergy_toReal (q w : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (hw : ∀ n : ℤ, 0 ≤ w n) (hsum : Summable (fun n : ℤ => w n / q n)) :
    (∫ z : ℤ → ℂ, (sequenceEnergy w z).toReal ∂countableComplexGaussian q) =
      ∑' n : ℤ, w n / q n := by
  have _hi := integrable_sequenceEnergy_toReal q w hq hw hsum
  rw [integral_toReal (measurable_sequenceEnergy w).aemeasurable
    (ae_sequenceEnergy_lt_top q w hq hw hsum), lintegral_sequenceEnergy q w hq hw,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => div_nonneg (hw n) (hq n).le) hsum,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => div_nonneg (hw n) (hq n).le))]

end NlsGge.Measure
