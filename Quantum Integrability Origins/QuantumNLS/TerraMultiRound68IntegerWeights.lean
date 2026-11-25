import QuantumNLS.TerraMultiRound68Endpoints
import QuantumNLS.TerraMultiRound60IndexedMoment

/-! REG-010 partial: the literal shifted weights at every positive integer
order, without a claim of positive-order weighted continuity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.RootWeightedMomentsR26
open QuantumNLS.TerraMultiRound60MomentComparison QuantumNLS.TerraMultiRound60IndexedMoment
namespace QuantumNLS.TerraMultiRound68IntegerWeights

theorem shifted_power_integrable_iff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : ℕ) (hp : 0 < p)
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => (1 + |f x|)^p) μ ↔ Integrable (fun x => |f x|^p) μ := by
  have hb : ∀ᵐ x ∂μ, ‖|f x| - (1 + |f x|)‖ ≤ (1 : ℝ) := by
    apply ae_of_all
    intro x
    have he : |f x| - (1 + |f x|) = -1 := by ring
    rw [he]
    norm_num
  have hfabs : AEStronglyMeasurable (fun x => |f x|) μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have h := bounded_displacement_moments μ p hp (fun x => |f x|)
    (fun x => 1 + |f x|) hfabs (aestronglyMeasurable_const.add hfabs) 1 hb
  simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg (show 0 ≤ 1 + |f _| by positivity)] using h.symm

theorem integer_shifted_criteria (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (s : ℕ) (hs : 1 ≤ s) (u : L2T L) :
    (hsq L s (fun n => QuantumNLS.Fourier.coeff L u n) ≠ ⊤ ↔
      Integrable (fun t : ℝ => (1 + |t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
    (Integrable (fun t : ℝ => (1 + |t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1 + |momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) := by
  have hp : 0 < 2*s := by omega
  have hμ := shifted_power_integrable_iff (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)
    (2*s) hp (fun t : ℝ => t) measurable_id.aestronglyMeasurable
  have he : (fun t : ℝ => |t|^(2*s)) = (fun t : ℝ => t^(2*s)) := by
    funext t
    rw [← abs_pow, abs_of_nonneg ((even_two_mul s).pow_nonneg t)]
  rw [he] at hμ
  have hm := QuantumNLS.TerraMultiRound64Equivalences.integer_even_equivalences L κ hκ s hs u
  have hmi := lintegral_ofReal_ne_top_iff_integrable
    (μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u)
    (by fun_prop : Continuous (fun t : ℝ => t^(2*s))).aestronglyMeasurable
    (ae_of_all _ ((even_two_mul s).pow_nonneg))
  have hint := indexed_moment_equivalence hκ u (2*s) hp
  have hbase : Integrable (fun t : ℝ => t^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => |momentum L n|^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
    simpa only [he, Real.norm_eq_abs] using hint
  haveI : IsFiniteMeasure (indexLaw hκ u) := by unfold indexLaw; infer_instance
  have hshift := shifted_power_integrable_iff (indexLaw hκ u) (2*s) hp
    (momentum L) (Measurable.of_discrete.aestronglyMeasurable)
  have hi₁ := integrable_indexLaw_iff hκ u (fun n => (1 + |momentum L n|)^(2*s))
  have hi₂ := integrable_indexLaw_iff hκ u (fun n => |momentum L n|^(2*s))
  have hsum0 := hi₁.symm.trans (hshift.trans hi₂)
  have hsum : Summable (fun n : ℤ => (1 + |momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) ↔
      Summable (fun n : ℤ => |momentum L n|^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs,
      abs_of_nonneg (show 0 ≤ 1 + |momentum L _| by positivity), mul_comm] using hsum0
  exact ⟨hm.1.trans (hmi.trans hμ.symm), hμ.trans (hbase.trans hsum.symm)⟩

#print axioms shifted_power_integrable_iff
#print axioms integer_shifted_criteria
end QuantumNLS.TerraMultiRound68IntegerWeights
