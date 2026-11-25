import QuantumNLS.TerraMultiRound70WeightComparison

/-! Extended quantitative shifted-moment comparison, including infinite moments. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.RootWeightedMomentsR26 QuantumNLS.TerraMultiRound60IndexedMoment
open QuantumNLS.TerraMultiRound70WeightComparison
namespace QuantumNLS.TerraMultiRound70ExtendedWeights

theorem extended_weight_comparison {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (p : ℝ) (hp : 0 ≤ p) :
    let D := 2 * Real.sqrt (κ * ‖u‖^2 / L)
    (∫⁻ t : ℝ, ENNReal.ofReal ((1+|t|)^p)
      ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ≤
      ENNReal.ofReal ((1+D)^p) * (∑' n : ℤ, ENNReal.ofReal
        ((1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) ∧
    (∑' n : ℤ, ENNReal.ofReal
        ((1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) ≤
      ENNReal.ofReal ((1+D)^p) * (∫⁻ t : ℝ, ENNReal.ofReal ((1+|t|)^p)
        ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u
  let D := 2 * Real.sqrt (κ * ‖u‖^2 / L)
  let w : ℝ → ℝ := fun t => (1+|t|)^p
  let wi : ℤ → ℝ := fun n => w (momentum L n)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hwm : Measurable (fun t : ℝ => ENNReal.ofReal (w t)) := by
    apply Measurable.ennreal_ofReal
    dsimp [w]
    fun_prop
  haveI : IsFiniteMeasure (indexLaw hκ u) := by unfold indexLaw; infer_instance
  have hmap : (∫⁻ t, ENNReal.ofReal (wi (cellIndex hκ u t)) ∂μ) =
      ∑' n : ℤ, ENNReal.ofReal (wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
    rw [← lintegral_map (Measurable.of_discrete : Measurable (fun n : ℤ => ENNReal.ofReal (wi n)))
      (measurable_cellIndex hκ u)]
    change (∫⁻ n, ENNReal.ofReal (wi n) ∂indexLaw hκ u) = _
    rw [lintegral_countable']
    apply tsum_congr
    intro n
    rw [← ENNReal.ofReal_toReal (measure_ne_top (indexLaw hκ u) {n}), indexLaw_singleton]
    rw [ENNReal.ofReal_mul (by dsimp [wi, w]; positivity)]
  have hpoint : ∀ᵐ t ∂μ, w t ≤ (1+D)^p * wi (cellIndex hκ u t) ∧
      wi (cellIndex hκ u t) ≤ (1+D)^p * w t := by
    filter_upwards [displacement_bound_ae hκ u] with t ht
    have ht' : |t - cellMomentum hκ u t| ≤ D := by simpa [D, Real.norm_eq_abs] using ht
    have ht'' : |cellMomentum hκ u t - t| ≤ D := by simpa [abs_sub_comm] using ht'
    exact ⟨shifted_weight_le _ _ _ _ hD hp ht', shifted_weight_le _ _ _ _ hD hp ht''⟩
  have hcoeff : 0 ≤ (1+D)^p := by positivity
  constructor
  · calc
      (∫⁻ t, ENNReal.ofReal (w t) ∂μ) ≤
          ∫⁻ t, ENNReal.ofReal ((1+D)^p) * ENNReal.ofReal (wi (cellIndex hκ u t)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with t ht
        rw [← ENNReal.ofReal_mul hcoeff]
        exact ENNReal.ofReal_le_ofReal ht.1
      _ = ENNReal.ofReal ((1+D)^p) *
          (∑' n : ℤ, ENNReal.ofReal (wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap]
  · calc
      (∑' n : ℤ, ENNReal.ofReal (wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) =
          ∫⁻ t, ENNReal.ofReal (wi (cellIndex hκ u t)) ∂μ := hmap.symm
      _ ≤ ∫⁻ t, ENNReal.ofReal ((1+D)^p) * ENNReal.ofReal (w t) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hpoint] with t ht
        rw [← ENNReal.ofReal_mul hcoeff]
        exact ENNReal.ofReal_le_ofReal ht.2
      _ = ENNReal.ofReal ((1+D)^p) * (∫⁻ t, ENNReal.ofReal (w t) ∂μ) := by
        rw [lintegral_const_mul _ hwm]

#print axioms extended_weight_comparison
end QuantumNLS.TerraMultiRound70ExtendedWeights
