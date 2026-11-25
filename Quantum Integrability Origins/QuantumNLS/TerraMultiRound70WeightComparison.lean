import QuantumNLS.TerraMultiRound69FractionalCells

/-! Quantitative comparison of the physical and indexed shifted moments.
This is a partial result toward REG-010. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.RootWeightedMomentsR26 QuantumNLS.TerraMultiRound60IndexedMoment
open QuantumNLS.TerraMultiRound69FractionalCells
namespace QuantumNLS.TerraMultiRound70WeightComparison

theorem shifted_weight_le (x y C p : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hxy : |x-y| ≤ C) :
    (1 + |x|)^p ≤ (1+C)^p * (1 + |y|)^p := by
  have ha : |x| ≤ |y| + C := by
    have h := abs_sub_abs_le_abs_sub x y
    linarith [le_abs_self (|x| - |y|)]
  have hb : 1 + |x| ≤ (1+C) * (1 + |y|) := by
    nlinarith [abs_nonneg y, mul_nonneg hC (abs_nonneg y)]
  have h := Real.rpow_le_rpow (show 0 ≤ 1+|x| by positivity) hb hp
  rwa [Real.mul_rpow (by positivity) (by positivity)] at h

theorem physical_indexed_weight_bounds {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (p : ℝ) (hp : 0 < p)
    (hfinite : Integrable (fun t : ℝ => (1+|t|)^p)
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) :
    let D := 2 * Real.sqrt (κ * ‖u‖^2 / L)
    (∫ t : ℝ, (1+|t|)^p ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ≤
      (1+D)^p * (∑' n : ℤ, (1+|momentum L n|)^p *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) ∧
    (∑' n : ℤ, (1+|momentum L n|)^p *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) ≤
      (1+D)^p * (∫ t : ℝ, (1+|t|)^p ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u
  let D := 2 * Real.sqrt (κ * ‖u‖^2 / L)
  let w : ℝ → ℝ := fun t => (1+|t|)^p
  let wi : ℤ → ℝ := fun n => w (momentum L n)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsum := (shifted_indexed_rpow_iff hκ u p hp).mp hfinite
  have hindex : Integrable wi (indexLaw hκ u) := by
    apply (integrable_indexLaw_iff hκ u wi).mpr
    simpa only [wi, w, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (1 + |momentum L _|)^p by positivity), mul_comm] using hsum
  have hcell : Integrable (fun t => wi (cellIndex hκ u t)) μ :=
    (integrable_map_measure (μ := μ) (g := wi)
      Measurable.of_discrete.aestronglyMeasurable
      (measurable_cellIndex hκ u).aemeasurable).mp hindex
  have hmap : (∫ t, wi (cellIndex hκ u t) ∂μ) =
      ∑' n : ℤ, wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n := by
    rw [← integral_map (measurable_cellIndex hκ u).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
    change (∫ n, wi n ∂indexLaw hκ u) = _
    rw [integral_indexLaw hκ u wi hindex]
    apply tsum_congr
    intro n
    ring
  have hpoint : ∀ᵐ t ∂μ, w t ≤ (1+D)^p * wi (cellIndex hκ u t) ∧
      wi (cellIndex hκ u t) ≤ (1+D)^p * w t := by
    filter_upwards [displacement_bound_ae hκ u] with t ht
    have ht' : |t - cellMomentum hκ u t| ≤ D := by simpa [D, Real.norm_eq_abs] using ht
    have ht'' : |cellMomentum hκ u t - t| ≤ D := by simpa [abs_sub_comm] using ht'
    exact ⟨shifted_weight_le _ _ _ _ hD hp.le ht', shifted_weight_le _ _ _ _ hD hp.le ht''⟩
  constructor
  · calc
      (∫ t, w t ∂μ) ≤ ∫ t, (1+D)^p * wi (cellIndex hκ u t) ∂μ :=
        integral_mono_ae hfinite (hcell.const_mul _) (hpoint.mono fun _ h => h.1)
      _ = (1+D)^p * (∑' n : ℤ, wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
        rw [integral_const_mul, hmap]
  · calc
      (∑' n : ℤ, wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) =
          ∫ t, wi (cellIndex hκ u t) ∂μ := hmap.symm
      _ ≤ ∫ t, (1+D)^p * w t ∂μ :=
        integral_mono_ae hcell (hfinite.const_mul _) (hpoint.mono fun _ h => h.2)
      _ = (1+D)^p * (∫ t, w t ∂μ) := by rw [integral_const_mul]

#print axioms shifted_weight_le
#print axioms physical_indexed_weight_bounds
end QuantumNLS.TerraMultiRound70WeightComparison
