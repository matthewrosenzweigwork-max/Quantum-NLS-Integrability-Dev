import QuantumNLS.TerraMultiRound70ExtendedWeights

/-! REG-010: physical-to-indexed weighted tail localization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.RootWeightedMomentsR26 QuantumNLS.TerraMultiRound60IndexedMoment
open QuantumNLS.TerraMultiRound70WeightComparison
namespace QuantumNLS.TerraMultiRound71Tail

/-- Confinement transfers a weighted indexed tail to a physical tail.  This is
an inequality of extended nonnegative quantities, with no moment hypothesis. -/
theorem indexed_tail_le_physical {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (p R : ℝ) (hp : 0 ≤ p) :
    let D := 2 * Real.sqrt (κ * ‖u‖^2 / L)
    (∑' n : ℤ, if R < |momentum L n| then ENNReal.ofReal
      ((1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) else 0) ≤
    ENNReal.ofReal ((1+D)^p) *
      ∫⁻ t : ℝ, if R-D < |t| then ENNReal.ofReal ((1+|t|)^p) else 0
        ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u := by
  classical
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u
  let D := 2 * Real.sqrt (κ * ‖u‖^2 / L)
  let w : ℝ → ℝ := fun t => (1+|t|)^p
  let wi : ℤ → ℝ := fun n => w (momentum L n)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  haveI : IsFiniteMeasure (indexLaw hκ u) := by unfold indexLaw; infer_instance
  have hmap : (∫⁻ t, if R < |momentum L (cellIndex hκ u t)| then
        ENNReal.ofReal (wi (cellIndex hκ u t)) else 0 ∂μ) =
      ∑' n : ℤ, if R < |momentum L n| then ENNReal.ofReal
        (wi n * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) else 0 := by
    rw [← lintegral_map (Measurable.of_discrete : Measurable (fun n : ℤ =>
      if R < |momentum L n| then ENNReal.ofReal (wi n) else 0))
      (measurable_cellIndex hκ u)]
    change (∫⁻ n, (if R < |momentum L n| then ENNReal.ofReal (wi n) else 0)
      ∂indexLaw hκ u) = _
    rw [lintegral_countable']
    apply tsum_congr
    intro n
    rw [← ENNReal.ofReal_toReal (measure_ne_top (indexLaw hκ u) {n}), indexLaw_singleton]
    split_ifs with h
    · exact (ENNReal.ofReal_mul (by dsimp [wi, w]; positivity)).symm
    · simp
  calc
    _ = ∫⁻ t, if R < |momentum L (cellIndex hκ u t)| then
        ENNReal.ofReal (wi (cellIndex hκ u t)) else 0 ∂μ := hmap.symm
    _ ≤ ∫⁻ t, ENNReal.ofReal ((1+D)^p) *
        (if R-D < |t| then ENNReal.ofReal (w t) else 0) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [displacement_bound_ae hκ u] with t ht
      have ht' : |t - cellMomentum hκ u t| ≤ D := by simpa [D, Real.norm_eq_abs] using ht
      have ht'' : |cellMomentum hκ u t - t| ≤ D := by simpa [abs_sub_comm] using ht'
      have hdist : |cellMomentum hκ u t| ≤ |t| + D := by
        have h := abs_sub_abs_le_abs_sub (cellMomentum hκ u t) t
        linarith [le_abs_self (|cellMomentum hκ u t| - |t|)]
      have hw := shifted_weight_le (cellMomentum hκ u t) t D p hD hp ht''
      have hn : 0 ≤ (1+D)^p := by positivity
      by_cases h : R < |momentum L (cellIndex hκ u t)|
      · have htai : R-D < |t| := by
          change |momentum L (cellIndex hκ u t)| ≤ |t| + D at hdist
          linarith
        simp only [if_pos h, if_pos htai, ← ENNReal.ofReal_mul hn]
        apply ENNReal.ofReal_le_ofReal
        simpa [wi, w, cellMomentum] using hw
      · simp [h]
    _ = ENNReal.ofReal ((1+D)^p) *
      ∫⁻ t, if R-D < |t| then ENNReal.ofReal (w t) else 0 ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- A common displacement bound gives the same tail estimate uniformly over a
family.  The bound is explicit so that the later continuity argument can use
one cutoff for the entire family. -/
theorem indexed_tail_le_common_bound {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (p R B : ℝ) (hp : 0 ≤ p)
    (hB : 2 * Real.sqrt (κ * ‖u‖^2 / L) ≤ B) :
    (∑' n : ℤ, if R+B < |momentum L n| then ENNReal.ofReal
      ((1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) else 0) ≤
    ENNReal.ofReal ((1+B)^p) *
      ∫⁻ t : ℝ, if R < |t| then ENNReal.ofReal ((1+|t|)^p) else 0
        ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u := by
  let D := 2 * Real.sqrt (κ * ‖u‖^2 / L)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb : D ≤ B := hB
  have hc : ENNReal.ofReal ((1+D)^p) ≤ ENNReal.ofReal ((1+B)^p) := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (by linarith) (by linarith) hp
  have hi : (∫⁻ t : ℝ, if R+B-D < |t| then ENNReal.ofReal ((1+|t|)^p) else 0
      ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ≤
      ∫⁻ t : ℝ, if R < |t| then ENNReal.ofReal ((1+|t|)^p) else 0
      ∂QuantumNLS.PhysicalQuantumMeasure.measure hκ u := by
    apply lintegral_mono
    intro t
    dsimp only
    split_ifs with h₁ h₂
    · exact le_rfl
    · exfalso; linarith
    · exact zero_le
    · exact le_rfl
  exact le_trans (indexed_tail_le_physical hκ u p (R+B) hp) (mul_le_mul' hc hi)

#print axioms indexed_tail_le_physical
#print axioms indexed_tail_le_common_bound
end QuantumNLS.TerraMultiRound71Tail
