import QuantumNLS.TerraMultiRound68IntegerWeights

/-! The physical and indexed shifted moments have the same finiteness for
all positive real exponents.  This is only one part of REG-010. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.RootWeightedMomentsR26 QuantumNLS.TerraMultiRound60IndexedMoment
namespace QuantumNLS.TerraMultiRound69FractionalCells

theorem bounded_displacement_rpow {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : ℝ) (hp : 0 < p)
    (f g : α → ℝ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ C) :
    Integrable (fun x => ‖f x‖ ^ p) μ ↔ Integrable (fun x => ‖g x‖ ^ p) μ := by
  have hzero : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have htop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf' := integrable_norm_rpow_iff hf hzero htop
  have hg' := integrable_norm_rpow_iff hg hzero htop
  rw [ENNReal.toReal_ofReal hp.le] at hf' hg'
  rw [hf', hg']
  have hd : MemLp (fun x => f x - g x) (ENNReal.ofReal p) μ :=
    MemLp.of_bound (hf.sub hg) C hbound
  constructor
  · intro h
    have hg'' := h.sub hd
    convert hg'' using 1
    funext x
    simp
  · intro h
    have hf'' := hd.add h
    convert hf'' using 1
    funext x
    simp

theorem shifted_indexed_rpow_iff {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (p : ℝ) (hp : 0 < p) :
    Integrable (fun t : ℝ => (1 + |t|) ^ p) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1 + |momentum L n|) ^ p *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  let μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u
  let f : ℝ → ℝ := fun x => 1 + |x|
  let g : ℝ → ℝ := fun x => 1 + |cellMomentum hκ u x|
  have hf : AEStronglyMeasurable f μ := by
    have h := (aestronglyMeasurable_const (b := (1 : ℝ))).add (measurable_id.aestronglyMeasurable (μ := μ)).norm
    convert h using 1
    funext x
    simp [f, Real.norm_eq_abs]
  have hg : AEStronglyMeasurable g μ := by
    have h := (aestronglyMeasurable_const (b := (1 : ℝ))).add ((measurable_cellMomentum hκ u).aestronglyMeasurable (μ := μ)).norm
    convert h using 1
  have hb : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ 2 * Real.sqrt (κ * ‖u‖^2 / L) := by
    filter_upwards [displacement_bound_ae hκ u] with x hx
    change |(1 + |x|) - (1 + |cellMomentum hκ u x|)| ≤ _
    calc
      _ = abs (|x| - |cellMomentum hκ u x|) := by congr 1; ring
      _ ≤ |x - cellMomentum hκ u x| := abs_abs_sub_abs_le_abs_sub _ _
      _ ≤ _ := hx
  have hd := bounded_displacement_rpow μ p hp f g hf hg _ hb
  have hm := integrable_map_measure (μ := μ)
    (g := fun n : ℤ => (1 + |momentum L n|) ^ p)
    (Measurable.of_discrete.aestronglyMeasurable)
    (measurable_cellIndex hκ u).aemeasurable
  have hi := integrable_indexLaw_iff hκ u (fun n => (1 + |momentum L n|) ^ p)
  have hn : ∀ x : ℝ, 0 ≤ (1 + |x|) ^ p := fun x => Real.rpow_nonneg (by positivity) _
  have he : Integrable (fun x : ℝ => (1 + |cellMomentum hκ u x|) ^ p) μ ↔
      Summable (fun n : ℤ => (1 + |momentum L n|) ^ p *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
    change Integrable ((fun n : ℤ => (1 + |momentum L n|) ^ p) ∘ cellIndex hκ u) μ ↔ _
    rw [← hm]
    change Integrable (fun n : ℤ => (1 + |momentum L n|) ^ p) (indexLaw hκ u) ↔ _
    rw [hi]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hn _), mul_comm]
  apply Iff.trans _ he
  have hnorm : ∀ x : ℝ, abs (1 + |x|) = 1 + |x| := fun x => abs_of_nonneg (by positivity)
  simpa only [f, g, Real.norm_eq_abs, hnorm] using hd

#print axioms bounded_displacement_rpow
#print axioms shifted_indexed_rpow_iff
end QuantumNLS.TerraMultiRound69FractionalCells
