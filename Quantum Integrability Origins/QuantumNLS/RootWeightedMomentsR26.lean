import QuantumNLS.RootWeightedCostR26

/-! Arbitrary-mass displacement and moment equivalence for R-A8F7B7B0. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootWeightedMomentsR26
open PhysicalTensor (L2T)
open RootWeightedCellsR26 RootWeightedCostR26
variable {L κ : ℝ} [Fact (0 < L)]

theorem lintegral_displacement_smul (hκ : 0 < κ) (c : ℂ) (hc : c ≠ 0) (u : L2T L) :
    (∫⁻ x, ENNReal.ofReal ((x-cellMomentum hκ (c • u) x)^2)
      ∂PhysicalQuantumMeasure.measure hκ (c • u)) =
    ENNReal.ofReal (‖c‖^2) *
      ∫⁻ x, ENNReal.ofReal ((x-cellMomentum
        (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u x)^2)
        ∂PhysicalQuantumMeasure.measure (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u := by
  rw [RootMassScaling.measure_smul hκ c hc u,lintegral_smul_measure]
  congr 1
  apply lintegral_congr
  intro x
  simp only [cellMomentum,cellIndex,RootIndexedPhase.theta,
    RootMassScaling.boundary_smul hκ c hc u]

theorem full_cost (hκ : 0 < κ) (u : L2T L) :
    (∫⁻ x, ENNReal.ofReal ((x-cellMomentum hκ u x)^2)
      ∂PhysicalQuantumMeasure.measure hκ u) ≤ ENNReal.ofReal (κ*‖u‖^4/L) := by
  by_cases hu : u = 0
  · subst u
    simp [PhysicalQuantumMeasure.measure_zero]
  · let c : ℂ := (‖u‖ : ℝ)
    have hc : c ≠ 0 := by
      change (‖u‖ : ℂ) ≠ 0
      exact_mod_cast (norm_ne_zero_iff.mpr hu)
    have hcn : ‖c‖ = ‖u‖ := by simp [c,Complex.norm_real]
    have he := lintegral_displacement_smul hκ c hc (FullMass.unitDir u)
    rw [show c • FullMass.unitDir u = u from FullMass.smul_unitDir hu] at he
    rw [he]
    have hb := unit_cost (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc)))
      (FullMass.unitDir u) (FullMass.norm_unitDir hu)
    calc
      _ ≤ ENNReal.ofReal (‖c‖^2)*ENNReal.ofReal ((κ*‖c‖^2)/L) :=
        by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        rw [hcn]
        ring

theorem integrable_displacement (hκ : 0 < κ) (u : L2T L) :
    Integrable (fun x => (x-cellMomentum hκ u x)^2) (PhysicalQuantumMeasure.measure hκ u) := by
  refine ⟨(measurable_id.sub (measurable_cellMomentum hκ u)).pow_const 2 |>.aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => sq_nonneg _))).mpr
    ((full_cost hκ u).trans_lt ENNReal.ofReal_lt_top)

theorem displacement_bound (hκ : 0 < κ) (u : L2T L) :
    0 ≤ displacement hκ u ∧ displacement hκ u ≤ κ*‖u‖^4/L := by
  refine ⟨displacement_nonneg hκ u,?_⟩
  have h := full_cost hκ u
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_displacement hκ u)
    (ae_of_all _ (fun _ => sq_nonneg _))] at h
  have hL : 0 < L := Fact.out
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

def indexLaw (hκ : 0 < κ) (u : L2T L) : Measure ℤ :=
  (PhysicalQuantumMeasure.measure hκ u).map (cellIndex hκ u)

theorem indexLaw_singleton (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    ((indexLaw hκ u) {n}).toReal = (RootIndexedMasses.masses hκ u).1 n := by
  rw [indexLaw,Measure.map_apply (measurable_cellIndex hκ u) (measurableSet_singleton n)]
  exact (mass_eq_fiber hκ u n).symm

theorem integrable_indexLaw_iff (hκ : 0 < κ) (u : L2T L) (f : ℤ → ℝ) :
    Integrable f (indexLaw hκ u) ↔
      Summable (fun n => (RootIndexedMasses.masses hκ u).1 n * ‖f n‖) := by
  have : IsFiniteMeasure (indexLaw hκ u) := by unfold indexLaw; infer_instance
  rw [← Measure.sum_smul_dirac (indexLaw hκ u),integrable_sum_dirac_iff
    (fun n => measure_ne_top _ _)]
  simp only [indexLaw_singleton]

theorem integral_indexLaw (hκ : 0 < κ) (u : L2T L) (f : ℤ → ℝ)
    (hf : Integrable f (indexLaw hκ u)) :
    (∫ n, f n ∂indexLaw hκ u) = ∑' n, (RootIndexedMasses.masses hκ u).1 n * f n := by
  have : IsFiniteMeasure (indexLaw hκ u) := by unfold indexLaw; infer_instance
  have hs := (integrable_indexLaw_iff hκ u f).mp hf
  rw [← Measure.sum_smul_dirac (indexLaw hκ u),integral_sum_dirac_eq_tsum
    (fun n => measure_ne_top _ _) (by simpa only [indexLaw_singleton] using hs)]
  simp only [smul_eq_mul,indexLaw_singleton]

theorem integrable_momentum_iff (hκ : 0 < κ) (u : L2T L) :
    Integrable (fun x => cellMomentum hκ u x ^ 2) (PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n => momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) := by
  have he := integrable_map_measure (μ := PhysicalQuantumMeasure.measure hκ u)
    (g := fun n => momentum L n ^ 2)
    (Measurable.of_discrete.aestronglyMeasurable)
    (measurable_cellIndex hκ u).aemeasurable
  apply he.symm.trans
  change Integrable (fun n => momentum L n^2) (indexLaw hκ u) ↔ _
  rw [integrable_indexLaw_iff]
  simp only [Real.norm_eq_abs,abs_pow,sq_abs,mul_comm]

theorem second_moment_equivalence (hκ : 0 < κ) (u : L2T L) :
    Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n => momentum L n ^ 2 * (RootIndexedMasses.masses hκ u).1 n) := by
  rw [← integrable_momentum_iff hκ u]
  have hd := (memLp_two_iff_integrable_sq
    (measurable_id.sub (measurable_cellMomentum hκ u)).aestronglyMeasurable).mpr
    (integrable_displacement hκ u)
  constructor
  · intro hx
    have hx' := (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hx
    have hp := hx'.sub hd
    simpa only [sub_sub_cancel] using hp.integrable_sq
  · intro hp
    have hp' := (memLp_two_iff_integrable_sq (measurable_cellMomentum hκ u).aestronglyMeasurable).mpr hp
    have hx := hd.add hp'
    simpa only [sub_add_cancel,id_eq] using hx.integrable_sq

end QuantumNLS.RootWeightedMomentsR26
