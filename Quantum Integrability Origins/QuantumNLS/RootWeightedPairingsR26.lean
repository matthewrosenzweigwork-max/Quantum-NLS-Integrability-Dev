import QuantumNLS.RootWeightedCutoffsR26

/-! The constant and first principal-value pairings for the actual full-mass law. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootWeightedPairingsR26
open PhysicalTensor (L2T)
open RootWeightedCellsR26 RootWeightedMomentsR26
variable {L κ : ℝ} [Fact (0 < L)]

theorem boundary_memLp (hκ : 0 < κ) (u : L2T L) :
    MemLp (Prop026Bound.reG hκ u) 2 (PhysicalQuantumMeasure.measure hκ u) := by
  have hd := (memLp_two_iff_integrable_sq
    (measurable_id.sub (measurable_cellMomentum hκ u)).aestronglyMeasurable).mpr
    (integrable_displacement hκ u)
  have hg : (fun x => (L/(2*κ))*(x-cellMomentum hκ u x)) =ᵐ[PhysicalQuantumMeasure.measure hκ u]
      Prop026Bound.reG hκ u := by
    filter_upwards [ae_displacement_boundary hκ u] with x hx
    rw [hx]
    field_simp [hκ.ne',(Fact.out : 0 < L).ne']
  exact (memLp_congr_ae hg).mp (hd.const_mul (L/(2*κ)))

theorem unit_pairings (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hx : Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫ x,Prop026Bound.reG hκ u x ∂PhysicalQuantumMeasure.measure hκ u) = 0 ∧
    (∫ x,x*Prop026Bound.reG hκ u x ∂PhysicalQuantumMeasure.measure hκ u) = 1/2 := by
  have : IsProbabilityMeasure (PhysicalQuantumMeasure.measure hκ u) :=
    ⟨by rw [PhysicalQuantumMeasure.measure_univ,hu]; norm_num⟩
  have : NullSingletonClass (PhysicalQuantumMeasure.measure hκ u) := PhysicalUnconditionalTrace.atomless hκ u
  have hg := boundary_memLp hκ u
  have hx2 := (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hx
  exact RootWeightedCutoffsR26.pairings _ (Or.inr (Prop026Bound.boundary_bounded hκ u))
    (hg.integrable (by norm_num)) (hx2.integrable_mul hg)

theorem boundary_smul (hκ : 0 < κ) (c : ℂ) (hc : c ≠ 0) (u : L2T L) (x : ℝ) :
    Prop026Bound.reG hκ (c • u) x = ‖c‖^2*
      Prop026Bound.reG (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))) u x := by
  unfold Prop026Bound.reG Prop026Bound.theta
  rw [RootMassScaling.boundary_smul hκ c hc u]
  field_simp [hκ.ne',sq_pos_of_pos (norm_pos_iff.mpr hc) |>.ne']

theorem full_pairings (hκ : 0 < κ) (u : L2T L)
    (hx : Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫ x,Prop026Bound.reG hκ u x ∂PhysicalQuantumMeasure.measure hκ u) = 0 ∧
    (∫ x,x*Prop026Bound.reG hκ u x ∂PhysicalQuantumMeasure.measure hκ u) = ‖u‖^4/2 := by
  by_cases hu : u = 0
  · subst u
    simp [PhysicalQuantumMeasure.measure_zero]
  · let c : ℂ := (‖u‖ : ℝ)
    let v := FullMass.unitDir u
    have hc : c ≠ 0 := by
      change (‖u‖ : ℂ) ≠ 0
      exact_mod_cast (norm_ne_zero_iff.mpr hu)
    have hcn : ‖c‖ = ‖u‖ := by simp [c,Complex.norm_real]
    have hcu : c • v = u := FullMass.smul_unitDir hu
    let heff := mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hc))
    have hM : PhysicalQuantumMeasure.measure hκ u = ENNReal.ofReal (‖c‖^2) •
        PhysicalQuantumMeasure.measure heff v := by
      rw [← hcu]
      exact RootMassScaling.measure_smul hκ c hc v
    have hxv : Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure heff v) := by
      rw [hM] at hx
      exact (integrable_smul_measure ((ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hc))).ne') ENNReal.ofReal_ne_top).mp hx
    obtain ⟨h0,h1⟩ := unit_pairings heff v (FullMass.norm_unitDir hu) hxv
    have hg : ∀ x,Prop026Bound.reG hκ u x = ‖c‖^2*Prop026Bound.reG heff v x := by
      intro x
      rw [← hcu]
      exact boundary_smul hκ c hc v x
    constructor
    · simp_rw [hg]
      rw [hM,integral_smul_measure,integral_const_mul,h0]
      simp
    · have he : (fun x => x*Prop026Bound.reG hκ u x) =
          fun x => ‖c‖^2*(x*Prop026Bound.reG heff v x) := by
        funext x
        rw [hg x]
        ring
      rw [he,hM,integral_smul_measure,integral_const_mul,h1,
        ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,hcn]
      ring

theorem displacement_pairing (hκ : 0 < κ) (u : L2T L)
    (hx : Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫ x,x*(x-cellMomentum hκ u x) ∂PhysicalQuantumMeasure.measure hκ u) = κ*‖u‖^4/L := by
  calc
    _ = ∫ x,(2*κ/L)*(x*Prop026Bound.reG hκ u x) ∂PhysicalQuantumMeasure.measure hκ u := by
      apply integral_congr_ae
      filter_upwards [ae_displacement_boundary hκ u] with x hx
      rw [hx]
      ring
    _ = _ := by rw [integral_const_mul,(full_pairings hκ u hx).2]; ring

end QuantumNLS.RootWeightedPairingsR26
