import QuantumNLS.RootScalarBoundaryR28
import QuantumNLS.RootScalarTransportR28

/-! All-L2 uniqueness by pairing the quantile difference with the Hilbert difference. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootScalarUniqueR28
open PhysicalTensor (L2T)
open RootHilbert RootHilbertQuantiles RootScalarDensityR28 RootScalarBoundaryR28
open RootScalarTransportR28 RootWeightedCellsR26 RootWeightedMomentsR26
variable {L κ : ℝ} [Fact (0 < L)]

lemma difference_memLp (hκ : 0 < κ) {u v : L2T L} (hu : u ≠ 0) (hv : v ≠ 0)
    (he : RootIndexedMasses.masses hκ u = RootIndexedMasses.masses hκ v) :
    MemLp (fun s => q κ u s-q κ v s) 2 (volume.restrict (Ioo 0 (‖u‖^2))) := by
  obtain ⟨hqu,_,hpu⟩ := quantile_facts hκ hu
  obtain ⟨hqv,_,hpv⟩ := quantile_facts hκ hv
  have hm := common_mass hκ he
  rw [← hm] at hqv hpv
  have hdu := (memLp_two_iff_integrable_sq
    (measurable_id.sub (measurable_cellMomentum hκ u)).aestronglyMeasurable).mpr
    (integrable_displacement hκ u)
  have hdv := (memLp_two_iff_integrable_sq
    (measurable_id.sub (measurable_cellMomentum hκ v)).aestronglyMeasurable).mpr
    (integrable_displacement hκ v)
  rw [← hpu] at hdu
  rw [← hpv] at hdv
  have hu' := (memLp_map_measure_iff hdu.aestronglyMeasurable hqu).mp hdu
  have hv' := (memLp_map_measure_iff hdv.aestronglyMeasurable hqv).mp hdv
  have hae : ((id-cellMomentum hκ u) ∘ q κ u - (id-cellMomentum hκ v) ∘ q κ v) =ᵐ[
      volume.restrict (Ioo 0 (‖u‖^2))] (fun s => q κ u s-q κ v s) := by
    filter_upwards [quantile_labels hκ hu hv he] with s hs
    change (q κ u s-cellMomentum hκ u (q κ u s))-
      (q κ v s-cellMomentum hκ v (q κ v s)) = q κ u s-q κ v s
    rw [hs]
    ring
  exact (memLp_congr_ae hae).mp (hu'.sub hv')

lemma difference_boundary (hκ : 0 < κ) {u v : L2T L} (hu : u ≠ 0) (hv : v ≠ 0)
    (he : RootIndexedMasses.masses hκ u = RootIndexedMasses.masses hκ v) :
    ∀ᵐ s ∂volume.restrict (Ioo 0 (‖u‖^2)),
      q κ u s-q κ v s = (2*κ/L)*
        (hilbertPV (RootDensityIdentification.dens κ u) (q κ u s)-
          hilbertPV (RootDensityIdentification.dens κ v) (q κ v s)) := by
  obtain ⟨hqu,_,hpu⟩ := quantile_facts hκ hu
  obtain ⟨hqv,_,hpv⟩ := quantile_facts hκ hv
  have hm := common_mass hκ he
  rw [← hm] at hqv hpv
  have hbu := displacement_pv hκ hu
  have hbv := displacement_pv hκ hv
  rw [← hpu] at hbu
  rw [← hpv] at hbv
  filter_upwards [ae_of_ae_map hqu hbu,ae_of_ae_map hqv hbv,quantile_labels hκ hu hv he]
    with s hs ht heq
  nlinarith [hs,ht]

lemma uniqueness_nonzero (hκ : 0 < κ) {u v : L2T L} (hu : u ≠ 0) (hv : v ≠ 0)
    (he : RootIndexedMasses.masses hκ u = RootIndexedMasses.masses hκ v) :
    PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v := by
  let ρ := RootDensityIdentification.dens κ u
  let σ := RootDensityIdentification.dens κ v
  let μ0 := volume.restrict (Ioo 0 (‖u‖^2))
  let d := fun s => q κ u s-q κ v s
  have hd := difference_memLp hκ hu hv he
  have hm := common_mass hκ he
  have hρm := density_mass hκ hu
  have hσm := (density_mass hκ hv).trans hm.symm
  obtain ⟨hi1,hi2,hmono⟩ := root_Hilbert_quantiles (density_hyp hκ hu) (density_hyp hκ hv)
    (sq_pos_of_pos (norm_pos_iff.mpr hu)) hρm hσm hd
  have hI : (∫ s,d s^2 ∂μ0) = (2*κ/L)*
      ∫ s,d s*(hilbertPV ρ (q κ u s)-hilbertPV σ (q κ v s)) ∂μ0 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [difference_boundary hκ hu hv he] with s hs
    change d s^2 = (2*κ/L)*(d s*(hilbertPV ρ (q κ u s)-hilbertPV σ (q κ v s)))
    change d s = (2*κ/L)*(hilbertPV ρ (q κ u s)-hilbertPV σ (q κ v s)) at hs
    calc
      d s^2 = d s*d s := pow_two _
      _ = d s*((2*κ/L)*(hilbertPV ρ (q κ u s)-hilbertPV σ (q κ v s))) := congrArg (fun z => d s*z) hs
      _ = _ := by ring
  have hL : 0 < L := Fact.out
  have hzero : (∫ s,d s^2 ∂μ0) = 0 := le_antisymm
    (by rw [hI]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hmono)
    (integral_nonneg fun _ => sq_nonneg _)
  have hd0 : ∀ᵐ s ∂μ0, d s^2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hd.integrable_sq).mp hzero
  have hq : q κ u =ᵐ[μ0] q κ v := hd0.mono fun s hs => sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  have hpu := (quantile_facts hκ hu).2.2
  have hpv := (quantile_facts hκ hv).2.2
  rw [← hm] at hpv
  rw [← hpu,← hpv]
  exact Measure.map_congr hq

lemma uniqueness (hκ : 0 < κ) {u v : L2T L}
    (he : RootIndexedMasses.masses hκ u = RootIndexedMasses.masses hκ v) :
    PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v := by
  have hm := common_mass hκ he
  by_cases hu : u = 0
  · subst u
    have hv : v = 0 := by simpa using (sq_eq_zero_iff.mp (by simpa using hm.symm) : ‖v‖ = 0)
    subst v
    rfl
  by_cases hv : v = 0
  · subst v
    have hu' : u = 0 := by simpa using (sq_eq_zero_iff.mp (by simpa using hm) : ‖u‖ = 0)
    exact (hu hu').elim
  exact uniqueness_nonzero hκ hu hv he

end QuantumNLS.RootScalarUniqueR28
