import QuantumNLS.RootScalarDensityR28

/-! Uniqueness of increasing label transports, with arbitrary finite mass. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace QuantumNLS.RootScalarTransportR28
open PhysicalTensor (L2T)
open RootHilbert RootHilbertQuantiles RootScalarDensityR28
open RootWeightedCellsR26 RootWeightedMomentsR26
variable {L κ : ℝ} [Fact (0 < L)]

lemma monotone_labels_ae {m : ℝ} {f g : ℝ → ℤ}
    (hf : AEMeasurable f (volume.restrict (Ioo 0 m)))
    (hg : AEMeasurable g (volume.restrict (Ioo 0 m)))
    (hfm : MonotoneOn f (Ioo 0 m)) (hgm : MonotoneOn g (Ioo 0 m))
    (he : (volume.restrict (Ioo 0 m)).map f = (volume.restrict (Ioo 0 m)).map g) :
    f =ᵐ[volume.restrict (Ioo 0 m)] g := by
  have cross : ∀ (f g : ℝ → ℤ),
      AEMeasurable f (volume.restrict (Ioo 0 m)) →
      AEMeasurable g (volume.restrict (Ioo 0 m)) →
      MonotoneOn f (Ioo 0 m) → MonotoneOn g (Ioo 0 m) →
      (volume.restrict (Ioo 0 m)).map f = (volume.restrict (Ioo 0 m)).map g →
      ∀ n : ℤ, ∀ᵐ s ∂volume.restrict (Ioo 0 m), ¬(f s ≤ n ∧ n < g s) := by
    intro f g hf hg hfm hgm he n
    let A := {s : ℝ | s ∈ Ioo 0 m ∧ f s ≤ n ∧ n < g s}
    have hc : ∀ s ∈ A, ∀ t ∈ A, t ≤ s := by
      intro s hs t ht
      have H := congrArg (fun μ : Measure ℤ => μ (Iic n)) he
      rw [Measure.map_apply_of_aemeasurable hf measurableSet_Iic,
        Measure.map_apply_of_aemeasurable hg measurableSet_Iic] at H
      have hlow : ENNReal.ofReal t ≤ (volume.restrict (Ioo 0 m)) (f ⁻¹' Iic n) := by
        rw [Measure.restrict_apply' measurableSet_Ioo]
        calc
          _ = volume (Ioo 0 t) := by rw [Real.volume_Ioo,sub_zero]
          _ ≤ _ := measure_mono (show Ioo 0 t ⊆ f ⁻¹' Iic n ∩ Ioo 0 m from fun z hz =>
            ⟨(hfm ⟨hz.1,hz.2.trans ht.1.2⟩ ht.1 hz.2.le).trans ht.2.1,
              ⟨hz.1,hz.2.trans ht.1.2⟩⟩)
      have hupp : (volume.restrict (Ioo 0 m)) (g ⁻¹' Iic n) ≤ ENNReal.ofReal s := by
        rw [Measure.restrict_apply' measurableSet_Ioo]
        calc
          _ ≤ volume (Ioc 0 s) := measure_mono (show g ⁻¹' Iic n ∩ Ioo 0 m ⊆ Ioc 0 s from fun z hz => ⟨hz.2.1,by
            by_contra hzs
            have hsz : s ≤ z := (not_le.mp hzs).le
            exact (not_lt.mpr hz.1) (hs.2.2.trans_le (hgm hs.1 hz.2 hsz))⟩)
          _ = _ := by rw [Real.volume_Ioc,sub_zero]
      rw [H] at hlow
      exact (ENNReal.ofReal_le_ofReal_iff hs.1.1.le).mp (hlow.trans hupp)
    have hsub : A.Subsingleton := fun s hs t ht => le_antisymm (hc t ht s hs) (hc s hs t ht)
    have hz : volume A = 0 := hsub.countable.measure_zero volume
    have hza : ∀ᵐ s ∂volume, s ∉ A := measure_eq_zero_iff_ae_notMem.mp hz
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hza.mono fun s hs hI hfg => hs ⟨hI,hfg⟩
  have hfg : ∀ᵐ s ∂volume.restrict (Ioo 0 m), ∀ n : ℤ, ¬(f s ≤ n ∧ n < g s) :=
    ae_all_iff.mpr (cross f g hf hg hfm hgm he)
  have hgf : ∀ᵐ s ∂volume.restrict (Ioo 0 m), ∀ n : ℤ, ¬(g s ≤ n ∧ n < f s) :=
    ae_all_iff.mpr (cross g f hg hf hgm hfm he.symm)
  filter_upwards [hfg,hgf] with s h1 h2
  exact le_antisymm (not_lt.mp fun h => h2 (g s) ⟨le_rfl,h⟩)
    (not_lt.mp fun h => h1 (f s) ⟨le_rfl,h⟩)

def q (κ : ℝ) (u : L2T L) : ℝ → ℝ := qtl (RootDensityIdentification.dens κ u)

lemma quantile_facts (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    AEMeasurable (q κ u) (volume.restrict (Ioo 0 (‖u‖^2))) ∧
    MonotoneOn (q κ u) (Ioo 0 (‖u‖^2)) ∧
    (volume.restrict (Ioo 0 (‖u‖^2))).map (q κ u) = PhysicalQuantumMeasure.measure hκ u := by
  have H := density_hyp hκ hu
  obtain ⟨B,_,hB⟩ := hilbertHyp_exists_bound H
  have hm := density_mass hκ hu
  have hp : 0 < ∫ x,RootDensityIdentification.dens κ u x := hm ▸ sq_pos_of_pos (norm_pos_iff.mpr hu)
  refine ⟨?_,?_,?_⟩
  · simpa [q,hm] using aemeasurable_qtl H.nonneg H.integrable hB
  · simpa [q,hm] using (qtl_strictMonoOn H.nonneg H.integrable hB).monotoneOn
  · simpa [q,hm,density_measure hκ hu] using map_qtl H.nonneg H.integrable hB hp

lemma common_mass (hκ : 0 < κ) {u v : L2T L}
    (he : RootIndexedMasses.masses hκ u = RootIndexedMasses.masses hκ v) : ‖u‖^2 = ‖v‖^2 := by
  have hu := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.2.1
  have hv := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ v).2.2.2.1
  rw [← hu,← hv,he]

lemma indexLaw_eq (hκ : 0 < κ) {u v : L2T L}
    (he : RootIndexedMasses.masses hκ u = RootIndexedMasses.masses hκ v) :
    indexLaw hκ u = indexLaw hκ v := by
  haveI : IsFiniteMeasure (indexLaw hκ u) := by unfold indexLaw; infer_instance
  haveI : IsFiniteMeasure (indexLaw hκ v) := by unfold indexLaw; infer_instance
  apply Measure.ext_of_singleton
  intro n
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [indexLaw_singleton,indexLaw_singleton,he]

lemma monotone_cellIndex (hκ : 0 < κ) (u : L2T L) : Monotone (cellIndex hκ u) := by
  intro a b hab
  apply Int.floor_mono
  have hh := div_le_div_of_nonneg_right
    ((RootIndexedPhase.root_indexed_phase hκ u).2.2.2.1 hab) Real.pi_pos.le
  linarith

lemma quantile_labels (hκ : 0 < κ) {u v : L2T L} (hu : u ≠ 0) (hv : v ≠ 0)
    (he : RootIndexedMasses.masses hκ u = RootIndexedMasses.masses hκ v) :
    (fun s => cellMomentum hκ u (q κ u s)) =ᵐ[volume.restrict (Ioo 0 (‖u‖^2))]
      (fun s => cellMomentum hκ v (q κ v s)) := by
  obtain ⟨hqu,hmu,hpu⟩ := quantile_facts hκ hu
  obtain ⟨hqv,hmv,hpv⟩ := quantile_facts hκ hv
  have hm := common_mass hκ he
  rw [← hm] at hqv hmv hpv
  have he' : (volume.restrict (Ioo 0 (‖u‖^2))).map (fun s => cellIndex hκ u (q κ u s)) =
      (volume.restrict (Ioo 0 (‖u‖^2))).map (fun s => cellIndex hκ v (q κ v s)) := by
    change (volume.restrict (Ioo 0 (‖u‖^2))).map (cellIndex hκ u ∘ q κ u) =
      (volume.restrict (Ioo 0 (‖u‖^2))).map (cellIndex hκ v ∘ q κ v)
    rw [← AEMeasurable.map_map_of_aemeasurable (measurable_cellIndex hκ u).aemeasurable hqu,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_cellIndex hκ v).aemeasurable hqv,hpu,hpv]
    exact indexLaw_eq hκ he
  have hh := monotone_labels_ae
    ((measurable_cellIndex hκ u).comp_aemeasurable hqu)
    ((measurable_cellIndex hκ v).comp_aemeasurable hqv)
    ((monotone_cellIndex hκ u).comp_monotoneOn hmu)
    ((monotone_cellIndex hκ v).comp_monotoneOn hmv) he'
  exact hh.mono fun s hs => congrArg (momentum L) hs

end QuantumNLS.RootScalarTransportR28
