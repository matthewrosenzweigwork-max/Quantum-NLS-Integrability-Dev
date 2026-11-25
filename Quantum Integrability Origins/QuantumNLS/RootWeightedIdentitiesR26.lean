import QuantumNLS.RootWeightedPairingsR26
import QuantumNLS.RootEnergyMomentScalar

/-! Absolutely convergent spectral sums and the H1 energy identity. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootWeightedIdentitiesR26
open PhysicalTensor (L2T)
open RootWeightedCellsR26 RootWeightedMomentsR26 RootWeightedPairingsR26
open ProductEnergyPreparation (OneH1)
variable {L κ : ℝ} [Fact (0 < L)]

theorem physical_second (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) :
    Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u) ∧
    (∫ x : ℝ,x^2 ∂PhysicalQuantumMeasure.measure hκ u) =
      ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) := by
  rw [PhysicalL2Normalization.measure_eq_Mmeas]
  exact RootEnergyMomentScalar.scalar_energy_moment hκ u hH

theorem integral_momentum_sq (hκ : 0 < κ) (u : L2T L)
    (hp : Integrable (fun x => cellMomentum hκ u x^2) (PhysicalQuantumMeasure.measure hκ u)) :
    (∫ x,cellMomentum hκ u x^2 ∂PhysicalQuantumMeasure.measure hκ u) =
      ∑' n,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n := by
  have he := integral_map (μ := PhysicalQuantumMeasure.measure hκ u)
    (φ := cellIndex hκ u) (f := fun n => momentum L n^2)
    (measurable_cellIndex hκ u).aemeasurable Measurable.of_discrete.aestronglyMeasurable
  have hi : Integrable (fun n => momentum L n^2) (indexLaw hκ u) :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
      (measurable_cellIndex hκ u).aemeasurable).mpr hp
  calc
    _ = ∫ n,momentum L n^2 ∂indexLaw hκ u := he.symm
    _ = _ := by rw [integral_indexLaw hκ u _ hi]; simp only [mul_comm]

theorem spectral_momentum (hκ : 0 < κ) (u : L2T L)
    (hx : Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u)) :
    Summable (fun n => |momentum L n*(RootIndexedMasses.masses hκ u).1 n|) ∧
    (∫ x : ℝ,x ∂PhysicalQuantumMeasure.measure hκ u) =
      ∑' n,momentum L n*(RootIndexedMasses.masses hκ u).1 n := by
  have hp := (integrable_momentum_iff hκ u).mpr ((second_moment_equivalence hκ u).mp hx)
  have hx2 := (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hx
  have hp2 := (memLp_two_iff_integrable_sq (measurable_cellMomentum hκ u).aestronglyMeasurable).mpr hp
  have hxi : Integrable (fun x : ℝ => x) (PhysicalQuantumMeasure.measure hκ u) := hx2.integrable (by norm_num)
  have hpi := hp2.integrable (by norm_num)
  have hd : (∫ x,x-cellMomentum hκ u x ∂PhysicalQuantumMeasure.measure hκ u) = 0 := by
    calc
      _ = ∫ x,(2*κ/L)*Prop026Bound.reG hκ u x ∂PhysicalQuantumMeasure.measure hκ u :=
        integral_congr_ae (ae_displacement_boundary hκ u)
      _ = _ := by rw [integral_const_mul,(full_pairings hκ u hx).1,mul_zero]
  rw [integral_sub hxi hpi] at hd
  have himap : Integrable (momentum L) (indexLaw hκ u) :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
      (measurable_cellIndex hκ u).aemeasurable).mpr hpi
  have hsum := (integrable_indexLaw_iff hκ u _).mp himap
  have hnonneg := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1
  constructor
  · simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hnonneg _),mul_comm] using hsum
  · have he := integral_map (μ := PhysicalQuantumMeasure.measure hκ u)
      (φ := cellIndex hκ u) (f := momentum L)
      (measurable_cellIndex hκ u).aemeasurable Measurable.of_discrete.aestronglyMeasurable
    calc
      _ = ∫ x,cellMomentum hκ u x ∂PhysicalQuantumMeasure.measure hκ u := sub_eq_zero.mp hd
      _ = ∫ n,momentum L n ∂indexLaw hκ u := he.symm
      _ = _ := by rw [integral_indexLaw hκ u _ himap]; simp only [mul_comm]

theorem energy_identity (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) :
    Summable (fun n => momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) ∧
    ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) =
      (∑' n,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) +
        2*κ*‖u‖^4/L-displacement hκ u ∧
    κ*‖u‖^4/L ≤ ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) -
      (∑' n,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) ∧
    ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) -
      (∑' n,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) ≤ 2*κ*‖u‖^4/L := by
  obtain ⟨hx,hE⟩ := physical_second hκ u hH
  have hs := (second_moment_equivalence hκ u).mp hx
  have hp := (integrable_momentum_iff hκ u).mpr hs
  have hx2 := (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hx
  have hd2 := (memLp_two_iff_integrable_sq
    (measurable_id.sub (measurable_cellMomentum hκ u)).aestronglyMeasurable).mpr
    (integrable_displacement hκ u)
  have hxd : Integrable (fun x : ℝ => x*(x-cellMomentum hκ u x))
      (PhysicalQuantumMeasure.measure hκ u) := hx2.integrable_mul hd2
  have he : (∫ x : ℝ,x^2 ∂PhysicalQuantumMeasure.measure hκ u) -
      (∫ x,cellMomentum hκ u x^2 ∂PhysicalQuantumMeasure.measure hκ u) =
      2*(∫ x,x*(x-cellMomentum hκ u x) ∂PhysicalQuantumMeasure.measure hκ u) -
        displacement hκ u := by
    rw [← integral_sub hx hp,← integral_const_mul,displacement,
      ← integral_sub (hxd.const_mul 2) (integrable_displacement hκ u)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [hE,integral_momentum_sq hκ u hp,displacement_pairing hκ u hx] at he
  have heq : ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) =
      (∑' n,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) +
        2*κ*‖u‖^4/L-displacement hκ u := by linear_combination he
  obtain ⟨hd0,hd1⟩ := displacement_bound hκ u
  exact ⟨hs,heq,by nlinarith [heq],by nlinarith [heq]⟩

end QuantumNLS.RootWeightedIdentitiesR26
