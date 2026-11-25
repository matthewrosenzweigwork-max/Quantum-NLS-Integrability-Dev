import QuantumNLS.RootWeightedVarianceR26

/-! The single-index characterization, including its physical plane-wave convention. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.RootWeightedPlaneR26
open PhysicalTensor (L2T)
open QuantumNLS.Fourier ProductEnergyPreparation ChargeEnergy
open RootWeightedCellsR26 RootWeightedMomentsR26 RootWeightedIdentitiesR26
open RootWeightedPhysicalR26 RootWeightedFirstR26 RootWeightedVarianceR26
variable {L κ : ℝ} [hLf : Fact (0 < L)]

def AllMassAt (hκ : 0 < κ) (u : L2T L) (k : ℤ) : Prop :=
  ∀ n : ℤ,(RootIndexedMasses.masses hκ u).1 n = if n=k then ‖u‖^2 else 0

theorem ae_single_index (hκ : 0 < κ) (u : L2T L) (k : ℤ) (hI : AllMassAt hκ u k) :
    ∀ᵐ x ∂PhysicalQuantumMeasure.measure hκ u,cellIndex hκ u x = k := by
  have hset : MeasurableSet (cellIndex hκ u ⁻¹' {k}) :=
    (measurableSet_singleton k).preimage (measurable_cellIndex hκ u)
  have he : PhysicalQuantumMeasure.measure hκ u (cellIndex hκ u ⁻¹' {k}) =
      PhysicalQuantumMeasure.measure hκ u univ := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [← mass_eq_fiber,hI k,PhysicalQuantumMeasure.measure_univ,
      ENNReal.toReal_ofReal (sq_nonneg _)]
    simp
  exact (ae_mem_iff_measure_eq hset.nullMeasurableSet).mpr he

theorem single_index_plane (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) (k : ℤ)
    (hI : AllMassAt hκ u k) : ∃ c : ℂ,u = c • modeLp L k := by
  obtain ⟨hx,hE⟩ := physical_second hκ u hH
  have hxi : Integrable (fun x : ℝ => x) (PhysicalQuantumMeasure.measure hκ u) :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hx).integrable (by norm_num)
  have hP : fourierMomentum u = freq L k*‖u‖^2 := by
    rw [← physical_first_moment hκ u hH,(spectral_momentum hκ u hx).2]
    simp [AllMassAt] at hI
    simp [hI,momentum,freq]
  have hIeq : ∀ n : ℤ,(RootIndexedMasses.masses hκ u).1 n = if n=k then ‖u‖^2 else 0 := hI
  have hW : (∑' n : ℤ,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) =
      freq L k^2*‖u‖^2 := by
    simp only [hIeq,mul_ite,mul_zero]
    simp [momentum,freq]
  have ha : ∀ᵐ x ∂PhysicalQuantumMeasure.measure hκ u,cellMomentum hκ u x = freq L k := by
    filter_upwards [ae_single_index hκ u k hI] with x hx
    simp only [cellMomentum,hx,momentum,freq]
  have hD : displacement hκ u = energyH1 κ (u : AddCircle L → ℂ)-freq L k^2*‖u‖^2 := by
    unfold displacement
    calc
      _ = ∫ x : ℝ,(x-freq L k)^2 ∂PhysicalQuantumMeasure.measure hκ u :=
        integral_congr_ae (ha.mono fun x hx => by rw [hx])
      _ = energyH1 κ (u : AddCircle L → ℂ)-freq L k^2*‖u‖^2 := by
        have hmul : Integrable (fun x : ℝ => 2*freq L k*x) (PhysicalQuantumMeasure.measure hκ u) :=
          hxi.const_mul _
        have hsub : Integrable (fun x : ℝ => x^2-2*freq L k*x) (PhysicalQuantumMeasure.measure hκ u) := hx.sub hmul
        have he : (fun x : ℝ => (x-freq L k)^2) = fun x => x^2-2*freq L k*x+freq L k^2 :=
          funext fun _ => by ring
        rw [he,integral_add hsub (integrable_const _),integral_sub hx hmul,
          integral_const_mul,hE,physical_first_moment hκ u hH,hP,integral_const]
        simp only [smul_eq_mul,measureReal_def,PhysicalQuantumMeasure.measure_univ,
          ENNReal.toReal_ofReal (sq_nonneg _)]
        ring
  have hEnergy := (energy_identity hκ u hH).2.1
  rw [hW] at hEnergy
  have hPlaneEnergy : energyH1 κ (u : AddCircle L → ℂ) =
      freq L k^2*‖u‖^2+κ*‖u‖^4/L := by linear_combination (1/2)*hEnergy-(1/2)*hD
  have hbal : variance u (freq L k)+κ*(quartic (u : AddCircle L → ℂ)-‖u‖^4/L) = 0 := by
    rw [variance_eq u hH,hP]
    unfold energyH1 at hPlaneEnergy
    linear_combination hPlaneEnergy
  have hQ := quartic_lower u hH
  have hV := variance_nonneg u (freq L k)
  have hv : variance u (freq L k) = 0 := by nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hQ)]
  exact zero_variance_plane u hH k hv

theorem plane_single_index (hκ : 0 < κ) (u : L2T L) (k : ℤ)
    (hp : ∃ c : ℂ,u = c • modeLp L k) : AllMassAt hκ u k := by
  obtain ⟨c,rfl⟩ := hp
  intro n
  rw [RootMassPlane.masses_plane]
  simp only [norm_smul,OneParticleBorn.norm_modeLp,mul_one]

theorem single_index_iff_mode (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) (k : ℤ) :
    AllMassAt hκ u k ↔ ∃ c : ℂ,u = c • modeLp L k :=
  ⟨single_index_plane hκ u hH k,plane_single_index hκ u k⟩

theorem mode_iff_plane (u : L2T L) (k : ℤ) :
    (∃ c : ℂ,u = c • modeLp L k) ↔
      ∃ a : ℂ,(u : AddCircle L → ℂ) =ᵐ[volume] fun x => a*_root_.fourier k x := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hLf.out).ne'
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨c/(Real.sqrt L : ℂ),?_⟩
    have he : (Real.sqrt L : ℂ)*(c/(Real.sqrt L : ℂ)) = c := by field_simp
    simpa only [he] using RootMassPlane.plane_coe (L := L) (c/(Real.sqrt L : ℂ)) k
  · rintro ⟨a,ha⟩
    refine ⟨(Real.sqrt L : ℂ)*a,?_⟩
    exact Lp.ext (ha.trans (RootMassPlane.plane_coe (L := L) a k).symm)

theorem single_index_iff_plane (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) (k : ℤ) :
    AllMassAt hκ u k ↔ ∃ a : ℂ,(u : AddCircle L → ℂ) =ᵐ[volume]
      fun x => a*_root_.fourier k x :=
  (single_index_iff_mode hκ u hH k).trans (mode_iff_plane u k)

end QuantumNLS.RootWeightedPlaneR26
