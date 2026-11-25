import QuantumNLS.REF88QuantumDef
import QuantumNLS.FullMassLimit
import QuantumNLS.F04Global

/-! R-EF8C2837 item (iv), physical_cubic.tex:316–337.
H¹ convergence implies W₂ convergence of the normalized spectral measures.
Both ingredients are proved here: weak continuity (accepted full-mass theorem) and
second-moment continuity (accepted physical energy identity). No W₂ assumption is added.
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.REF88SQuantiles
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.Fourier
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.QuantileTransport
variable {L κ : ℝ} [Fact (0 < L)]

/-- Fourier coefficients of an H¹ field, with the F04 equivalent norm. -/
def coeffH1Linear : H02 L 1 →ₗ[ℂ] h04 L 1 where
  toFun u := WSeq.mk (f04W L 1) (fun n => fourierL2 L u.val n)
    (Fourier.mem04_of_memHs (by norm_num : (0 : ℝ) ≤ 1) u.summable)
  map_add' u v := by
    apply WSeq.ext; funext n
    simp only [WSeq.val_mk, WSeq.val_add, Pi.add_apply, WField.val_add, map_add, lp.coeFn_add, Pi.add_apply]
    rfl
  map_smul' c u := by
    apply WSeq.ext; funext n
    simp only [WSeq.val_mk, WSeq.val_smul, Pi.smul_apply, WField.val_smul, map_smul, lp.coeFn_smul, Pi.smul_apply]
    rfl

def coeffH1 : H02 L 1 →L[ℂ] h04 L 1 :=
  coeffH1Linear.mkContinuous 1 (by
    intro u
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      PosWeight.norm_sq_eq_tsum, WField.norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun n => ?_) (WSeq.summable _) u.summable
    change Fourier.f04Weight L 1 n * ‖fourierL2 L u.val n‖ ^ 2 ≤
      Fourier.sobolevWeight L 1 n * ‖fourierL2 L u.val n‖ ^ 2
    exact mul_le_mul_of_nonneg_right (Fourier.f04Weight_comparison L 1 (by norm_num) n).1 (sq_nonneg _))

@[simp] theorem coeffH1_val (u : H02 L 1) (n : ℤ) :
    (coeffH1 u).val n = fourierL2 L u.val n := rfl

theorem coeffH1_physical (u : H02 L 1) :
    RootEnergyVariation.physical (F04Regularity.m10 (coeffH1 u)) = u.val := by
  apply (fourierL2 L).injective
  apply lp.ext; funext n
  rw [RootEnergyVariation.physical_coeff]
  exact coeffH1_val u n

theorem oneH1 (u : H02 L 1) : ProductEnergyPreparation.OneH1 u.val := by
  have h := RootEnergyVariation.physical_oneH1 (coeffH1 u)
  rwa [coeffH1_physical] at h

theorem energy_continuous :
    Continuous (fun u : H02 L 1 => ChargeEnergy.energyH1 κ (u.val : AddCircle L → ℂ)) := by
  have h := (F04Global.continuous_energy (L := L) κ).comp (coeffH1 (L := L)).continuous
  have he : ∀ u : H02 L 1, F04Regularity.energy κ (coeffH1 u) =
      ChargeEnergy.energyH1 κ (u.val : AddCircle L → ℂ) := by
    intro u
    rw [← RootEnergyVariation.physical_energy, coeffH1_physical]
  simpa only [Function.comp_def, he] using h

/-- The normalized endpoint measure M_{κ,u}/‖u‖² (used only at nonzero fields). -/
def normalized (hκ : 0 < κ) (u : L2T L) : Measure ℝ :=
  (ENNReal.ofReal (‖u‖ ^ 2))⁻¹ • measure hκ u

theorem normalized_prob (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    IsProbabilityMeasure (normalized hκ u) := by
  constructor
  rw [normalized, Measure.smul_apply, PhysicalQuantumMeasure.measure_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (sq_pos_of_pos (norm_pos_iff.2 hu))).ne' ENNReal.ofReal_ne_top

theorem normalized_integral (hκ : 0 < κ) (u : L2T L) (f : ℝ → ℝ) :
    (∫ x, f x ∂normalized hκ u) = (‖u‖ ^ 2)⁻¹ * ∫ x, f x ∂measure hκ u := by
  rw [normalized, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem normalized_unitDir (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    (hK : 0 < κ * ‖u‖ ^ 2) :
    normalized hκ u = F04SelBand.Mu hK (FullMass.unitDir u) := by
  have he := REF88QuantumDef.measure_unitDir hκ hu hK
  change measure hκ u = _ at he
  rw [normalized, he, smul_smul, ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.2 (sq_pos_of_pos (norm_pos_iff.2 hu))).ne' ENNReal.ofReal_ne_top, one_smul]

theorem normalized_moment (hκ : 0 < κ) (u : H02 L 1) :
    HasFiniteSecondMoment (normalized hκ u.val) ∧
      (∫ x, x ^ 2 ∂normalized hκ u.val) =
        (‖u.val‖ ^ 2)⁻¹ * ChargeEnergy.energyH1 κ (u.val : AddCircle L → ℂ) := by
  obtain ⟨hi,he⟩ := REF88EnergyBound.moment_of_oneH1 hκ u.val (oneH1 u)
  constructor
  · change Integrable _ _
    have h := hi.to_average
    rwa [PhysicalQuantumMeasure.measure_univ] at h
  · rw [normalized_integral, he]

/-- Weak continuity of normalized measures, including the varying effective coupling κ‖u_j‖². -/
theorem normalized_weak (hκ : 0 < κ) {v : ℕ → L2T L} {u : L2T L}
    (hu : u ≠ 0) (hv : Tendsto v atTop (𝓝 u)) :
    WeakConv (fun j => normalized hκ (v j)) (normalized hκ u) := by
  intro f
  have hw : Tendsto (fun j => FullMass.Mfin κ (v j)) atTop (𝓝 (FullMass.Mfin κ u)) :=
    ((FullMassLimit.continuous_Mfin (L := L)).tendsto (⟨κ,hκ.le⟩,u)).comp
      (tendsto_const_nhds.prodMk_nhds hv)
  have hi := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 hw) f
  have hn := (hv.norm.pow 2).inv₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hu))
  have hh := hn.mul hi
  simp only [normalized_integral, PhysicalL2Normalization.measure_eq_Mmeas]
  exact hh

/-- The printed quantile-convergence step, with every hypothesis derived from H¹ convergence. -/
theorem normalized_W2 (hκ : 0 < κ) {v : ℕ → H02 L 1} {u : H02 L 1}
    (hu : u.val ≠ 0) (hv0 : ∀ j, (v j).val ≠ 0) (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun j => W2 (normalized hκ (v j).val) (normalized hκ u.val)) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (normalized hκ u.val) := normalized_prob hκ hu
  haveI : ∀ j, IsProbabilityMeasure (normalized hκ (v j).val) := fun j => normalized_prob hκ (hv0 j)
  have hL2 := ((H02.toL2 (L := L) (by norm_num : (0 : ℝ) ≤ 1)).continuous.tendsto u).comp hv
  have hm : Tendsto (fun j => ∫ x, x ^ 2 ∂normalized hκ (v j).val) atTop
      (𝓝 (∫ x, x ^ 2 ∂normalized hκ u.val)) := by
    simp_rw [(normalized_moment hκ _).2]
    exact ((hL2.norm.pow 2).inv₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hu))).mul
      ((energy_continuous (κ := κ)).tendsto u |>.comp hv)
  exact tendsto_W2_of_weak_of_moment (fun j => (normalized_moment hκ (v j)).1)
    (normalized_moment hκ u).1 (normalized_weak hκ hu hL2) hm

/-- Literal L² convergence of the increasing normalized spectral quantiles. -/
theorem normalized_quantiles (hκ : 0 < κ) {v : ℕ → H02 L 1} {u : H02 L 1}
    (hu : u.val ≠ 0) (hv0 : ∀ j, (v j).val ≠ 0) (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun j => eLpNorm (fun t => quantile (normalized hκ (v j).val) t -
      quantile (normalized hκ u.val) t) 2 (volume.restrict (Set.Ioo 0 1))) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (normalized hκ u.val) := normalized_prob hκ hu
  haveI : ∀ j, IsProbabilityMeasure (normalized hκ (v j).val) := fun j => normalized_prob hκ (hv0 j)
  simpa only [W2_eq_eLpNorm_quantile_of_prob] using normalized_W2 hκ hu hv0 hv

#print axioms oneH1
#print axioms energy_continuous
#print axioms normalized_unitDir
#print axioms normalized_weak
#print axioms normalized_W2
#print axioms normalized_quantiles
end QuantumNLS.REF88SQuantiles
