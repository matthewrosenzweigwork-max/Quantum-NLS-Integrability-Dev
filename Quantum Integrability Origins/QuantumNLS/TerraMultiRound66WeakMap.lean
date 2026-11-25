import QuantumNLS.TerraMultiRound66WeakBound

/-! The H¹-to-L² first derivative as a bounded linear map. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives QuantumNLS.Fourier
open QuantumNLS.Sobolev QuantumNLS.TerraMultiRound66WeakFirst QuantumNLS.TerraMultiRound66WeakBound
namespace QuantumNLS.TerraMultiRound66WeakMap
variable {L : ℝ} [Fact (0 < L)]

def weakD (u : Hk L 1) : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  Classical.choose (exists_unique_first_weak_derivative L u)

theorem weakD_is_derivative (u : Hk L 1) : HasWeakDeriv u.val (weakD u) :=
  (Classical.choose_spec (exists_unique_first_weak_derivative L u)).1

theorem weakD_coeff (u : Hk L 1) (n : ℤ) :
    fourierL2 L (weakD u) n = ikn L n * fourierL2 L u.val n := by
  simp only [fourierL2_apply]
  exact coeff_of_hasWeakDeriv (weakD_is_derivative u) n

def weakDLinear : Hk L 1 →ₗ[ℂ] Lp ℂ 2 (volume : Measure (AddCircle L)) where
  toFun := weakD
  map_add' u v := by
    apply (fourierL2 L).injective
    ext n
    simp only [weakD_coeff, WField.val_add, map_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c u := by
    apply (fourierL2 L).injective
    ext n
    simp only [weakD_coeff, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    change ikn L n * (fourierL2 L (c • u.val)) n = _
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def weakDCLM : Hk L 1 →L[ℂ] Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  weakDLinear.mkContinuous 1 (fun u => by
    change ‖weakD u‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using weak_derivative_norm_le L u (weakD u) (weakD_is_derivative u))

#print axioms weakDCLM
#print axioms weakD_is_derivative
end QuantumNLS.TerraMultiRound66WeakMap
