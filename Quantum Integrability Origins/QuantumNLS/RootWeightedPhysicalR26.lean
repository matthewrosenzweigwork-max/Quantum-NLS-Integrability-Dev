import QuantumNLS.RootWeightedIdentitiesR26
import QuantumNLS.WeakDerivatives

/-! Physical weak derivative and Fourier momentum of every H1 input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.RootWeightedPhysicalR26
open PhysicalTensor (L2T)
open QuantumNLS.Fourier ProductEnergyPreparation ChargeEnergy
variable {L : ℝ} [Fact (0 < L)]

theorem exists_derivative (u : L2T L) (hH : OneH1 u) : ∃ v,WeakDerivatives.HasWeakDeriv u v := by
  apply (WeakDerivatives.exists_hasWeakDeriv_iff u).mpr
  simpa only [fourierL2_apply] using (hasSum_kin_a hH).summable

def weakDerivative (u : L2T L) (hH : OneH1 u) : L2T L := (exists_derivative u hH).choose

theorem derivative_spec (u : L2T L) (hH : OneH1 u) :
    WeakDerivatives.HasWeakDeriv u (weakDerivative u hH) := (exists_derivative u hH).choose_spec

theorem derivative_coeff (u : L2T L) (hH : OneH1 u) (n : ℤ) :
    fourierL2 L (weakDerivative u hH) n = WeakDerivatives.ikn L n * fourierL2 L u n := by
  simpa only [fourierL2_apply] using WeakDerivatives.coeff_of_hasWeakDeriv (derivative_spec u hH) n

theorem norm_derivative (u : L2T L) (hH : OneH1 u) :
    ‖weakDerivative u hH‖^2 = kinetic (u : AddCircle L → ℂ) := by
  rw [← norm_fourierL2,Energy.norm_sq_eq_tsum]
  simp_rw [derivative_coeff,WeakDerivatives.norm_ikn_mul_sq]
  exact (hasSum_kin_a hH).tsum_eq

def fourierMomentum (u : L2T L) : ℝ := ∑' n : ℤ,freq L n*‖fourierL2 L u n‖^2

theorem momentum_summable (u : L2T L) (hH : OneH1 u) :
    Summable (fun n : ℤ =>|freq L n*‖fourierL2 L u n‖^2|) := by
  have h0 := Energy.summable_sq (fourierL2 L u)
  have hk := (hasSum_kin_a hH).summable
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_) (h0.add hk)
  rw [abs_mul]
  simp only [abs_pow,abs_norm]
  have hp : |freq L n| ≤ 1+freq L n^2 := by nlinarith [sq_nonneg (|freq L n|-1),sq_abs (freq L n)]
  nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖fourierL2 L u n‖)]

theorem momentum_inner (u : L2T L) (hH : OneH1 u) :
    (fourierMomentum u : ℂ) = ⟪u,-Complex.I • weakDerivative u hH⟫_ℂ := by
  rw [← (fourierL2 L).inner_map_map,lp.inner_eq_tsum]
  unfold fourierMomentum
  apply Eq.trans (Complex.ofReal_tsum (fun n : ℤ => freq L n*‖fourierL2 L u n‖^2))
  apply tsum_congr
  intro n
  simp only [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RCLike.inner_apply',derivative_coeff,
    WeakDerivatives.ikn,Complex.ofReal_mul,Complex.ofReal_pow]
  rw [show conj (fourierL2 L u n)*(-Complex.I*(Complex.I*(freq L n : ℂ)*fourierL2 L u n)) =
      (freq L n : ℂ)*(conj (fourierL2 L u n)*fourierL2 L u n) by
        ring_nf; simp]
  rw [Complex.conj_mul',← Complex.ofReal_pow]

end QuantumNLS.RootWeightedPhysicalR26
