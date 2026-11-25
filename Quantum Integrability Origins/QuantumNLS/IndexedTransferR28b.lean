import QuantumNLS.IndexedInverseR28b
import QuantumNLS.RootInvolutionLimit
import QuantumNLS.Local013Main

/-! LOCAL-016: chosen radius-8 expansions of the actual transfer perturbation.
This is an input to, not an assumption of, the pending contour calculus. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace QuantumNLS.IndexedTransferR28b
open PhysicalTensor KernelDefinition LocalPlacement KernelConvergence
  NormalizedTransfer HighMomentsRank IndexedInverseR28b
section Generic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem norm_zero_kernel (p : ℕ) : ‖(0 : BoundedSymmetricKernel H p)‖ = 0 :=
  norm_zero (E := TensorCarrier.SymSector ℂ H p →L[ℂ] TensorCarrier.SymSector ℂ H p)

theorem genericU_zero (N p : ℕ) (hp : p ≤ N) :
    genericU_N_r N p hp (0 : BoundedSymmetricKernel H p) = 0 := by
  have hh := RootOverlapLimit.genericU_smul N p hp (0 : ℂ)
    (0 : BoundedSymmetricKernel H p)
  simpa only [Local013ProductLimit.zero_smul_kernel] using hh

theorem norm_sub_smul_kernel {p : ℕ} (a b : ℂ) (K : BoundedSymmetricKernel H p) :
    ‖a • K-b • K‖ = ‖a-b‖*‖K‖ := by
  have he : a • K-b • K = (a-b) • K := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply,smul_apply]
    exact (sub_smul a b (K v)).symm
  rw [he,RadiusBound.norm_smul_kernel]
end Generic

variable {L κ : ℝ} [Fact (0 < L)]

def kernels (κ : ℝ) (z : ℂ) (N : ℕ) : KernelList (H := L2T L) N :=
  fun p => if p.1 = 0 then 0 else
    ((κ^p.1*fallR N p.1 : ℝ) : ℂ) • orderedKernel L p.1 z

def limitKernels (κ : ℝ) (z : ℂ) (p : ℕ) : BoundedSymmetricKernel (L2T L) p :=
  if p = 0 then 0 else ((κ^p : ℝ) : ℂ) • orderedKernel L p z

theorem represented_kernels (κ : ℝ) (z : ℂ) (N : ℕ) :
    RadiusBound.represented (kernels (L := L) κ z N) = normalizedTransfer L κ N z -
      (1+Complex.exp (Complex.I*z*L)) • ContinuousLinearMap.id ℂ _ := by
  rw [RadiusBound.represented,Fin.sum_univ_succ]
  simp only [Fin.val_zero]
  have hz : RadiusBound.Q N 0 (by omega) ((kernels (L := L) κ z N) 0) = 0 := by
    simp only [kernels,Fin.val_zero,eq_self]
    rw [RadiusBound.Q_eq_genericU_N_r]
    exact genericU_zero N 0 (by omega)
  rw [hz,zero_add]
  unfold normalizedTransfer
  rw [add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro p _
  simp only [kernels,Fin.val_succ,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false]
  rw [RadiusBound.Q_eq_genericU_N_r,RootOverlapLimit.genericU_smul]

theorem kernel_norm_geometric (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (p : ℕ) :
    ‖orderedKernel L p z‖ ≤ 16*L^p := by
  have hL : 0 < L := Fact.out
  have hp : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.factorial_pos p
  exact (ordered_kernel_bound n hz p).trans (div_le_self (by positivity) hp)

theorem coefficient_bound (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n)
    (N : ℕ) (p : Fin (N+1)) :
    8^p.1*‖kernels (L := L) κ z N p‖ ≤
      if p.1 = 0 then 0 else 16*(8*κ*L)^p.1 := by
  by_cases hp : p.1 = 0
  · simp only [kernels,hp,ite_true,norm_zero_kernel,mul_zero,le_refl]
  · have hN : 0 < N := by omega
    have hr := fallR_bounds N hN p.1 (by omega)
    have hK := kernel_norm_geometric n hz p.1
    simp only [kernels,hp,ite_false]
    rw [RadiusBound.norm_smul_kernel,Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg hκ.le _) hr.1)]
    calc
      _ ≤ 8^p.1*((κ^p.1*1)*(16*L^p.1)) := by gcongr; exact hr.2.2
      _ = _ := by rw [mul_pow,mul_pow]; ring

theorem radius_bound (hκ : 0 < κ) (hsmall : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (N : ℕ) :
    RadiusBound.radiusBound 8 (kernels (L := L) κ z N) ≤ 256*(κ*L) := by
  let q : ℝ := 8*κ*L
  have hL : 0 < L := Fact.out
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; nlinarith
  have hs : Summable (fun j : ℕ => 16*q^(j+1)) := by
    simpa [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      ((summable_geometric_of_lt_one hq0 hq1).mul_left (16*q))
  calc
    _ ≤ ∑ p : Fin (N+1), if p.1 = 0 then 0 else 16*q^p.1 :=
      Finset.sum_le_sum fun p _ => coefficient_bound hκ n hz N p
    _ = ∑ j ∈ Finset.range N, 16*q^(j+1) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero,ite_true,Fin.val_succ,Nat.add_eq_zero_iff,
        Nat.one_ne_zero,and_false,ite_false,zero_add]
      exact (Finset.sum_range (fun j : ℕ => 16*q^(j+1))).symm
    _ ≤ ∑' j : ℕ, 16*q^(j+1) :=
      hs.sum_le_tsum (Finset.range N) (fun j _ => by positivity)
    _ = 16*q/(1-q) := by
      have hh := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (16*q)
      have he : (fun j : ℕ => 16*q^(j+1)) = fun j => (16*q)*q^j := by
        funext j; rw [pow_succ]; ring
      rw [he,hh.tsum_eq]
      ring
    _ ≤ 256*(κ*L) := by
      apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
      dsimp [q]
      nlinarith [mul_pos hκ hL]

theorem coefficient_limit (κ : ℝ) (z : ℂ) (p : ℕ) :
    Tendsto (fun N => ‖coeffAt (kernels (L := L) κ z) N p - limitKernels κ z p‖)
      atTop (𝓝 0) := by
  by_cases hp : p = 0
  · subst p
    simp only [coeffAt,kernels,limitKernels,Nat.zero_le,dite_eq_left,ite_true,eq_self,
      sub_self,norm_zero_kernel]
    exact tendsto_const_nhds
  · have ht : Tendsto (fun N : ℕ => ((κ^p*fallR N p : ℝ) : ℂ)) atTop
        (𝓝 ((κ^p : ℝ) : ℂ)) := by
      simpa only [Function.comp_def,Complex.ofReal_mul,Complex.ofReal_pow,mul_one] using
        (Complex.continuous_ofReal.tendsto _).comp
        ((RootInvolutionLimit.fallR_tendsto p).const_mul (κ^p))
    have hn := ((ht.sub_const ((κ^p : ℝ) : ℂ)).norm).mul_const ‖orderedKernel L p z‖
    have he : (fun N => ‖coeffAt (kernels (L := L) κ z) N p - limitKernels κ z p‖) =ᶠ[atTop]
        (fun N => ‖((κ^p*fallR N p : ℝ) : ℂ) • orderedKernel L p z - limitKernels κ z p‖) := by
      filter_upwards [eventually_ge_atTop p] with N hN
      simp only [coeffAt,dite_eq_left hN,kernels,hp,ite_false]
    apply Tendsto.congr' he.symm
    simpa only [limitKernels,hp,ite_false,norm_sub_smul_kernel,sub_self,norm_zero,zero_mul] using hn

/-- Actual transfer perturbations converge on radius 8 with the source
smallness condition and an explicit uniform bound. -/
theorem transfer_converges (hκ : 0 < κ) (hsmall : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    ConvergesOnRadius 8 (kernels (L := L) κ z) (limitKernels κ z) :=
  ⟨⟨256*(κ*L),radius_bound hκ hsmall n hz⟩,coefficient_limit κ z⟩

theorem inverse_ratio_small (hκ : 0 < κ) (hsmall : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (N : ℕ) :
    RadiusBound.radiusBound 8 (kernels (L := L) κ z N)/rstar < 1/1000000 := by
  have hb := radius_bound hκ hsmall n hz N
  apply (div_lt_iff₀ (by norm_num [rstar] : 0 < rstar)).mpr
  norm_num [rstar] at *
  linarith

end QuantumNLS.IndexedTransferR28b
#print axioms QuantumNLS.IndexedTransferR28b.represented_kernels
#print axioms QuantumNLS.IndexedTransferR28b.transfer_converges
#print axioms QuantumNLS.IndexedTransferR28b.inverse_ratio_small
