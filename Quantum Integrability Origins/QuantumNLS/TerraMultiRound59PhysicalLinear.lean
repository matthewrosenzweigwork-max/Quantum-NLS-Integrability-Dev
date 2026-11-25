import QuantumNLS.TerraMultiRound49SobolevBridge

/-! The Fourier physical realization is a continuous linear isometry. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59PhysicalLinear
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.TerraMultiRound49SobolevBridge

variable {L : ℝ} [Fact (0 < L)]

theorem physicalToHk_add (k : ℕ) (x y : Ell2) :
    physicalToHk (L := L) k (x + y) = physicalToHk k x + physicalToHk k y := by
  apply (fourierHs (L := L) (one_le_def002 L (Nat.cast_nonneg k))).injective
  apply PosWeight.WSeq.ext
  funext n
  simp only [map_add, PosWeight.WSeq.val_add, Pi.add_apply, fourierHs_val, physicalToHk_coeff, toField_add]

theorem physicalToHk_smul (k : ℕ) (c : ℂ) (x : Ell2) :
    physicalToHk (L := L) k (c • x) = c • physicalToHk k x := by
  apply (fourierHs (L := L) (one_le_def002 L (Nat.cast_nonneg k))).injective
  apply PosWeight.WSeq.ext
  funext n
  simp only [map_smul, PosWeight.WSeq.val_smul, Pi.smul_apply, fourierHs_val, physicalToHk_coeff, toField_smul, smul_eq_mul]

theorem norm_physicalToHk (k : ℕ) (x : Ell2) : ‖physicalToHk (L := L) k x‖ = ‖x‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
  rw [WField.norm_sq_eq_tsum L, norm_sq_eq_tsum]
  apply tsum_congr
  intro n
  rw [physicalToHk_coeff]
  change wt L (k : ℝ) n * ‖toField L (k : ℝ) x n‖ ^ 2 = ‖x n‖ ^ 2
  exact wt_mul_norm_div_sq L (k : ℝ) n (x n)

def physicalCLM (k : ℕ) : Ell2 →L[ℂ] Hk L k :=
  LinearMap.mkContinuous
    { toFun := physicalToHk k
      map_add' := physicalToHk_add k
      map_smul' := physicalToHk_smul k }
    1 (fun x => by simp [norm_physicalToHk])

@[simp] theorem physicalCLM_apply (k : ℕ) (x : Ell2) :
    physicalCLM (L := L) k x = physicalToHk k x := rfl

#print axioms physicalToHk_add
#print axioms physicalToHk_smul
#print axioms norm_physicalToHk
#print axioms physicalCLM
#print axioms physicalCLM_apply
end QuantumNLS.TerraMultiRound59PhysicalLinear
