import Mathlib

/-! LOCAL-007 stage Z1: coordinatewise multiplication `ℓ∞(ℤ;ℝ) × ℓ²(ℤ;ℂ) → ℓ²(ℤ;ℂ)` as a bounded bilinear map. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction
open scoped ENNReal
namespace QuantumNLS.Local007Mul

abbrev Seq := lp (fun _ : ℤ => ℂ) 2

theorem sq_summable (g : Seq) : Summable fun n : ℤ => ‖g n‖ ^ 2 := by
  have h := (lp.hasSum_norm (p := 2) (by norm_num) g).summable
  simpa [Real.rpow_two] using h

theorem tsum_sq (g : Seq) : ∑' n : ℤ, ‖g n‖ ^ 2 = ‖g‖ ^ 2 := by
  have h := (lp.hasSum_norm (p := 2) (by norm_num) g).tsum_eq
  simpa [Real.rpow_two] using h

theorem mem_mul (s : ℤ →ᵇ ℝ) (g : Seq) : Memℓp (fun n : ℤ => (s n : ℂ) * g n) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hs : Summable fun n : ℤ => ‖s‖ ^ 2 * ‖g n‖ ^ 2 := (sq_summable g).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [norm_mul, mul_pow, Complex.norm_real]
  gcongr
  rw [Real.norm_eq_abs]
  simpa [Real.norm_eq_abs] using s.norm_coe_le_norm n

def mulSeq (s : ℤ →ᵇ ℝ) (g : Seq) : Seq := ⟨fun n => (s n : ℂ) * g n, mem_mul s g⟩

theorem mulSeq_apply (s : ℤ →ᵇ ℝ) (g : Seq) (n : ℤ) : mulSeq s g n = (s n : ℂ) * g n := rfl

theorem norm_mulSeq_le (s : ℤ →ᵇ ℝ) (g : Seq) : ‖mulSeq s g‖ ≤ ‖s‖ * ‖g‖ := by
  refine lp.norm_le_of_forall_sum_le (by norm_num) (by positivity) fun S => ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, mulSeq_apply]
  have h1 : ∀ n ∈ S, ‖(s n : ℂ) * g n‖ ^ 2 ≤ ‖s‖ ^ 2 * ‖g n‖ ^ 2 := by
    intro n _
    rw [norm_mul, mul_pow, Complex.norm_real]
    gcongr
    rw [Real.norm_eq_abs]
    simpa [Real.norm_eq_abs] using s.norm_coe_le_norm n
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum, mul_pow]
  gcongr
  have := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) g S
  simpa [Real.rpow_two] using this

/-- Coordinatewise multiplication as a bounded real-bilinear map. -/
def mulCLM : (ℤ →ᵇ ℝ) →L[ℝ] Seq →L[ℝ] Seq :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ mulSeq
      (fun s t g => by
        apply lp.ext; funext n
        simp [mulSeq_apply, add_mul])
      (fun a s g => by
        apply lp.ext; funext n
        simp [mulSeq_apply, Complex.real_smul]; ring)
      (fun s g h => by
        apply lp.ext; funext n
        simp [mulSeq_apply, mul_add])
      (fun a s g => by
        apply lp.ext; funext n
        simp [mulSeq_apply, Complex.real_smul]; ring))
    1 (fun s g => by simpa using norm_mulSeq_le s g)

theorem mulCLM_apply (s : ℤ →ᵇ ℝ) (g : Seq) (n : ℤ) : mulCLM s g n = (s n : ℂ) * g n := rfl

end QuantumNLS.Local007Mul
#print axioms QuantumNLS.Local007Mul.mulCLM
