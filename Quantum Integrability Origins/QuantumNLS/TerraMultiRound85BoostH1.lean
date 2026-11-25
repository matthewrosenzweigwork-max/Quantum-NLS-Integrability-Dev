import QuantumNLS.LocalWellPosedness

/-! The integer Fourier-index shift is bounded on the actual H¹ carrier.
This is support toward the Galilean solution-class proof, not a flow identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness
namespace QuantumNLS.TerraMultiRound85BoostH1
variable {L : ℝ} [Fact (0 < L)]

def shiftSeq (k : ℤ) (a : ℤ → ℂ) : ℤ → ℂ := fun n => a (n-k)

def shiftBound (k : ℤ) : ℝ := 2*(1 + freq L k ^ 2)

theorem shiftBound_pos (k : ℤ) : 0 < shiftBound (L := L) k := by
  unfold shiftBound
  positivity

/-- The shifted H¹ weight is bounded by the original weight. -/
theorem shifted_weight_le (k n : ℤ) :
    f04Weight L 1 n ≤ shiftBound (L := L) k * f04Weight L 1 (n-k) := by
  have hf : freq L n = freq L (n-k) + freq L k := by
    rw [← freq_add]
    congr 1
    omega
  simp only [f04Weight, Real.rpow_one, shiftBound, hf]
  nlinarith [sq_nonneg (freq L (n-k) - freq L k),
    mul_nonneg (sq_nonneg (freq L (n-k))) (sq_nonneg (freq L k))]

/-- Integer frequency shifts preserve H¹ membership. -/
theorem mem04_shift {a : ℤ → ℂ} (ha : Mem04 L 1 a) (k : ℤ) : Mem04 L 1 (shiftSeq k a) := by
  unfold Mem04 at *
  have hs : Summable (fun n : ℤ => f04Weight L 1 (n-k) * ‖a (n-k)‖^2) := by
    simpa only [Function.comp_def, Equiv.coe_addRight, sub_eq_add_neg] using (Equiv.addRight (-k)).summable_iff.mpr ha
  have hC : 0 ≤ shiftBound (L := L) k := (shiftBound_pos k).le
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (f04Weight_pos L 1 n).le (sq_nonneg _)) ?_
    (hs.mul_left (shiftBound (L := L) k))
  intro n
  change f04Weight L 1 n * ‖a (n-k)‖^2 ≤
    shiftBound (L := L) k * (f04Weight L 1 (n-k) * ‖a (n-k)‖^2)
  calc
    _ ≤ (shiftBound (L := L) k * f04Weight L 1 (n-k)) * ‖a (n-k)‖^2 :=
      mul_le_mul_of_nonneg_right (shifted_weight_le k n) (sq_nonneg _)
    _ = _ := by ring

/-- The corresponding weighted squared norm has the same uniform bound. -/
theorem shift_normSq_le (k : ℤ) (a : h04 L 1) :
    f04NormSq L 1 (shiftSeq k a.val) ≤ shiftBound (L := L) k * f04NormSq L 1 a.val := by
  have hsum : Summable (fun n : ℤ => f04Weight L 1 (n-k) * ‖a.val (n-k)‖^2) := by
    simpa only [Function.comp_def, Equiv.coe_addRight, sub_eq_add_neg] using (Equiv.addRight (-k)).summable_iff.mpr (h04_mem L 1 a)
  have hp : ∀ n : ℤ, f04Weight L 1 n * ‖shiftSeq k a.val n‖^2 ≤
      shiftBound (L := L) k * (f04Weight L 1 (n-k) * ‖a.val (n-k)‖^2) := by
    intro n
    change f04Weight L 1 n * ‖a.val (n-k)‖^2 ≤ _
    calc
      _ ≤ (shiftBound (L := L) k * f04Weight L 1 (n-k)) * ‖a.val (n-k)‖^2 :=
        mul_le_mul_of_nonneg_right (shifted_weight_le k n) (sq_nonneg _)
      _ = _ := by ring
  unfold f04NormSq
  calc
    _ ≤ ∑' n : ℤ, shiftBound (L := L) k * (f04Weight L 1 (n-k) * ‖a.val (n-k)‖^2) :=
      Summable.tsum_le_tsum hp (mem04_shift (h04_mem L 1 a) k) (hsum.mul_left _)
    _ = shiftBound (L := L) k * ∑' n : ℤ, f04Weight L 1 n * ‖a.val n‖^2 := by
      rw [hsum.tsum_mul_left]
      congr 1
      simpa only [Function.comp_def, Equiv.coe_addRight, sub_eq_add_neg] using (Equiv.addRight (-k)).tsum_eq (fun n => f04Weight L 1 n * ‖a.val n‖^2)

/-- The actual index shift is a bounded complex-linear H¹ operator. -/
def shift (k : ℤ) : h04 L 1 →L[ℂ] h04 L 1 :=
  LinearMap.mkContinuous
    { toFun a := WSeq.mk _ (shiftSeq k a.val) (mem04_shift (h04_mem L 1 a) k)
      map_add' a b := WSeq.ext (by funext n; rfl)
      map_smul' c a := WSeq.ext (by funext n; rfl) }
    (Real.sqrt (shiftBound (L := L) k)) (fun a => by
      rw [norm_eq_sqrt, norm_eq_sqrt]
      have hh := Real.sqrt_le_sqrt (shift_normSq_le k a)
      rw [Real.sqrt_mul (shiftBound_pos k).le] at hh
      exact hh)

#print axioms shifted_weight_le
#print axioms mem04_shift
#print axioms shift_normSq_le
#print axioms shift
end QuantumNLS.TerraMultiRound85BoostH1
