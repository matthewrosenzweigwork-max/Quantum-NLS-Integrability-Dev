import QuantumNLS.LocalWellPosedness

/-! Reflection on the actual Fourier H¹ spaces, as support toward the
physical-flow symmetry. No flow identity is asserted in this module. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness
namespace QuantumNLS.TerraMultiRound85ReflectionH1
variable {L : ℝ} [Fact (0 < L)]

def reverseSeq (a : ℤ → ℂ) : ℤ → ℂ := fun n => a (-n)

theorem mem04_reverse {s : ℝ} {a : ℤ → ℂ} (ha : Mem04 L s a) : Mem04 L s (reverseSeq a) := by
  unfold Mem04 at *
  have h := (Equiv.neg ℤ).summable_iff.2 ha
  refine h.congr fun n => ?_
  simp [reverseSeq, f04Weight_neg]

theorem f04NormSq_reverse (s : ℝ) (a : ℤ → ℂ) :
    f04NormSq L s (reverseSeq a) = f04NormSq L s a := by
  unfold f04NormSq
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => f04Weight L s n * ‖a n‖^2)]
  refine tsum_congr fun n => ?_
  simp [reverseSeq, f04Weight_neg]

/-- Spatial reflection is a bounded complex-linear Hˢ isometry. -/
def reflect (s : ℝ) : h04 L s →L[ℂ] h04 L s :=
  LinearMap.mkContinuous
    { toFun a := WSeq.mk _ (reverseSeq a.val) (mem04_reverse (h04_mem L s a))
      map_add' a b := WSeq.ext (by funext n; rfl)
      map_smul' c a := WSeq.ext (by funext n; rfl) }
    1 (fun a => by
      rw [one_mul, norm_eq_sqrt, norm_eq_sqrt]
      change Real.sqrt (f04NormSq L s (reverseSeq a.val)) ≤ Real.sqrt (f04NormSq L s a.val)
      rw [f04NormSq_reverse])

@[simp] theorem reflect_val (s : ℝ) (a : h04 L s) : (reflect s a).val = reverseSeq a.val := rfl

/-- Reflection commutes with the free Schrödinger group. -/
theorem reflect_Sgrp (s t : ℝ) (a : h04 L s) :
    reflect s (Sgrp s t a) = Sgrp s t (reflect s a) := by
  apply WSeq.ext
  funext n
  change phase L t (-n) * a.val (-n) = phase L t n * a.val (-n)
  unfold phase
  rw [freq_neg, neg_sq]

#print axioms mem04_reverse
#print axioms f04NormSq_reverse
#print axioms reflect_Sgrp
end QuantumNLS.TerraMultiRound85ReflectionH1
