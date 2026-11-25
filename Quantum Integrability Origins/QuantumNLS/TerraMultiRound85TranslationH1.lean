import QuantumNLS.LocalWellPosedness

/-! Translation on Fourier Sobolev spaces and commutation with the free group. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness AddCircle
namespace QuantumNLS.TerraMultiRound85TranslationH1
variable {L : ℝ} [Fact (0 < L)]

/-- The Fourier multiplier for `u(x+y)`. -/
def transPhase (y : ℝ) (n : ℤ) : ℂ := fourier n (y : AddCircle L)

theorem norm_transPhase (y : ℝ) (n : ℤ) : ‖transPhase (L := L) y n‖ = 1 := by
  unfold transPhase
  rw [fourier_apply]
  exact Circle.norm_coe _

def translatedSeq (y : ℝ) (a : ℤ → ℂ) : ℤ → ℂ := fun n => transPhase (L := L) y n * a n

theorem mem04_translated {s : ℝ} {a : ℤ → ℂ} (ha : Mem04 L s a) (y : ℝ) :
    Mem04 L s (translatedSeq (L := L) y a) := by
  unfold Mem04 at *
  refine ha.congr fun n => ?_
  simp [translatedSeq, norm_mul, norm_transPhase]

theorem f04NormSq_translated (s y : ℝ) (a : ℤ → ℂ) :
    f04NormSq L s (translatedSeq (L := L) y a) = f04NormSq L s a := by
  unfold f04NormSq
  apply tsum_congr
  intro n
  simp [translatedSeq, norm_mul, norm_transPhase]

/-- Spatial translation as a complex-linear Hˢ isometry. -/
def translate (s y : ℝ) : h04 L s →L[ℂ] h04 L s :=
  LinearMap.mkContinuous
    { toFun a := WSeq.mk _ (translatedSeq (L := L) y a.val) (mem04_translated (h04_mem L s a) y)
      map_add' a b := WSeq.ext (by
        funext n
        change transPhase (L := L) y n * (a.val n + b.val n) =
          transPhase (L := L) y n * a.val n + transPhase (L := L) y n * b.val n
        ring)
      map_smul' c a := WSeq.ext (by
        funext n
        change transPhase (L := L) y n * (c * a.val n) = c * (transPhase (L := L) y n * a.val n)
        ring) }
    1 (fun a => by
      rw [one_mul, norm_eq_sqrt, norm_eq_sqrt]
      change Real.sqrt (f04NormSq L s (translatedSeq (L := L) y a.val)) ≤ Real.sqrt (f04NormSq L s a.val)
      rw [f04NormSq_translated])

@[simp] theorem translate_val (s y : ℝ) (a : h04 L s) : (translate s y a).val = translatedSeq (L := L) y a.val := rfl

theorem translate_Sgrp (s y t : ℝ) (a : h04 L s) :
    translate s y (Sgrp s t a) = Sgrp s t (translate s y a) := by
  apply WSeq.ext
  funext n
  change transPhase (L := L) y n * (phase L t n * a.val n) = phase L t n * (transPhase (L := L) y n * a.val n)
  ring

#print axioms mem04_translated
#print axioms f04NormSq_translated
#print axioms translate_Sgrp
end QuantumNLS.TerraMultiRound85TranslationH1
