import QuantumNLS.TerraMultiRound85ReflectionH1

/-! The Fourier H¹ reflection commutes with the actual cubic nonlinearity. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.TerraMultiRound85ReflectionH1
namespace QuantumNLS.TerraMultiRound85ReflectionCubic
variable {L : ℝ} [Fact (0 < L)]

/-- Fourier synthesis of reversed coefficients is spatial reflection. -/
theorem series_reverse (a : ℤ → ℂ) (x : AddCircle L) :
    seriesRep L (reverseSeq a) x = seriesRep L a (-x) := by
  unfold seriesRep
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => a n * mode L n (-x))]
  refine tsum_congr fun n => ?_
  simp [reverseSeq, mode_neg, conj_mode]

/-- A spatial reflection reverses the Fourier coefficient index. -/
theorem coeff_reflect (f : AddCircle L → ℂ) (n : ℤ) :
    coeff L (fun x => f (-x)) n = coeff L f (-n) := by
  unfold coeff
  change (∫ x, conj (mode L n x) * f (-x)) = ∫ x, conj (mode L (-n) x) * f x
  rw [← integral_neg_eq_self (fun x => conj (mode L n x) * f (-x)) (volume : Measure (AddCircle L))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mode_neg, conj_mode]

/-- The cubic Sobolev map commutes with spatial reflection. -/
theorem Fh_reflect {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) :
    Fh hs (reflect s a) = reflect s (Fh hs a) := by
  apply WSeq.ext
  funext n
  change coeff L (nlRep L (reverseSeq a.val)) n = coeff L (nlRep L a.val) (-n)
  rw [← coeff_reflect]
  congr 1
  funext x
  simp [nlRep, series_reverse]

#print axioms series_reverse
#print axioms coeff_reflect
#print axioms Fh_reflect
end QuantumNLS.TerraMultiRound85ReflectionCubic
