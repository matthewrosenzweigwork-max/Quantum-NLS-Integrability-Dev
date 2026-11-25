import QuantumNLS.TerraMultiRound85TranslationH1

/-! Fourier synthesis and cubic nonlinearity under spatial translation. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.TerraMultiRound85TranslationH1 AddCircle
namespace QuantumNLS.TerraMultiRound85TranslationCubic
variable {L : ℝ} [Fact (0 < L)]

/-- A Fourier mode translated by `y` gains its exact unit multiplier. -/
theorem mode_translate (n : ℤ) (x : AddCircle L) (y : ℝ) :
    mode L n (x + (y : AddCircle L)) = transPhase (L := L) y n * mode L n x := by
  unfold mode transPhase
  simp_rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]
  ring

/-- Fourier synthesis of translated coefficients is the translated field. -/
theorem series_translated (a : ℤ → ℂ) (x : AddCircle L) (y : ℝ) :
    seriesRep L (translatedSeq (L := L) y a) x = seriesRep L a (x + (y : AddCircle L)) := by
  unfold seriesRep translatedSeq
  apply tsum_congr
  intro n
  rw [mode_translate]
  ring

/-- Fourier coefficients of a translated integrable field. -/
theorem coeff_translate (f : AddCircle L → ℂ) (n : ℤ) (y : ℝ) :
    coeff L (fun x => f (x + (y : AddCircle L))) n = transPhase (L := L) y n * coeff L f n := by
  unfold coeff
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self (μ := (volume : Measure (AddCircle L)))
    (fun x : AddCircle L => conj (mode L n x) * f (x + (y : AddCircle L))) (-(y : AddCircle L))
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : mode L n (x - (y : AddCircle L)) =
      conj (transPhase (L := L) y n) * mode L n x := by
    have hp := mode_translate n (x - (y : AddCircle L)) y
    have hphase : transPhase (L := L) y n * conj (transPhase (L := L) y n) = 1 := by
      rw [Complex.mul_conj', norm_transPhase]
      norm_num
    have heq : x - (y : AddCircle L) + (y : AddCircle L) = x := sub_add_cancel _ _
    rw [heq] at hp
    calc
      mode L n (x - (y : AddCircle L)) = (conj (transPhase (L := L) y n) * transPhase (L := L) y n) * mode L n (x - (y : AddCircle L)) := by rw [mul_comm (conj _) _, hphase, one_mul]
      _ = conj (transPhase (L := L) y n) * mode L n x := by rw [mul_assoc, ← hp]
  change conj (mode L n (x - (y : AddCircle L))) * f (x - (y : AddCircle L) + (y : AddCircle L)) =
    transPhase (L := L) y n * (conj (mode L n x) * f x)
  rw [sub_add_cancel, hm]
  simp only [map_mul, Complex.conj_conj]
  ring

/-- The cubic Sobolev map commutes with spatial translation. -/
theorem Fh_translate {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) (y : ℝ) :
    Fh hs (translate s y a) = translate s y (Fh hs a) := by
  apply WSeq.ext
  funext n
  change coeff L (nlRep L (translatedSeq (L := L) y a.val)) n = transPhase (L := L) y n * coeff L (nlRep L a.val) n
  rw [← coeff_translate]
  congr 1
  funext x
  simp [nlRep, series_translated]

#print axioms mode_translate
#print axioms series_translated
#print axioms coeff_translate
#print axioms Fh_translate
end QuantumNLS.TerraMultiRound85TranslationCubic
