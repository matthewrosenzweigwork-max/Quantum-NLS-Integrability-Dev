import QuantumNLS.TerraMultiRound85BoostH1
import QuantumNLS.RootMassBoostSymbol
import QuantumNLS.H1Bridge

/-! The H¹ Fourier shift is physical modulation and commutes with the cubic
map up to the same shift. This is support, not the Galilean flow identity. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.H1Bridge QuantumNLS.TerraMultiRound85BoostH1 AddCircle
namespace QuantumNLS.TerraMultiRound85BoostCubic
variable {L : ℝ} [Fact (0 < L)]

/-- The shifted Fourier mode identity with the physical boost character. -/
theorem mode_boost (k n : ℤ) (x : AddCircle L) :
    fourier k x * mode L (n-k) x = mode L n x := by
  unfold mode
  rw [mul_comm (fourier k x) _, mul_assoc, ← fourier_add]
  rw [show n-k+k = n by omega]

/-- Synthesis after index shift is multiplication by the boost character. -/
theorem series_shift (k : ℤ) (a : ℤ → ℂ) (x : AddCircle L) :
    seriesRep L (shiftSeq k a) x = fourier k x * seriesRep L a x := by
  unfold seriesRep
  rw [← tsum_mul_left]
  rw [← (Equiv.addRight (-k)).tsum_eq (fun n => fourier k x * (a n * mode L n x))]
  refine tsum_congr fun n => ?_
  simp only [Function.comp_def, Equiv.coe_addRight, shiftSeq, sub_eq_add_neg]
  rw [← mode_boost k n]
  ring

/-- Multiplication by the boost character shifts Fourier coefficients. -/
theorem coeff_boost (k n : ℤ) (f : AddCircle L → ℂ) :
    coeff L (fun x => fourier k x * f x) n = coeff L f (n-k) := by
  unfold coeff
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : conj (mode L n x) * fourier k x = conj (mode L (n-k) x) := by
    unfold mode
    rw [map_mul, map_mul, Complex.conj_ofReal, ← fourier_neg, ← fourier_neg]
    rw [mul_assoc, ← fourier_add, show -n+k = -(n-k) by omega]
  change conj (mode L n x) * (fourier k x * f x) = conj (mode L (n-k) x) * f x
  rw [← mul_assoc, hm]

/-- The cubic map is equivariant under physical modulation. -/
theorem Fh_shift (k : ℤ) (a : h04 L 1) :
    Fh (le_refl (1 : ℝ)) (shift k a) = shift k (Fh (le_refl (1 : ℝ)) a) := by
  apply WSeq.ext
  funext n
  change coeff L (nlRep L (shiftSeq k a.val)) n = coeff L (nlRep L a.val) (n-k)
  rw [← coeff_boost]
  congr 1
  funext x
  simp only [nlRep, series_shift, norm_mul, show ‖fourier k x‖ = 1 from Circle.norm_coe _, one_mul]
  ring

/-- On H¹ the coefficient shift is the actual L² boost. -/
theorem emb_shift (k : ℤ) (a : h04 L 1) :
    emb (shift k a) = QuantumNLS.RootMassBoostSymbol.boost k (emb a) := by
  apply MeasureTheory.Lp.ext
  have h1 := emb_coeFn (shift k a)
  have h2 := QuantumNLS.RootMassBoostSymbol.coe_boost k (emb a)
  have h3 := emb_coeFn a
  filter_upwards [h1,h2,h3] with x h1x h2x h3x
  rw [h1x, h2x]
  change seriesRep L (shiftSeq k a.val) x = fourier k x * (emb a : AddCircle L → ℂ) x
  rw [series_shift, h3x]
  rfl

#print axioms mode_boost
#print axioms series_shift
#print axioms coeff_boost
#print axioms Fh_shift
#print axioms emb_shift
end QuantumNLS.TerraMultiRound85BoostCubic
