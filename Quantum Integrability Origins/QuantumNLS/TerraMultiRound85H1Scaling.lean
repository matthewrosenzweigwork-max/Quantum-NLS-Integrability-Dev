import QuantumNLS.TerraMultiRound85H1Bridge

/-! Real-amplitude scaling for the Fourier H¹ cubic equation. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness
namespace QuantumNLS.TerraMultiRound85H1Scaling
variable {L : ℝ} [Fact (0 < L)]

/-- The Fourier cubic map is homogeneous of degree three under real scalings. -/
theorem Fh_real_scale {s : ℝ} (hs : 1 ≤ s) (r : ℝ) (a : h04 L s) :
    Fh hs ((r : ℂ) • a) = ((r : ℂ)^3) • Fh hs a := by
  apply WSeq.ext
  funext n
  change coeff L (nlRep L (((r : ℂ) • a).val)) n =
    ((r : ℂ)^3) * coeff L (nlRep L a.val) n
  have hn : nlRep L (((r : ℂ) • a).val) =
      fun x => ((r : ℂ)^3) * nlRep L a.val x := by
    funext x
    have hval : (((r : ℂ) • a).val) = fun n => (r : ℂ) * a.val n := by
      funext k
      rfl
    rw [hval]
    simp only [nlRep, seriesRep_smul', norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    push_cast
    ring
  rw [hn, coeff_const_mul]

#print axioms Fh_real_scale
end QuantumNLS.TerraMultiRound85H1Scaling
