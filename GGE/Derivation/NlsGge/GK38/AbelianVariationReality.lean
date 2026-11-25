import NlsGge.GK38.AbelianNumeratorVariation
import NlsGge.GK38.AbelianRealImage
import Mathlib.Analysis.Complex.RealDeriv

/-! Reality of the entire directional numerator on the real spectral axis.
Both sequence and direction are genuine real-valued complex lp2 elements. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem variation_real (n : ℤ) (s h : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0) (hh : ∀ k : ℤ, (h k).im=0) (x : ℝ) :
    (p4NumeratorVariation38 n s h (x : ℂ)).im=0 := by
  have hd := variation_hasDerivAt n s h (x : ℂ)
  have hdr : HasDerivAt
      (fun t : ℝ => p2FullNumerator38 n (s+(t : ℂ) • h) (x : ℂ))
      (p4NumeratorVariation38 n s h (x : ℂ)) 0 := by
    simpa only [Complex.ofReal_zero] using! hd.comp_ofReal
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdr
  have he : (fun t : ℝ => (p2FullNumerator38 n (s+(t : ℂ) • h) (x : ℂ)).im) =
      (fun _t : ℝ => (0 : ℝ)) := by
    funext t
    apply p2FullNumerator_real38 n _ _ x
    intro k
    simp only [lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Complex.add_im,Complex.mul_im,hs k,hh k,Complex.ofReal_im,
      mul_zero,zero_mul,add_zero]
  change HasDerivAt
    (fun t : ℝ => (p2FullNumerator38 n (s+(t : ℂ) • h) (x : ℂ)).im)
    (p4NumeratorVariation38 n s h (x : ℂ)).im 0 at him
  rw [he] at him
  exact him.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))

end
end NlsGge.GK38.P4NumeratorVariation
