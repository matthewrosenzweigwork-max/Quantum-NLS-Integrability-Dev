import Armstrong.Work.ActualScalarCartesianModels
import Armstrong.Work.ActualTerminalRootRealTrace
import Armstrong.Work.ActualWeightedCorrectionRealTrace
import NlsGge.GK38.TauGamma
import NlsGge.GK38.DirichletRealReality

/-!
# Actual signed scalar Z conjugation

SPECULATIVE_UNCOMPILED_WEIGHTED_PARENT, task SIGNED_Z_REAL_TRACE_014.
Exactly one reviewed theorem, zero definitions. The literal original F/own
coefficient/disc data are retained. Weighted reality is earned inside the proof.
All real potentials and signed modes are covered, including collapsed gaps and
terminal tips. No division, beta, XY, action or complex-collapse claim is used.
-/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- The literal original plus model conjugates to the literal original minus
model on the actual real slice, without any noncollapse or tip restriction. -/
theorem gk16_same_family_scalar_models_conj38
    (W : Set PotPair) (hreal : range realSlice ⊆ W)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (n : ℤ) (u : PhysicalL2) :
    star (gk16ActualScalarZPlus38 F n (realSlice u)) =
      gk16ActualScalarZMinus38 F n (realSlice u) := by
  let H : ℂ := gk16TerminalRoot38 n (realSlice u)
  let w : ℂ := H *
    gk16OwnCorrectionCoefficient38 (realSlice u) n
      (p2Extend38 n (F n (realSlice u)))
      (discC (realSlice u) n) (discR (realSlice u) n)
      (muSeq (realSlice u) n)
  have hHre : H.re = 0 := gk16_terminal_root_real_trace38 u n
  have hwre : w.re = 0 :=
    gk16_same_family_actual_weighted_correction_real_trace38 W hreal F
      hperiod hFreal u n
  have hHconj : (starRingEnd ℂ) H = -H := by
    apply Complex.ext
    · simp only [Complex.conj_re,Complex.neg_re,hHre,neg_zero]
    · simp only [Complex.conj_im,Complex.neg_im]
  have hwconj : (starRingEnd ℂ) (-w) = w := by
    apply Complex.ext
    · simp only [Complex.conj_re,Complex.neg_re,hwre,neg_zero]
    · simp only [Complex.conj_im,Complex.neg_im,neg_neg]
  have htau : (starRingEnd ℂ) (tauN (realSlice u) n) =
      tauN (realSlice u) n := by
    rw [(tauGamma_real38 u n).1,Complex.conj_ofReal]
  have hmu : (starRingEnd ℂ) (muSeq (realSlice u) n) =
      muSeq (realSlice u) n := by
    rw [muSeq_eq_gkMu38 u n,Complex.conj_ofReal]
  have hpref : (starRingEnd ℂ)
      (2*(tauN (realSlice u) n-muSeq (realSlice u) n)+2*H) =
        2*(tauN (realSlice u) n-muSeq (realSlice u) n)-2*H := by
    simp only [map_add,map_mul,map_sub,map_ofNat,htau,map_neg,hmu,hHconj,
      mul_neg,sub_eq_add_neg]
  change (starRingEnd ℂ)
      ((2*(tauN (realSlice u) n-muSeq (realSlice u) n)+2*H) *
        Complex.exp (-w)) =
    (2*(tauN (realSlice u) n-muSeq (realSlice u) n)-2*H) *
      Complex.exp w
  rw [map_mul,hpref,← Complex.exp_conj,hwconj]

end
end NlsGge.GK38
