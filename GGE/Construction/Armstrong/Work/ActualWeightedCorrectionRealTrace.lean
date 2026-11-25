import Armstrong.Work.RealQuadraticODEInvariant
import Armstrong.Work.CartesianContinuationSpec
import Armstrong.Work.ActualTerminalRootRealTrace
import NlsGge.GK38.AbelianJacobianGeometry
import NlsGge.GK38.AbelianRealSequenceSpace
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Ring

/-!
# Literal original weighted correction on the real slice

SPECULATIVE_PARENT_UNACCEPTED, RT-WEIGHTED-013. The same actual normalized
family supplies the real numerator coefficients and own period. The actual
filled-disc correction ODE and weighted real-axis invariant earn a purely
imaginary terminal product, including real collapsed gaps and both tips.
No coefficient reality, real rooted path, gap division or uniform bound is
assumed. This is a pointwise prerequisite, not a Cartesian-map theorem.
-/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem gk16_same_family_actual_weighted_correction_real_trace38
    (W : Set PotPair) (hreal : Set.range realSlice ⊆ W)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : NlsGge.Pilot.PhysicalL2),
      ∃ t : P3RealSpace38 n,
        t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
          F n (realSlice u) = p3RealInclude38 n t)
    (u : NlsGge.Pilot.PhysicalL2) (n : ℤ) :
    (gk16TerminalRoot38 n (realSlice u) *
      gk16OwnCorrectionCoefficient38 (realSlice u) n
        (p2Extend38 n (F n (realSlice u)))
        (discC (realSlice u) n) (discR (realSlice u) n)
        (muSeq (realSlice u) n)).re = 0 := by
  classical
  let phi : PotPair := realSlice u
  let s0 : Lib.L2Seq := p2Extend38 n (F n phi)
  let c : ℂ := discC phi n
  let r : ℝ := discR phi n
  let a : ℂ := lamMinus phi n
  let b : ℂ := lamPlus phi n
  let ar : ℝ := NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n
  let br : ℝ := NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n
  let x0 : ℝ := gkMu u n
  let T : ℂ → ℂ := gk16OwnCorrectionCoefficient38 phi n s0 c r
  let Q : ℂ → ℂ := fun z => (z-a)*(z-b)
  let q : ℂ → ℂ := fun z => p2OmittedRatio38 n ((phi,s0),z)
  let U : Set ℝ := (fun x : ℝ => (x : ℂ)) ⁻¹' ball c r
  have hphiW : phi ∈ W := hreal (mem_range_self u)
  have hphiGK : phi ∈ gkW := realSlice_mem_gkW u
  have hfam : IsolatingFamily38 phi (discC phi) (discR phi) :=
    isolating_family38 phi hphiGK
  obtain ⟨t,_ht,_htzero,hFbase⟩ := hFreal n u
  have hsReal : ∀ k : ℤ, (s0 k).im = 0 := by
    intro k
    change ((p2Extend38 n (F n (realSlice u))) k).im = 0
    by_cases hk : k = n
    · subst k
      simp only [p2Extend_self38,Complex.zero_im]
    · rw [p2Extend_at38 n (F n (realSlice u)) ⟨k,hk⟩,
        hFbase,p3RealInclude_apply38]
      exact Complex.ofReal_im (t ⟨k,hk⟩)
  have hqReal : ∀ x ∈ U, (q (x : ℂ)).im = 0 := by
    intro x hx
    have hxBall : (x : ℂ) ∈ ball c r := hx
    have hp : (phi,(x : ℂ)) ∈ a5OmittedRootDomain38 n :=
      a5OwnClosedBall_omittedDomain38 phi hphiGK (discC phi) (discR phi)
        hfam n (x : ℂ) (ball_subset_closedBall hxBall)
    exact P3JacobianColumns.omittedRatio_real u s0 hsReal n x hp
  have hown : abelianPeriod38 n phi (p2FullNumerator38 n s0) =
      2 * (Real.pi : ℂ) :=
    (hperiod n phi hphiW n).trans (if_pos (show n = n from rfl))
  have hdata := gk16_own_correction_coefficient38 phi hphiGK
    (discC phi) (discR phi) hfam n s0 hown
  have hTan : AnalyticOnNhd ℂ T (ball c r) := hdata.1
  have hODEoriginal : ∀ z ∈ ball c r,
      Q z * deriv T z + (z-(a+b)/2)*T z = q z-1 := hdata.2
  have hUopen : IsOpen U := isOpen_ball.preimage Complex.continuous_ofReal
  have hUconvex : Convex ℝ U :=
    (convex_ball c r).linear_preimage Complex.ofRealCLM.toLinearMap
  have hUc : IsPreconnected U := hUconvex.isPreconnected
  have ha : a = (ar : ℂ) := (lamPlus_real u n).2
  have hb : b = (br : ℂ) := (lamPlus_real u n).1
  have hmu : muSeq phi n = (x0 : ℂ) := muSeq_eq_gkMu38 u n
  have hfamCopy := hfam
  obtain ⟨_cgeom,_N,_hgeom,hspec⟩ := hfamCopy
  have haU : ar ∈ U := by
    change (ar : ℂ) ∈ ball c r
    rw [← ha]
    exact (hspec.1 n).1 (left_mem_segment ℝ a b)
  have hxU : x0 ∈ U := by
    change (x0 : ℂ) ∈ ball c r
    rw [← hmu]
    exact (hspec.1 n).2.1
  have hQderiv (z : ℂ) : HasDerivAt Q ((z-b)+(z-a)) z := by
    change HasDerivAt (fun w : ℂ => (w-a)*(w-b)) ((z-b)+(z-a)) z
    simpa only [Pi.mul_def,id_eq,one_mul,mul_one] using
      (((hasDerivAt_id z).sub_const a).mul ((hasDerivAt_id z).sub_const b))
  have hQreal : ∀ x ∈ U, (Q (x : ℂ)).im = 0 := by
    intro x _hx
    simp only [Q,ha,hb,Complex.mul_im,Complex.sub_im,Complex.ofReal_im,
      sub_self,mul_zero,zero_mul,add_zero]
  have hPsireal : ∀ x ∈ U, (q (x : ℂ)-1).im = 0 := by
    intro x hx
    simpa only [Complex.sub_im,Complex.one_im,sub_zero] using hqReal x hx
  have hODE : ∀ x ∈ U,
      Q (x : ℂ)*deriv T (x : ℂ) +
        (deriv Q (x : ℂ)/2)*T (x : ℂ) = q (x : ℂ)-1 := by
    intro x hx
    rw [(hQderiv (x : ℂ)).deriv]
    have hmid : (((x : ℂ)-b)+((x : ℂ)-a))/2 =
        (x : ℂ)-(a+b)/2 := by ring
    rw [hmid]
    exact hODEoriginal (x : ℂ) hx
  have hQa : Q (ar : ℂ) = 0 := by
    simp only [Q,ha,sub_self,zero_mul]
  have hInvariant := gk_real_axis_weighted_ode_invariant38 U hUopen hUc
    Q T (fun z => q z-1)
    (fun x _hx => (hQderiv (x : ℂ)).differentiableAt)
    (fun x hx => (hTan (x : ℂ) hx).differentiableAt)
    hQreal hPsireal hODE ar x0 haU hxU hQa
  let h : ℂ := gk16TerminalRoot38 n phi
  have hRe : h.re = 0 := gk16_terminal_root_real_trace38 u n
  have hSquare : h^2 = Q (x0 : ℂ) := by
    change (gk16TerminalRoot38 n phi)^2 =
      ((x0 : ℂ)-lamMinus phi n)*((x0 : ℂ)-lamPlus phi n)
    simpa only [hmu] using gk16_terminal_root_sq38 n phi hphiGK
  have hSquareRe := congrArg Complex.re hSquare
  simp only [pow_two,Complex.mul_re,hRe,zero_mul,zero_sub] at hSquareRe
  have hProductSquare : (h.im*(T (x0 : ℂ)).im)^2 = 0 := by
    calc
      _ = -(Q (x0 : ℂ)).re*((T (x0 : ℂ)).im)^2 := by
        rw [← hSquareRe]
        ring
      _ = 0 := by rw [neg_mul,hInvariant,neg_zero]
  have hProduct : h.im*(T (x0 : ℂ)).im = 0 := sq_eq_zero_iff.mp hProductSquare
  change (h*T (muSeq phi n)).re = 0
  rw [hmu]
  simp only [Complex.mul_re,hRe,zero_mul,zero_sub,hProduct,neg_zero]

end
end NlsGge.GK38
