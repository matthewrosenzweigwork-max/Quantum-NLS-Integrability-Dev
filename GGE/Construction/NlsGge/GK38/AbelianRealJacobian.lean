import NlsGge.GK38.AbelianRealSequenceSpace
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! Actual real restriction and its derivative, before any Omega/diagonal/HS bounds.
UNCOMPILED source preparation. The real operator is the derivative of actual Fn. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- Concrete actual sequence function at a fixed real potential. -/
def p3ComplexSequenceFn38 (n : ℤ) (u : PhysicalL2) : P2Space38 n → P2Space38 n :=
  fun s => p2Fn38 n (realSlice u,s)

theorem p3ComplexSequenceFn_analytic38 (n : ℤ) (u : PhysicalL2) :
    AnalyticOnNhd ℂ (p3ComplexSequenceFn38 n u) univ := by
  intro s _
  exact AnalyticAt.comp
    (g := p2Fn38 n) (f := fun t : P2Space38 n => (realSlice u,t))
    (p2Fn_analytic38 n (realSlice u,s) ⟨realSlice_mem_gkW u,mem_univ _⟩)
    (analyticAt_const.prod analyticAt_id)

/-- The actual Fn in genuine real omitted Hilbert coordinates. -/
def p3RealFn38 (n : ℤ) (u : PhysicalL2) (s : P3RealSpace38 n) : P3RealSpace38 n :=
  p3RealPart38 n (p3ComplexSequenceFn38 n u (p3RealInclude38 n s))

theorem p3RealFn_graph38 (n : ℤ) (u : PhysicalL2) (s : P3RealSpace38 n) :
    p3RealInclude38 n (p3RealFn38 n u s) =
      p2Fn38 n (realSlice u,p3RealInclude38 n s) := by
  apply p3RealInclude_realPart38 n
  intro m
  exact p2Fn_real38 n u (p3RealInclude38 n s)
    (fun j => by simp only [p3RealInclude_apply38, Complex.ofReal_im]) m

theorem p3RealFn_analytic38 (n : ℤ) (u : PhysicalL2) :
    AnalyticOnNhd ℝ (p3RealFn38 n u) univ := by
  intro s _
  have hf := (p3ComplexSequenceFn_analytic38 n u (p3RealInclude38 n s)
    (mem_univ _)).restrictScalars (𝕜 := ℝ)
  have hJ := (p3RealIncludeCLM38 n).analyticAt s
  have hc : AnalyticAt ℝ
      (fun t : P3RealSpace38 n => p3ComplexSequenceFn38 n u (p3RealInclude38 n t)) s :=
    AnalyticAt.comp
      (g := p3ComplexSequenceFn38 n u)
      (f := fun t : P3RealSpace38 n => p3RealIncludeCLM38 n t) hf hJ
  exact AnalyticAt.comp
    (g := p3RealPart38 n)
    (f := fun t : P3RealSpace38 n => p3ComplexSequenceFn38 n u (p3RealInclude38 n t))
    ((p3RealPart38 n).analyticAt _) hc

/-- Genuine real differentiation commutes with the concrete inclusion. -/
theorem p3RealFn_fderiv_include38 (n : ℤ) (u : PhysicalL2) (s : P3RealSpace38 n) :
    (p3RealIncludeCLM38 n).comp (fderiv ℝ (p3RealFn38 n u) s) =
      ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
        (p3RealInclude38 n s)).restrictScalars ℝ).comp (p3RealIncludeCLM38 n) := by
  let f : P2Space38 n → P2Space38 n := p3ComplexSequenceFn38 n u
  let J : P3RealSpace38 n →L[ℝ] P2Space38 n := p3RealIncludeCLM38 n
  have hf : HasFDerivAt f (fderiv ℂ f (J s)) (J s) :=
    (p3ComplexSequenceFn_analytic38 n u (J s) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcomplex := (hf.restrictScalars ℝ).comp s (J.hasFDerivAt (x := s))
  have hreal : HasFDerivAt (p3RealFn38 n u) (fderiv ℝ (p3RealFn38 n u) s) s :=
    (p3RealFn_analytic38 n u s (mem_univ _)).differentiableAt.hasFDerivAt
  have hinclude := (J.hasFDerivAt).comp s hreal
  have heq : J ∘ p3RealFn38 n u = f ∘ J := by
    funext t
    exact p3RealFn_graph38 n u t
  rw [heq] at hinclude
  exact hinclude.unique hcomplex

/-- The concrete inclusion carries each real unit vector to its complex unit vector. -/
theorem p3RealInclude_single38 (n : ℤ) (r : P2Index38 n) :
    p3RealInclude38 n (lp.single 2 r (1 : ℝ)) = lp.single 2 r (1 : ℂ) := by
  apply Subtype.ext
  funext m
  by_cases hm : m = r
  · subst m
    simp only [p3RealInclude_apply38, lp.single_apply_self, Complex.ofReal_one]
  · simp only [p3RealInclude_apply38,
      lp.single_apply_ne (E := fun _ : P2Index38 n => ℝ) 2 r (1 : ℝ) hm,
      lp.single_apply_ne (E := fun _ : P2Index38 n => ℂ) 2 r (1 : ℂ) hm,
      Complex.ofReal_zero]

/-- Matrix reality follows from the actual derivative restriction, on every real input. -/
theorem p3RealJacobian_matrix_im_zero38 (n : ℤ) (u : PhysicalL2)
    (s : P3RealSpace38 n) (m r : P2Index38 n) :
    ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)) (lp.single 2 r (1 : ℂ)) m).im = 0 := by
  have hb := p3RealFn_fderiv_include38 n u s
  have he := congrArg
    (fun T : P3RealSpace38 n →L[ℝ] P2Space38 n => T (lp.single 2 r (1 : ℝ)) m) hb
  have hJ : p3RealIncludeCLM38 n (lp.single 2 r (1 : ℝ)) =
      lp.single 2 r (1 : ℂ) := p3RealInclude_single38 n r
  simp only [ContinuousLinearMap.comp_apply, hJ] at he
  change (((fderiv ℝ (p3RealFn38 n u) s) (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ) =
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t))
      (p3RealInclude38 n s)) (lp.single 2 r (1 : ℂ)) m at he
  rw [← he]
  exact Complex.ofReal_im _

end
end NlsGge.GK38
