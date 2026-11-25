import NlsGge.GK38.AbelianFixedGapCube

/-! Uncompiled actual solution topology prefix. Joint continuity and compact
closed-gap fibers are earned; no local inverse, finite fibers or properness
is assumed or concluded in this module. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5RealJointFn_analytic38 (n : ℤ) : AnalyticOnNhd ℝ
    (fun p : PhysicalL2 × P3RealSpace38 n => p3RealFn38 n p.1 p.2) univ := by
  intro p _
  have hf := (p2Fn_analytic38 n (realSlice p.1,p3RealInclude38 n p.2)
    ⟨realSlice_mem_gkW p.1,mem_univ _⟩).restrictScalars (𝕜 := ℝ)
  have hmap : AnalyticAt ℝ
      (fun q : PhysicalL2 × P3RealSpace38 n => (realSlice q.1,p3RealInclude38 n q.2)) p :=
    ((realSlice.analyticAt p.1).comp analyticAt_fst).prod
      (((p3RealIncludeCLM38 n).analyticAt p.2).comp analyticAt_snd)
  have hc : AnalyticAt ℝ
      (fun q : PhysicalL2 × P3RealSpace38 n =>
        p2Fn38 n (realSlice q.1,p3RealInclude38 n q.2)) p :=
    AnalyticAt.comp (g := p2Fn38 n)
      (f := fun q : PhysicalL2 × P3RealSpace38 n =>
        (realSlice q.1,p3RealInclude38 n q.2)) hf hmap
  exact AnalyticAt.comp (g := p3RealPart38 n)
    (f := fun q : PhysicalL2 × P3RealSpace38 n =>
      p2Fn38 n (realSlice q.1,p3RealInclude38 n q.2))
    ((p3RealPart38 n).analyticAt _) hc

theorem p5RealJointFn_continuous38 (n : ℤ) :
    Continuous (fun p : PhysicalL2 × P3RealSpace38 n => p3RealFn38 n p.1 p.2) :=
  continuous_iff_continuousAt.mpr (fun p =>
    (p5RealJointFn_analytic38 n p (mem_univ _)).continuousAt)

def p5RealSolutionFiber38 (n : ℤ) (u : PhysicalL2) : Set (P3RealSpace38 n) :=
  {t | t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0}

theorem p5RealSolutionFiber_isCompact38 (n : ℤ) (u : PhysicalL2) :
    IsCompact (p5RealSolutionFiber38 n u) := by
  have hcont : Continuous (p3RealFn38 n u) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (p3RealFn_analytic38 n u t (mem_univ _)).continuousAt)
  have hc : IsClosed {t : P3RealSpace38 n | p3RealFn38 n u t=0} :=
    isClosed_singleton.preimage hcont
  apply (p5RealGapCube_isCompact38 n u).of_isClosed_subset
    ((p5RealGapCube_isCompact38 n u).isClosed.inter hc)
  exact inter_subset_left

end
end NlsGge.GK38
