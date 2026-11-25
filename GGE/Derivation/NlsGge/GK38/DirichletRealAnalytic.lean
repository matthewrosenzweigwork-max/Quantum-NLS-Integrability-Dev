import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.GK38.DirichletRealAnalyticAlgebra
import NlsGge.GK38.RealTypeMultiplicityRealDeriv
import NlsGge.GK38.Lib.ProperLocalHomeo

/-! Real Banach analyticity of the actual Dirichlet labels via an explicit triangular chart.
Private source anchor: book I.7 simple-root analytic argument. -/
set_option autoImplicit false
open Filter Topology Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def dirichletRealChar38 (p : PhysicalL2 × ℝ) : ℝ :=
  (dirichletChar (realSlice p.1) (p.2 : ℂ)).re

theorem analyticAt_dirichletRealChar38 (p : PhysicalL2 × ℝ) :
    AnalyticAt ℝ dirichletRealChar38 p := by
  have hA : AnalyticAt ℝ (fun q : PhysicalL2 × ℝ => (realSlice q.1, (q.2 : ℂ))) p :=
    ((realSlice.analyticAt p.1).comp (analyticAt_fst (𝕜 := ℝ))).prod
      ((Complex.ofRealCLM.analyticAt p.2).comp (analyticAt_snd (𝕜 := ℝ)))
  have hχ := AnalyticAt.comp
    (g := fun q : PotPair × ℂ => dirichletChar q.1 q.2)
    (f := fun q : PhysicalL2 × ℝ => (realSlice q.1, (q.2 : ℂ)))
    ((analyticOnNhd_dirichletChar (realSlice p.1, (p.2 : ℂ))
    (mem_univ _)).restrictScalars (𝕜 := ℝ)) hA
  have hcomp := AnalyticAt.comp (g := fun z : ℂ => z.re)
    (f := fun q : PhysicalL2 × ℝ => dirichletChar (realSlice q.1) (q.2 : ℂ))
    (Complex.reCLM.analyticAt _) hχ
  unfold dirichletRealChar38
  simpa only [Function.comp_def] using hcomp

theorem dirichletRealChar_partial_ne_zero38 (u : PhysicalL2) (x : ℝ)
    (hx : dirichletChar (realSlice u) (x : ℂ) = 0) :
    (fderiv ℝ dirichletRealChar38 (u, x)) (0, 1) ≠ 0 := by
  have hD := (analyticAt_dirichletRealChar38 (u, x)).differentiableAt.hasFDerivAt
  have hp : HasDerivAt (fun r : ℝ => (u, r)) (0, 1) x :=
    (hasDerivAt_const x u).prodMk (hasDerivAt_id x)
  have hρ : HasDerivAt (fun r : ℝ => dirichletRealChar38 (u, r))
      ((fderiv ℝ dirichletRealChar38 (u, x)) (0, 1)) x := by
    simpa only [Function.comp_def] using hD.comp_hasDerivAt x hp
  have hf : Differentiable ℂ (dirichletChar (realSlice u)) := fun z =>
    ((analyticOnNhd_dirichletChar_z (realSlice u)) z (mem_univ _)).differentiableAt
  have hr := realRestriction_deriv38 _ hf (fun r => (dirichlet_real_characteristic38 u r).1) x
  intro hz
  have he : deriv (fun r : ℝ => (dirichletChar (realSlice u) (r : ℂ)).re) x = 0 := by
    simpa only [dirichletRealChar38] using hρ.deriv.trans hz
  exact dirichlet_root_deriv_ne_zero38 u x hx (hr.2.2.mp he)

theorem analyticAt_gkMu38 (u₀ : PhysicalL2) (n : ℤ) :
    AnalyticAt ℝ (fun u : PhysicalL2 => gkMu u n) u₀ := by
  let x₀ := gkMu u₀ n
  let F : PhysicalL2 × ℝ → PhysicalL2 × ℝ := fun p => (p.1, dirichletRealChar38 p)
  have hF : AnalyticAt ℝ F (u₀, x₀) :=
    (analyticAt_fst (𝕜 := ℝ)).prod (analyticAt_dirichletRealChar38 (u₀, x₀))
  have hd : fderiv ℝ F (u₀, x₀) =
      (ContinuousLinearMap.fst ℝ PhysicalL2 ℝ).prod
        (fderiv ℝ dirichletRealChar38 (u₀, x₀)) :=
    (hasFDerivAt_fst.prodMk
      (analyticAt_dirichletRealChar38 (u₀, x₀)).differentiableAt.hasFDerivAt).fderiv
  have hinv : (fderiv ℝ F (u₀, x₀)).IsInvertible := by
    rw [hd]
    exact dirichlet_triangular_invertible38 _
      (dirichletRealChar_partial_ne_zero38 u₀ x₀ (gkMu_root38 u₀ n))
  obtain ⟨e, he, hEF, han⟩ := Lib.exists_analytic_chart hF hinv
  have hvalue : F (u₀, x₀) = (u₀, 0) := by
    apply Prod.ext
    · rfl
    · change (dirichletChar (realSlice u₀) (gkMu u₀ n : ℂ)).re = 0
      rw [gkMu_root38]; rfl
  rw [hvalue] at han
  have hinverse : AnalyticAt ℝ (fun u : PhysicalL2 => e.symm (u, (0 : ℝ))) u₀ := by
    have hcomp := AnalyticAt.comp (g := fun p : PhysicalL2 × ℝ => e.symm p)
      (f := fun u : PhysicalL2 => (u, (0 : ℝ))) han
      ((analyticAt_id (𝕜 := ℝ)).prod (analyticAt_const (v := (0 : ℝ))))
    simpa only [Function.comp_def] using hcomp
  have hbranch : AnalyticAt ℝ (fun u : PhysicalL2 => (e.symm (u, 0)).2) u₀ := by
    have hcomp := AnalyticAt.comp (g := fun p : PhysicalL2 × ℝ => p.2)
      (f := fun u : PhysicalL2 => e.symm (u, (0 : ℝ))) (analyticAt_snd (𝕜 := ℝ)) hinverse
    simpa only [Function.comp_def] using hcomp
  apply hbranch.congr
  have hgraph : Continuous (fun u : PhysicalL2 => (u, gkMu u n)) :=
    continuous_id.prodMk (continuous_gkMu38 n)
  have hsource : ∀ᶠ u in 𝓝 u₀, (u, gkMu u n) ∈ e.source :=
    hgraph.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds he)
  filter_upwards [hsource] with u hu
  have hev : e (u, gkMu u n) = (u, 0) := by
    rw [hEF]
    apply Prod.ext
    · rfl
    · change (dirichletChar (realSlice u) (gkMu u n : ℂ)).re = 0
      rw [gkMu_root38]; rfl
  have hi := e.left_inv hu
  rw [hev] at hi
  exact congrArg Prod.snd hi

theorem analyticOnNhd_gkMu38 (n : ℤ) :
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => gkMu u n) univ := fun u _ => analyticAt_gkMu38 u n

theorem analyticOnNhd_deltaMu38 (n : ℤ) :
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => deltaMu u n) univ := by
  intro u _
  have hA : AnalyticAt ℝ (fun v : PhysicalL2 => (realSlice v, (gkMu v n : ℂ))) u :=
    (realSlice.analyticAt u).prod
      (AnalyticAt.comp (g := fun x : ℝ => (x : ℂ)) (f := fun v : PhysicalL2 => gkMu v n)
        (Complex.ofRealCLM.analyticAt (gkMu u n)) (analyticAt_gkMu38 u n))
  have hδ := AnalyticAt.comp
    (g := fun q : PotPair × ℂ => antiDiscrim q.1 q.2)
    (f := fun v : PhysicalL2 => (realSlice v, (gkMu v n : ℂ)))
    ((analyticOnNhd_antiDiscrim (realSlice u, (gkMu u n : ℂ))
    (mem_univ _)).restrictScalars (𝕜 := ℝ)) hA
  have hcomp := AnalyticAt.comp (g := fun z : ℂ => z.re)
    (f := fun v : PhysicalL2 => antiDiscrim (realSlice v) (gkMu v n : ℂ))
    (Complex.reCLM.analyticAt _) hδ
  simpa only [Function.comp_def, deltaMu] using hcomp

end
end NlsGge.GK38
