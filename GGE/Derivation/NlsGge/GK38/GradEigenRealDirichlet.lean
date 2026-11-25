import NlsGge.GK38.GradEigenRealState
import NlsGge.GK38.GradEigenDirichlet
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem actual_dirichlet_label_complex_gradient (u : PhysicalL2) (n : ℤ)
    (h : PhysicalL2) :
    ((fderiv ℝ (fun v : PhysicalL2 => gkMu v n) u) h : ℂ) =
      dirImplicitGradient (realSlice u) (gkMu u n : ℂ) (realSlice h) := by
  let r : PhysicalL2 → ℝ := fun v => gkMu v n
  let dr := fderiv ℝ r u
  let f : PotPair × ℂ → ℂ := fun p => dirichletChar p.1 p.2
  let D := fderiv ℂ f (realSlice u,(r u : ℂ))
  let d := deriv (dirichletChar (realSlice u)) (r u : ℂ)
  have hr : HasFDerivAt r dr u := (analyticAt_gkMu38 u n).differentiableAt.hasFDerivAt
  have hf : HasFDerivAt f D (realSlice u,(r u : ℂ)) :=
    (analyticOnNhd_dirichletChar (realSlice u,(r u : ℂ)) (mem_univ _)).differentiableAt.hasFDerivAt
  have hgraph : HasFDerivAt (fun v : PhysicalL2 => (realSlice v,(r v : ℂ)))
      (realSlice.prod (Complex.ofRealCLM.comp dr)) u :=
    realSlice.hasFDerivAt.prodMk (Complex.ofRealCLM.hasFDerivAt.comp u hr)
  have hz := (hf.restrictScalars ℝ).comp u hgraph
  have heq : (fun v : PhysicalL2 => f (realSlice v,(r v : ℂ))) = fun _ => (0 : ℂ) := by
    funext v
    exact gkMu_root38 v n
  simp only [Function.comp_def] at hz
  rw [heq] at hz
  have hz' := congrArg (fun L : PhysicalL2 →L[ℝ] ℂ => L h)
    (hz.unique (hasFDerivAt_const (0 : ℂ) u))
  change D (realSlice h,(dr h : ℂ)) = 0 at hz'
  have hp : D (realSlice h,0) = dirCLM (realSlice u) (r u : ℂ) (realSlice h) := by
    exact congrArg (fun L : PotPair →L[ℂ] ℂ => L (realSlice h))
      (dirichlet_joint_potential_partial (realSlice u) (r u : ℂ))
  have hs : D (0,1) = d := dirichlet_joint_spectral_partial (realSlice u) (r u : ℂ)
  have hdecomp : D (realSlice h,(dr h : ℂ)) =
      dirCLM (realSlice u) (r u : ℂ) (realSlice h) + (dr h : ℂ)*d := by
    calc
      D (realSlice h,(dr h : ℂ)) = D ((realSlice h,0) + (dr h : ℂ) • (0,1)) := by
        congr 1
        simp
      _ = D (realSlice h,0) + (dr h : ℂ) * D (0,1) := by rw [map_add,map_smul]; rfl
      _ = _ := by rw [hp,hs]
  have hd : d ≠ 0 := dirichlet_root_deriv_ne_zero38 u (r u) (gkMu_root38 u n)
  rw [hdecomp] at hz'
  change (dr h : ℂ) = -d⁻¹ * dirCLM (realSlice u) (r u : ℂ) (realSlice h)
  field_simp
  linear_combination hz'

theorem actual_dirichlet_label_hasFDerivAt (u : PhysicalL2) (n : ℤ) :
    HasFDerivAt (fun v : PhysicalL2 => gkMu v n) (realEnergyGradient (dirState u n)) u := by
  have hr := (analyticAt_gkMu38 u n).differentiableAt.hasFDerivAt
  have hd : fderiv ℝ (fun v : PhysicalL2 => gkMu v n) u = realEnergyGradient (dirState u n) := by
    apply ContinuousLinearMap.ext
    intro h
    have hc := actual_dirichlet_label_complex_gradient u n h
    rw [complex_dirichlet_gradient_identity (realSlice u) (gkMu u n : ℂ)
      (gkMu_root38 u n) (dirichlet_root_deriv_ne_zero38 u (gkMu u n) (gkMu_root38 u n))] at hc
    have hre := congrArg Complex.re hc
    change (fderiv ℝ (fun v : PhysicalL2 => gkMu v n) u) h =
      (bilinearGradient (dirState u n) (realSlice h)).re at hre
    rw [bilinear_real_energy _ (dirState_real_symmetry u n)] at hre
    exact hre
  rw [hd] at hr
  exact hr

def RealDirichletGradientTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ),
    realSymmetric (dirState u n) ∧ 0 < energy (dirState u n) ∧
    HasFDerivAt (fun v : PhysicalL2 => gkMu v n) (realEnergyGradient (dirState u n)) u

theorem real_dirichlet_gradient_target : RealDirichletGradientTarget := by
  intro u n
  exact ⟨dirState_real_symmetry u n,dirState_energy_positive u n,
    actual_dirichlet_label_hasFDerivAt u n⟩

end
end NlsGge.GK38.GradEigen38
