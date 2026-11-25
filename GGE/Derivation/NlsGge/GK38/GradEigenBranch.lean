import NlsGge.GK38.GradEigenCharacteristic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section
theorem complex_linear_split (L : PotPair × ℂ →L[ℂ] ℂ) (p : PotPair × ℂ) :
    L p = L (p.1,0) + p.2 * L (0,1) := by
  have he : p = (p.1,0) + p.2 • ((0 : PotPair),(1 : ℂ)) := by
    ext <;> simp
  calc L p = L ((p.1,0) + p.2 • ((0 : PotPair),(1 : ℂ))) := congrArg L he
    _ = _ := by rw [map_add, map_smul]; rfl

theorem complex_triangular_equiv (L : PotPair × ℂ →L[ℂ] ℂ) (hc : L (0,1) ≠ 0) :
    ∃ e : (PotPair × ℂ) ≃L[ℂ] (PotPair × ℂ),
      (e : (PotPair × ℂ) →L[ℂ] (PotPair × ℂ)) =
        (ContinuousLinearMap.fst ℂ PotPair ℂ).prod L := by
  let D := (ContinuousLinearMap.fst ℂ PotPair ℂ).prod L
  let invD : PotPair × ℂ →L[ℂ] PotPair × ℂ :=
    (ContinuousLinearMap.fst ℂ PotPair ℂ).prod ((L (0,1))⁻¹ •
      ((ContinuousLinearMap.snd ℂ PotPair ℂ) -
        (L.comp potentialInclusion).comp (ContinuousLinearMap.fst ℂ PotPair ℂ)))
  have hl : Function.LeftInverse invD D := by
    intro p
    apply Prod.ext
    · rfl
    · change (L (0,1))⁻¹ * (L p - L (p.1,0)) = p.2
      rw [complex_linear_split L p]
      field_simp
      ring
  have hr : Function.RightInverse invD D := by
    intro p
    apply Prod.ext
    · rfl
    · change L (p.1, (L (0,1))⁻¹ * (p.2 - L (p.1,0))) = p.2
      rw [complex_linear_split L (p.1, (L (0,1))⁻¹ * (p.2 - L (p.1,0)))]
      field_simp
      ring
  exact ⟨ContinuousLinearEquiv.equivOfInverse D invD hl hr, rfl⟩

theorem complex_analytic_root (f : PotPair × ℂ → ℂ) (φ : PotPair) (z : ℂ)
    (hf : AnalyticAt ℂ f (φ,z)) (hroot : f (φ,z) = 0)
    (hc : fderiv ℂ f (φ,z) (0,1) ≠ 0) :
    ∃ κ : PotPair → ℂ, AnalyticAt ℂ κ φ ∧ κ φ = z ∧
      ∀ᶠ ψ in 𝓝 φ, f (ψ,κ ψ) = 0 := by
  let L := fderiv ℂ f (φ,z)
  obtain ⟨e, he⟩ := complex_triangular_equiv L hc
  let F : PotPair × ℂ → PotPair × ℂ := fun p => (p.1, f p)
  have hFa : AnalyticAt ℂ F (φ,z) := (analyticAt_fst (𝕜 := ℂ)).prod hf
  have hFd : HasStrictFDerivAt F (e : (PotPair × ℂ) →L[ℂ] (PotPair × ℂ)) (φ,z) := by
    rw [he]
    exact hasStrictFDerivAt_fst.prodMk hf.hasStrictFDerivAt
  let chart := hFd.toOpenPartialHomeomorph F
  have hchart : (chart : PotPair × ℂ → PotPair × ℂ) = F := rfl
  have hsrc : (φ,z) ∈ chart.source := hFd.mem_toOpenPartialHomeomorph_source
  have hpt : F (φ,z) = (φ,0) := by simp only [F, hroot]
  have htgt : (φ,0) ∈ chart.target := by
    have ht := chart.map_source hsrc
    rwa [hchart, hpt] at ht
  have hvalue : chart.symm (φ,0) = (φ,z) := by
    have hv := chart.left_inv hsrc
    rwa [hchart, hpt] at hv
  have hInv : AnalyticAt ℂ chart.symm (φ,0) := by
    have ha := chart.analyticAt_symm' hsrc hFa hFd.hasFDerivAt.fderiv
    rwa [hchart, hpt] at ha
  have hcurve : AnalyticAt ℂ (fun ψ : PotPair => (ψ,(0 : ℂ))) φ :=
    (analyticAt_id (𝕜 := ℂ)).prod analyticAt_const
  have hcomp : AnalyticAt ℂ (fun ψ : PotPair => chart.symm (ψ,0)) φ := by
    exact AnalyticAt.comp (g := fun p : PotPair × ℂ => chart.symm p)
      (f := fun ψ : PotPair => (ψ,(0 : ℂ))) hInv hcurve
  refine ⟨fun ψ => (chart.symm (ψ,0)).2, ?_, ?_, ?_⟩
  · exact AnalyticAt.comp (g := fun p : PotPair × ℂ => p.2)
      (f := fun ψ : PotPair => chart.symm (ψ,(0 : ℂ))) (analyticAt_snd (𝕜 := ℂ)) hcomp
  · show (chart.symm (φ,0)).2 = z
    rw [hvalue]
  · have hev : ∀ᶠ ψ in 𝓝 φ, (ψ,(0 : ℂ)) ∈ chart.target :=
      hcurve.continuousAt.preimage_mem_nhds (chart.open_target.mem_nhds htgt)
    filter_upwards [hev] with ψ hψ
    have hr := chart.right_inv hψ
    rw [hchart] at hr
    have hfirst := congrArg Prod.fst hr
    have hsecond := congrArg Prod.snd hr
    change (chart.symm (ψ,0)).1 = ψ at hfirst
    change f (chart.symm (ψ,0)) = 0 at hsecond
    have hp : chart.symm (ψ,0) = (ψ,(chart.symm (ψ,0)).2) := Prod.ext hfirst rfl
    exact (congrArg f hp).symm.trans hsecond

theorem complex_scalar_root_quotient (c a d : ℂ) (hc : c ≠ 0)
    (hs : a + d*c = 0) : d = -c⁻¹*a := by
  field_simp
  linear_combination hs


theorem complex_root_derivative (f : PotPair × ℂ → ℂ) (φ : PotPair) (z : ℂ)
    (hf : AnalyticAt ℂ f (φ,z)) (hc : fderiv ℂ f (φ,z) (0,1) ≠ 0)
    (κ : PotPair → ℂ) (hκ : AnalyticAt ℂ κ φ) (hκvalue : κ φ = z)
    (hroot : ∀ᶠ ψ in 𝓝 φ, f (ψ,κ ψ) = 0) :
    HasFDerivAt κ (-(fderiv ℂ f (φ,z) (0,1))⁻¹ •
      ((fderiv ℂ f (φ,z)).comp potentialInclusion)) φ := by
  let L := fderiv ℂ f (φ,z)
  have hcurve : HasFDerivAt (fun ψ : PotPair => (ψ,κ ψ))
      ((ContinuousLinearMap.id ℂ PotPair).prod (fderiv ℂ κ φ)) φ :=
    (hasFDerivAt_id φ).prodMk hκ.differentiableAt.hasFDerivAt
  have hf' : HasFDerivAt f L (φ,κ φ) := by
    rw [hκvalue]
    exact hf.differentiableAt.hasFDerivAt
  have hchain := hf'.comp φ hcurve
  have hzero : HasFDerivAt (fun ψ : PotPair => f (ψ,κ ψ)) (0 : PotPair →L[ℂ] ℂ) φ :=
    hasFDerivAt_zero_of_eventually_const (𝕜 := ℂ) 0 hroot
  have he := hchain.unique hzero
  apply hκ.differentiableAt.hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  have hs := congrArg (fun K : PotPair →L[ℂ] ℂ => K h) he
  change L (h, fderiv ℂ κ φ h) = 0 at hs
  rw [complex_linear_split L (h, fderiv ℂ κ φ h)] at hs
  change fderiv ℂ κ φ h = -(L (0,1))⁻¹ * L (h,0)
  exact complex_scalar_root_quotient _ _ _ hc hs

/-- Generic complex local simple-root branch, with its actual derivative. -/
def SimpleRootBranchTarget : Prop :=
  ∀ (f : PotPair × ℂ → ℂ) (φ : PotPair) (z : ℂ),
    AnalyticAt ℂ f (φ,z) → f (φ,z) = 0 →
    (fderiv ℂ f (φ,z)) (0,1) ≠ 0 →
    ∃ (U : Set PotPair) (κ : PotPair → ℂ),
      IsOpen U ∧ φ ∈ U ∧ AnalyticOnNhd ℂ κ U ∧ κ φ = z ∧
      (∀ ψ ∈ U, f (ψ,κ ψ) = 0) ∧
      HasFDerivAt κ
        (-(fderiv ℂ f (φ,z) (0,1))⁻¹ •
          ((fderiv ℂ f (φ,z)).comp potentialInclusion)) φ

theorem simple_root_branch_target : SimpleRootBranchTarget := by
  intro f φ z hf hroot hc
  obtain ⟨κ,hκ,hvalue,hev⟩ := complex_analytic_root f φ z hf hroot hc
  have hder := complex_root_derivative f φ z hf hc κ hκ hvalue hev
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hκ.eventually_analyticAt.and hev)
  exact ⟨Metric.ball φ r, κ, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (fun ψ hψ => (hsub hψ).1), hvalue, (fun ψ hψ => (hsub hψ).2), hder⟩


end
end NlsGge.GK38.GradEigen38
