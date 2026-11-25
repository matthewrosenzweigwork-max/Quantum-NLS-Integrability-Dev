import NlsGge.GK38.GradEigenRealPeriodicLabels
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem discrim_joint_potential_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ,z)).comp potentialInclusion =
      gradDiscrimCLM φ z := by
  let f : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) :=
    (analyticOnNhd_discrim (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasFDerivAt (fun ψ : PotPair => (ψ,z)) potentialInclusion φ := by
    change HasFDerivAt (fun ψ : PotPair => (ψ,z)) (ContinuousLinearMap.inl ℂ PotPair ℂ) φ
    exact hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z
  have hp := hf.comp φ hcurve
  change HasFDerivAt (fun ψ : PotPair => discrim ψ z)
    ((fderiv ℂ f (φ,z)).comp potentialInclusion) φ at hp
  exact hp.unique (hasFDerivAt_discrim z φ)

theorem discrim_joint_spectral_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => discrim p.1 p.2) (φ,z)) (0,1) =
      deriv (discrim φ) z := by
  let f : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) :=
    (analyticOnNhd_discrim (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun w : ℂ => (φ,w)) ((0 : PotPair),(1 : ℂ)) z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  have hs : HasDerivAt (discrim φ) ((fderiv ℂ f (φ,z)) (0,1)) z :=
    hf.comp_hasDerivAt z hcurve
  exact hs.deriv.symm

theorem actual_endpoint_complex_gradient (u : PhysicalL2) (n : ℤ) (upper : Bool)
    (hgap : actualGapLowerAllE02_38 u n<actualGapUpperAllE02_38 u n) (h : PhysicalL2) :
    ((fderiv ℝ (fun v : PhysicalL2 => endpoint v n upper) u) h : ℂ) =
      perImplicitGradient (realSlice u) (endpoint u n upper : ℂ) (realSlice h) := by
  let r : PhysicalL2 → ℝ := fun v => endpoint v n upper
  let dr := fderiv ℝ r u
  let f : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  let D := fderiv ℂ f (realSlice u,(r u : ℂ))
  let d := deriv (discrim (realSlice u)) (r u : ℂ)
  have hr : HasFDerivAt r dr u := (analyticAt_endpoint u n upper hgap).differentiableAt.hasFDerivAt
  have hf : HasFDerivAt f D (realSlice u,(r u : ℂ)) :=
    (analyticOnNhd_discrim (realSlice u,(r u : ℂ)) (mem_univ _)).differentiableAt.hasFDerivAt
  have hgraph : HasFDerivAt (fun v : PhysicalL2 => (realSlice v,(r v : ℂ)))
      (realSlice.prod (Complex.ofRealCLM.comp dr)) u :=
    realSlice.hasFDerivAt.prodMk (Complex.ofRealCLM.hasFDerivAt.comp u hr)
  have hz := (hf.restrictScalars ℝ).comp u hgraph
  have heq : (fun v : PhysicalL2 => f (realSlice v,(r v : ℂ))) =
      fun _ => (2*parity n : ℂ) := by
    funext v
    exact endpoint_discrim_value v n upper
  simp only [Function.comp_def] at hz
  rw [heq] at hz
  have hz' := congrArg (fun L : PhysicalL2 →L[ℝ] ℂ => L h)
    (hz.unique (hasFDerivAt_const (2*parity n : ℂ) u))
  change D (realSlice h,(dr h : ℂ))=0 at hz'
  have hp : D (realSlice h,0)=gradDiscrimCLM (realSlice u) (r u : ℂ) (realSlice h) := by
    exact congrArg (fun L : PotPair →L[ℂ] ℂ => L (realSlice h))
      (discrim_joint_potential_partial (realSlice u) (r u : ℂ))
  have hs : D (0,1)=d := discrim_joint_spectral_partial (realSlice u) (r u : ℂ)
  have hdecomp : D (realSlice h,(dr h : ℂ)) =
      gradDiscrimCLM (realSlice u) (r u : ℂ) (realSlice h)+(dr h : ℂ)*d := by
    calc
      D (realSlice h,(dr h : ℂ))=D ((realSlice h,0)+(dr h : ℂ) • (0,1)) := by
        congr 1
        simp
      _ = D (realSlice h,0)+(dr h : ℂ)*D (0,1) := by rw [map_add,map_smul]; rfl
      _ = _ := by rw [hp,hs]
  have hd : d ≠ 0 := endpoint_discrim_deriv_ne_zero u n upper hgap
  rw [hdecomp] at hz'
  change (dr h : ℂ)= -d⁻¹*gradDiscrimCLM (realSlice u) (r u : ℂ) (realSlice h)
  field_simp
  linear_combination hz'

theorem actual_endpoint_hasFDerivAt (u : PhysicalL2) (n : ℤ) (upper : Bool)
    (hgap : actualGapLowerAllE02_38 u n<actualGapUpperAllE02_38 u n) (a : PairVec38)
    (ha : a ≠ 0) (hasym : a 1=star (a 0))
    (he : Matrix.mulVec (monodromyPair (realSlice u) (endpoint u n upper : ℂ)) a=parity n • a) :
    HasFDerivAt (fun v : PhysicalL2 => endpoint v n upper)
      (realEnergyGradient (state (realSlice u) (endpoint u n upper : ℂ) a)) u := by
  have hr := (analyticAt_endpoint u n upper hgap).differentiableAt.hasFDerivAt
  have hsym := real_state_symmetry u (endpoint u n upper) a hasym
  have hgrad := (periodic_arbitrary_eigenvector_gradient (realSlice u)
    (endpoint u n upper : ℂ) (parity n) a (parity_square n)
    (endpoint_perChar_deriv_ne_zero u n upper hgap) ha he).2.2
  have hd : fderiv ℝ (fun v : PhysicalL2 => endpoint v n upper) u =
      realEnergyGradient (state (realSlice u) (endpoint u n upper : ℂ) a) := by
    apply ContinuousLinearMap.ext
    intro h
    have hc := actual_endpoint_complex_gradient u n upper hgap h
    rw [hgrad] at hc
    have hre := congrArg Complex.re hc
    rw [bilinear_real_energy _ hsym] at hre
    exact hre
  rw [hd] at hr
  exact hr

end
end NlsGge.GK38.GradEigen38
