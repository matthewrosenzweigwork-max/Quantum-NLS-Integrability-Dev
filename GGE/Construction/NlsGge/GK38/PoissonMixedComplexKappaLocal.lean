import NlsGge.GK38.PoissonMixedKappaDerivativeData

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem complexKappaLocalDerivativeTarget : ComplexKappaLocalDerivativeTarget := by
  intro φ z hr hs
  have hU := normingFactor_ne_zero_at_dirichlet_root38 φ z hr
  obtain ⟨hQ,hgrad,V,ρ,hV,hφ,hρ,hvalue,hroot,hder⟩ :=
    complex_dirichlet_simple_target φ z hr hs
  rw [← hgrad] at hder
  let a : PotPair → ℂ := fun ψ => normingFactor ψ (ρ ψ)
  let r : PotPair → ℂ := fun ψ => a ψ / normingFactor φ z
  have ha : AnalyticOnNhd ℂ a V := by
    intro ψ hψ
    exact (analyticOnNhd_normingFactor38 (ψ,ρ ψ) (mem_univ _)).comp
      (f := fun x : PotPair => (x,ρ x)) (x := ψ)
      (analyticAt_id.prod (hρ ψ hψ))
  have hratio : AnalyticOnNhd ℂ r V := by
    convert! ha.div_const (c := normingFactor φ z) using 1
  have hbase : r φ = 1 := by
    dsimp [r,a]
    rw [hvalue,div_self hU]
  let U : Set PotPair := V ∩ r ⁻¹' Complex.slitPlane
  have hopen : IsOpen U :=
    hratio.continuousOn.isOpen_inter_preimage hV Complex.isOpen_slitPlane
  have hmem : φ ∈ U := ⟨hφ,by change r φ ∈ Complex.slitPlane; rw [hbase]; exact Complex.one_mem_slitPlane⟩
  have hκ : AnalyticOnNhd ℂ (relativeKappa38 φ z ρ) U := by
    have hlog : AnalyticOnNhd ℂ (fun ψ => Complex.log (r ψ)) U :=
      (hratio.mono inter_subset_left).clog (fun ψ hψ => hψ.2)
    intro ψ hψ
    exact analyticAt_const.mul (hlog ψ hψ)
  have hκvalue : relativeKappa38 φ z ρ φ = 0 := by
    change 2*Complex.log (r φ) = 0
    rw [hbase,Complex.log_one,mul_zero]
  have hgraph := hasFDerivAt_norming_graph38 φ z ρ (dirImplicitGradient φ z) hvalue hder
  have hratioDer : HasFDerivAt r
      ((normingFactor φ z)⁻¹ •
        (normingSpectral38 φ z • dirImplicitGradient φ z + normingCLM38 φ z)) φ := by
    convert! hgraph.const_mul (normingFactor φ z)⁻¹ using 1
    ext ψ
    exact div_eq_inv_mul _ _
  have hlogDer := (hratioDer.clog (by rw [hbase]; exact Complex.one_mem_slitPlane)).const_mul (2 : ℂ)
  have hκDer : HasFDerivAt (relativeKappa38 φ z ρ) (kappaCLM38 φ z) φ := by
    rw [kappaCLM_at_dirichlet_root38 φ z hr hs]
    convert! hlogDer using 1
    rw [hbase,inv_one,one_smul,smul_smul]
    rw [div_eq_mul_inv]
  refine ⟨hU,U,ρ,hopen,hmem,hρ.mono inter_subset_left,hvalue,?_,hder,hκ,hκvalue,?_,hκDer⟩
  · intro ψ hψ
    have hne : normingFactor ψ (ρ ψ) ≠ 0 := by
      intro hz
      have hn := Complex.slitPlane_ne_zero hψ.2
      apply hn
      change normingFactor ψ (ρ ψ) / normingFactor φ z = 0
      rw [hz,zero_div]
    exact ⟨hroot ψ hψ.1,hne,hψ.2⟩
  · intro ψ hψ
    have hn := Complex.slitPlane_ne_zero hψ.2
    change Complex.exp ((2*Complex.log (r ψ))/2) = r ψ
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0),Complex.exp_log hn]

end
end NlsGge.GK38.PoissonMixed38
