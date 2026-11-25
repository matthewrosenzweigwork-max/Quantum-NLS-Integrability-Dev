import NlsGge.GK38.GradEigenPeriodicGradient
set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem periodic_characteristic_potential_derivative (φ : PotPair) (z : ℂ) :
    HasFDerivAt (fun ψ : PotPair => perChar ψ z)
      ((2*discrim φ z) • gradDiscrimCLM φ z) φ := by
  have hp := ((hasFDerivAt_discrim z φ).pow 2).sub_const 4
  simpa only [perChar,perCharOf,Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat] using hp

theorem periodic_joint_potential_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (φ,z)).comp potentialInclusion =
      (2*discrim φ z) • gradDiscrimCLM φ z := by
  let f : PotPair × ℂ → ℂ := fun p => perChar p.1 p.2
  have hA : AnalyticAt ℂ f (φ,z) :=
    ((analyticOnNhd_discrim.pow 2).sub analyticOnNhd_const) (φ,z) (mem_univ _)
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) := hA.differentiableAt.hasFDerivAt
  have hcurve : HasFDerivAt (fun ψ : PotPair => (ψ,z)) potentialInclusion φ := by
    change HasFDerivAt (fun ψ : PotPair => (ψ,z)) (ContinuousLinearMap.inl ℂ PotPair ℂ) φ
    exact hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z
  have hp := hf.comp φ hcurve
  change HasFDerivAt (fun ψ : PotPair => perChar ψ z)
    ((fderiv ℂ f (φ,z)).comp potentialInclusion) φ at hp
  exact hp.unique (periodic_characteristic_potential_derivative φ z)

theorem periodic_joint_spectral_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (φ,z)) (0,1) =
      deriv (perChar φ) z := by
  let f : PotPair × ℂ → ℂ := fun p => perChar p.1 p.2
  have hA : AnalyticAt ℂ f (φ,z) :=
    ((analyticOnNhd_discrim.pow 2).sub analyticOnNhd_const) (φ,z) (mem_univ _)
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) := hA.differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun w : ℂ => (φ,w)) ((0 : PotPair),(1 : ℂ)) z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  have hs : HasDerivAt (perChar φ)
      ((fderiv ℂ f (φ,z)) (0,1)) z := hf.comp_hasDerivAt z hcurve
  exact hs.deriv.symm

/-- Both periodic signs and arbitrary nonzero complex eigenvector phase. -/

def ComplexPeriodicSimpleTarget : Prop :=
  ∀ (φ : PotPair) (z c : ℂ) (a : PairVec38),
    c ^ 2 = 1 → perChar φ z = 0 → deriv (perChar φ) z ≠ 0 →
    a ≠ 0 → Matrix.mulVec (monodromyPair φ z) a = c • a →
    Q (state φ z a) ≠ 0 ∧ deriv (discrim φ) z ≠ 0 ∧
    perImplicitGradient φ z = bilinearGradient (state φ z a) ∧
    ∃ (U : Set PotPair) (κ : PotPair → ℂ),
      IsOpen U ∧ φ ∈ U ∧ AnalyticOnNhd ℂ κ U ∧ κ φ = z ∧
      (∀ ψ ∈ U, perChar ψ (κ ψ) = 0) ∧
      HasFDerivAt κ (bilinearGradient (state φ z a)) φ

theorem complex_periodic_simple_target : ComplexPeriodicSimpleTarget := by
  intro φ z c a hc hroot hsimple ha he
  obtain ⟨hQ,hd,hgrad⟩ := periodic_arbitrary_eigenvector_gradient φ z c a hc hsimple ha he
  have hpartial : (fderiv ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (φ,z)) (0,1) ≠ 0 := by
    rw [periodic_joint_spectral_partial]
    exact hsimple
  have hA : AnalyticAt ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (φ,z) :=
    ((analyticOnNhd_discrim.pow 2).sub analyticOnNhd_const) (φ,z) (mem_univ _)
  obtain ⟨U,κ,hU,hbase,hκ,hvalue,heq,hder⟩ := simple_root_branch_target
    (fun p : PotPair × ℂ => perChar p.1 p.2) φ z hA hroot hpartial
  have hk : 2*discrim φ z ≠ 0 := by
    intro hz
    apply hsimple
    rw [periodic_perChar_deriv,hz,zero_mul]
  have hΔ : discrim φ z ≠ 0 := (mul_ne_zero_iff.mp hk).2
  have hinv : -((2*discrim φ z)*deriv (discrim φ) z)⁻¹*(2*discrim φ z) =
      -(deriv (discrim φ) z)⁻¹ := by field_simp [hΔ,hd]
  rw [periodic_joint_potential_partial,periodic_joint_spectral_partial,
    periodic_perChar_deriv,smul_smul,hinv] at hder
  change HasFDerivAt κ (perImplicitGradient φ z) φ at hder
  rw [hgrad] at hder
  exact ⟨hQ,hd,hgrad,U,κ,hU,hbase,hκ,hvalue,heq,hder⟩

end
end NlsGge.GK38.GradEigen38
