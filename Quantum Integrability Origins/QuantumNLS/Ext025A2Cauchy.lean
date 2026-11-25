import QuantumNLS.Ext025AAnalysis

/-! Round 2 author constituents for GP-03 and GP-05.
Every analytic conclusion below is derived. Scalar complex domain statements
have arbitrary complete complex Banach targets; the arbitrary Banach-domain
polarization and weak covector Haar averaging clauses remain explicit gaps. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
namespace QuantumNLS.Ext025A2
section Cauchy
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- All fixed orders, in the target Banach norm, with the exact factorial. -/
theorem gp05_cauchy_all_orders {f : ℂ → E} {U : Set ℂ} {z : ℂ} {r M : ℝ}
    (hf : DifferentiableOn ℂ f U) (hr : 0 < r)
    (hball : closedBall z r ⊆ U) (hM : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) (n : ℕ) :
    ‖iteratedDeriv n f z‖ ≤ n.factorial * M / r ^ n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr _ hM
  exact (hf.mono (closure_ball_subset_closedBall.trans hball)).diffContOnCl

/-- A fixed common circle transfers a uniform value bound to every fixed order. -/
theorem gp05_uniform_all_orders {I : Type*} {f : I → ℂ → E}
    {U : Set ℂ} {z : ℂ} {r C : ℝ} (hr : 0 < r) (hball : closedBall z r ⊆ U)
    (weight : I → ℝ) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hM : ∀ i w, w ∈ sphere z r → ‖f i w‖ ≤ C * weight i) (n : ℕ) :
    ∀ i, ‖iteratedDeriv n (f i) z‖ ≤ (n.factorial * C / r ^ n) * weight i := by
  intro i
  convert gp05_cauchy_all_orders (hf i) hr hball (hM i) n using 1
  ring

/-- Normal convergence implies holomorphy, analyticity, and termwise differentiation. -/
theorem gp05_normal_sum {I : Type*} {f : I → ℂ → E} {U : Set ℂ} {b : I → ℝ}
    (hU : IsOpen U) (hb : Summable b) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hbound : ∀ i z, z ∈ U → ‖f i z‖ ≤ b i) :
    AnalyticOnNhd ℂ (fun z => ∑' i, f i z) U ∧
      ∀ z ∈ U, HasSum (fun i => deriv (f i) z) (deriv (fun z => ∑' i, f i z) z) := by
  exact ⟨(Complex.differentiableOn_tsum_of_summable_norm hb hf hU hbound).analyticOnNhd hU,
    fun z hz => Complex.hasSum_deriv_of_summable_norm hb hf hU hbound hz⟩

/-- A locally uniform holomorphic limit has an actual convergent power series. -/
theorem gp05_limit_power_series {I : Type*} {l : Filter I} [l.NeBot]
    {f : I → ℂ → E} {g : ℂ → E} {U : Set ℂ}
    (hU : IsOpen U) (hlim : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (f i) U) : AnalyticOnNhd ℂ g U :=
  (hlim.differentiableOn hf hU).analyticOnNhd hU

omit [CompleteSpace E] in
/-- Bounded integration with explicit measurability in the target norm.
This is not the weak covector Haar average, which requires a separate construction. -/
theorem gp05_bounded_integration {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f df : ℂ → X → E} {b : X → ℝ} {S : Set ℂ} {z : ℂ}
    (hS : S ∈ 𝓝 z) (hm : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (f w) μ)
    (hi : Integrable (f z) μ) (hdm : AEStronglyMeasurable (df z) μ)
    (hb : ∀ᵐ x ∂μ, ∀ w ∈ S, ‖df w x‖ ≤ b x) (hbi : Integrable b μ)
    (hd : ∀ᵐ x ∂μ, ∀ w ∈ S, HasDerivAt (fun w => f w x) (df w x) w) :
    Integrable (df z) μ ∧
      HasDerivAt (fun w => ∫ x, f w x ∂μ) (∫ x, df z x ∂μ) z :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le hS hm hi hdm hb hbi hd
end Cauchy

/-- Holomorphy alone supplies the analytic input to the scalar inverse theorem.
Neither analyticity of the original function nor that of the inverse is assumed. -/
theorem gp03_holomorphic_scalar_inverse {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U)
    (i : ℂ ≃L[ℂ] ℂ) (hd : HasFDerivAt f i.toContinuousLinearMap a) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (f a) ∧ AnalyticAt ℝ g (f a) ∧
      g (f a) = a ∧ (∀ᶠ x in 𝓝 a, g (f x) = x) ∧
      (∀ᶠ y in 𝓝 (f a), f (g y) = y) := by
  obtain ⟨g, hg, hga, hl, hr⟩ :=
    QuantumNLS.Ext025A.gp03_analytic_inverse i (hf.analyticAt (hU.mem_nhds ha)) hd
  exact ⟨g, hg, hg.restrictScalars, hga, hl, hr⟩

/-- Real restriction of a Banach analytic inverse. The power-series input is
explicit; this theorem does not claim the missing multivariate holomorphy bridge. -/
theorem gp03_real_restriction {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] {f : E → F} {a : E} (i : E ≃L[ℂ] F)
    (hf : AnalyticAt ℂ f a) (hd : HasFDerivAt f i.toContinuousLinearMap a) :
    ∃ g : F → E, AnalyticAt ℂ g (f a) ∧ AnalyticAt ℝ g (f a) ∧
      (∀ᶠ x in 𝓝 a, g (f x) = x) ∧ (∀ᶠ y in 𝓝 (f a), f (g y) = y) := by
  obtain ⟨g, hg, _, hl, hr⟩ := QuantumNLS.Ext025A.gp03_analytic_inverse i hf hd
  exact ⟨g, hg, hg.restrictScalars, hl, hr⟩
end QuantumNLS.Ext025A2

#print axioms QuantumNLS.Ext025A2.gp05_cauchy_all_orders
#print axioms QuantumNLS.Ext025A2.gp05_uniform_all_orders
#print axioms QuantumNLS.Ext025A2.gp05_normal_sum
#print axioms QuantumNLS.Ext025A2.gp05_limit_power_series
#print axioms QuantumNLS.Ext025A2.gp05_bounded_integration
#print axioms QuantumNLS.Ext025A2.gp03_holomorphic_scalar_inverse
#print axioms QuantumNLS.Ext025A2.gp03_real_restriction
