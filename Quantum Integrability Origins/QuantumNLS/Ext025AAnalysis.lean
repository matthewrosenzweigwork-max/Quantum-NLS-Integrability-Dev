import Mathlib

/-!+# EXT-025 A: inverse functions, ODEs, and Cauchy estimates

These are named, proved parts of GP-03, GP-04, GP-05. The final receipt
keeps the whole records OPEN wherever a conclusion or a mathematical
application wrapper is not supplied here. In particular no Banach-domain
holomorphic-to-power-series implication or analytic ODE dependence is assumed.
The source's consumer descriptions identify intended uses; they are prose,
not extra hypotheses granting a consumer's conclusion.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open scoped NNReal

namespace QuantumNLS.Ext025A

section Inverse
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- GP-03 differentiable inverse, with an actual local inverse, its
regularity, and both identities on neighborhoods. A C1 germ is precisely
what an open-domain C1 hypothesis supplies at an interior point. -/
theorem «FIN-EXT025-GP-03» {f : E → F} {a : E} (i : E ≃L[𝕜] F)
    (hf : ContDiffAt 𝕜 1 f a) (hd : HasFDerivAt f i.toContinuousLinearMap a) :
    ∃ g : F → E, ContDiffAt 𝕜 1 g (f a) ∧ g (f a) = a ∧
      (∀ᶠ x in 𝓝 a, g (f x) = x) ∧
      (∀ᶠ y in 𝓝 (f a), f (g y) = y) := by
  let hs := hf.hasStrictFDerivAt' hd (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  exact ⟨hf.localInverse hd (by norm_num), hf.to_localInverse hd (by norm_num),
    hf.localInverse_apply_image hd (by norm_num), hs.eventually_left_inverse,
    hs.eventually_right_inverse⟩

/-- GP-03 analytic inverse, when analytic is expressed by a convergent
Banach-valued power series. This theorem proves the inverse analyticity;
it does not assume it. The holomorphic-complexification bridge in the
record remains separately listed in the gaps. -/
theorem gp03_analytic_inverse {f : E → F} {a : E} (i : E ≃L[𝕜] F)
    (hf : AnalyticAt 𝕜 f a) (hd : HasFDerivAt f i.toContinuousLinearMap a) :
    ∃ g : F → E, AnalyticAt 𝕜 g (f a) ∧ g (f a) = a ∧
      (∀ᶠ x in 𝓝 a, g (f x) = x) ∧
      (∀ᶠ y in 𝓝 (f a), f (g y) = y) := by
  obtain ⟨p, hp⟩ := hf
  have hs : HasStrictFDerivAt f i.toContinuousLinearMap a := by
    have he : continuousMultilinearCurryFin1 𝕜 E F (p 1) = i.toContinuousLinearMap :=
      hp.hasFDerivAt.unique hd
    exact he ▸ hp.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  have hp1 : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i := by
    apply (continuousMultilinearCurryFin1 𝕜 E F).injective
    simpa using hp.hasFDerivAt.unique hd
  have ha : a ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have han : AnalyticAt 𝕜 e.symm (f a) :=
    (e.hasFPowerSeriesAt_symm ha hp hp1).analyticAt
  exact ⟨e.symm, han, e.left_inv ha, hs.eventually_left_inverse,
    hs.eventually_right_inverse⟩
end Inverse

section Implicit
variable {𝕜 E P F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- GP-03 implicit wrapper: invert the unknown partial derivative.
The equivalence in a neighborhood states local uniqueness as well as existence. -/
theorem gp03_implicit {f : P × E → F} {u : P × E} {d : P × E →L[𝕜] F}
    (hf : HasStrictFDerivAt f d u)
    (hi : (d ∘L ContinuousLinearMap.inr 𝕜 P E).IsInvertible) :
    ∃ ψ : P → E,
      HasStrictFDerivAt ψ
        (-(d ∘L ContinuousLinearMap.inr 𝕜 P E).inverse ∘L
          (d ∘L ContinuousLinearMap.inl 𝕜 P E)) u.1 ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2) ∧
      (∀ᶠ p in 𝓝 u.1, f (p, ψ p) = f u) := by
  exact ⟨hf.implicitFunctionOfProdDomain hi,
    hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hi,
    hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi,
    hf.eventually_apply_implicitFunctionOfProdDomain hi⟩
end Implicit

/-- GP-04 integral-equation existence under explicit common local
Picard bounds. Variational equations and analytic initial dependence
are not consequences asserted by this partial theorem. -/
theorem «FIN-EXT025-GP-04» {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E}
    {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, α t = ODE.picard f t₀ x α t :=
  hf.exists_eq_forall_mem_Icc_eq_picard hx

section Cauchy
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- GP-05 first Cauchy derivative bound in the actual Banach norm,
with a fixed enclosing circle strictly inside a common open neighborhood. -/
theorem «FIN-EXT025-GP-05» {f : ℂ → E} {U : Set ℂ} {z : ℂ} {r M : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hr : 0 < r)
    (hball : closedBall z r ⊆ U) (hM : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) :
    ‖deriv f z‖ ≤ M / r := by
  rw [← Complex.cderiv_eq_deriv hU hf hr hball]
  exact Complex.norm_cderiv_le hr hM

/-- GP-05 uniform `C r^-1 eta^-m` derivative transfer. The hypotheses
are uniform complex-neighborhood value bounds, not real pointwise asymptotics. -/
theorem gp05_uniform_parameter_bound {I : Type*} {f : I → ℂ → E}
    {U : Set ℂ} {z : ℂ} {r C : ℝ} (hU : IsOpen U) (hr : 0 < r)
    (hball : closedBall z r ⊆ U) (weight : I → ℝ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hM : ∀ i w, w ∈ sphere z r → ‖f i w‖ ≤ C * weight i) :
    ∀ i, ‖deriv (f i) z‖ ≤ (C / r) * weight i := by
  intro i
  simpa only [mul_div_right_comm] using
    «FIN-EXT025-GP-05» hU (hf i) hr hball (hM i)

/-- GP-05 Banach-valued holomorphy is preserved by locally uniform
limits on a common open scalar domain. -/
theorem gp05_locally_uniform_limit {I : Type*} {l : Filter I} [l.NeBot]
    {F : I → ℂ → E} {f : ℂ → E} {U : Set ℂ}
    (hU : IsOpen U) (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) :
    DifferentiableOn ℂ f U :=
  hlim.differentiableOn hF hU
end Cauchy
end QuantumNLS.Ext025A

#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-03»
#print axioms QuantumNLS.Ext025A.gp03_analytic_inverse
#print axioms QuantumNLS.Ext025A.gp03_implicit
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-04»
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-05»
#print axioms QuantumNLS.Ext025A.gp05_uniform_parameter_bound
#print axioms QuantumNLS.Ext025A.gp05_locally_uniform_limit
