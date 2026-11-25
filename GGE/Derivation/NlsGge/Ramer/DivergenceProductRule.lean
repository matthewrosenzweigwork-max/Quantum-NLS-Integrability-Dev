import NlsGge.Ramer.FiniteDivergenceL2

/-!
# Product rule and locality of the finite Gaussian divergence (obligation R2, finite part)

On a finite-dimensional real inner product space `V`, for a scalar function `f` and a
vector field `h`, both differentiable at `x`,

  `δ(f h)(x) = f(x) δh(x) - Df(x)(h x)`,

which is v2's `δ(ηF) = η δF - ⟨D_H η, F⟩_H` (proof of `prop:gaussiancommon`) with
`⟨∇f, h⟩ = Df(h)`. Locality: `δF(x)` depends only on the germ of `F` at `x`, so fields that
agree on an open set have the same divergence there. In particular `δ(ηF) = δF` wherever
`η = 1` on a neighbourhood.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Product rule.** `δ(f h)(x) = f(x) δh(x) - Df(x)(h x)`. -/
theorem finiteGaussianDivergence_smul (f : V → ℝ) (h : V → V) (x : V)
    (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x) :
    finiteGaussianDivergence (fun y => f y • h y) x =
      f x * finiteGaussianDivergence h x - fderiv ℝ f x (h x) := by
  have hd : fderiv ℝ (fun y => f y • h y) x =
      f x • fderiv ℝ h x + (fderiv ℝ f x).smulRight (h x) :=
    (hf.hasFDerivAt.smul hh.hasFDerivAt).fderiv
  unfold finiteGaussianDivergence
  rw [hd, inner_smul_right]
  have htr : LinearMap.trace ℝ V
      (((f x • fderiv ℝ h x + (fderiv ℝ f x).smulRight (h x) : V →L[ℝ] V)) : V →ₗ[ℝ] V) =
      f x * LinearMap.trace ℝ V ((fderiv ℝ h x : V →L[ℝ] V) : V →ₗ[ℝ] V) +
        fderiv ℝ f x (h x) := by
    rw [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul, map_add, map_smul,
      smul_eq_mul]
    congr 1
    exact LinearMap.trace_smulRight _ _
  rw [htr]
  ring

/-- **Locality.** The divergence at `x` depends only on the germ of the field at `x`. -/
theorem finiteGaussianDivergence_congr_of_eventuallyEq {F G : V → V} {x : V}
    (h : F =ᶠ[𝓝 x] G) : finiteGaussianDivergence F x = finiteGaussianDivergence G x := by
  unfold finiteGaussianDivergence
  rw [h.fderiv_eq, h.eq_of_nhds]

/-- Fields that agree on an open set have the same divergence on it. -/
theorem finiteGaussianDivergence_eqOn_of_eqOn {F G : V → V} {U : Set V} (hU : IsOpen U)
    (h : Set.EqOn F G U) : Set.EqOn (finiteGaussianDivergence F) (finiteGaussianDivergence G) U :=
  fun x hx => finiteGaussianDivergence_congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)

/-- **Cutoff invariance.** If `η = 1` on an open set `U`, then `δ(η F) = δF` on `U`. This is
v2's independence of the chosen bump, in finite dimensions. -/
theorem finiteGaussianDivergence_smul_eqOn_of_eqOn_one (η : V → ℝ) (F : V → V) {U : Set V}
    (hU : IsOpen U) (hη : Set.EqOn η 1 U) :
    Set.EqOn (finiteGaussianDivergence (fun y => η y • F y)) (finiteGaussianDivergence F) U :=
  finiteGaussianDivergence_eqOn_of_eqOn hU (fun y hy => by simp [hη hy])

/-- The product rule integrated: for compactly supported `C¹` `f` and `C¹` field `h`,
`∫ δ(f h) dγ = 0`, i.e. `∫ f δh dγ = ∫ Df(h) dγ` (consistency with the IBP duality). -/
theorem integral_finiteGaussianDivergence_smul_eq_zero (f : V → ℝ) (h : V → V)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hh : ContDiff ℝ 1 h) :
    ∫ x, finiteGaussianDivergence (fun y => f y • h y) x ∂(finiteStdGaussian V) = 0 := by
  have hc : HasCompactSupport (fun y => f y • h y) := hfc.smul_right
  exact integral_finiteGaussianDivergence_eq_zero (hf.smul hh) hc

end NlsGge.Ramer
