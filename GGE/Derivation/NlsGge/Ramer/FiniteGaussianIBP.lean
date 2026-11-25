import NlsGge.Ramer.FiniteGaussian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite-dimensional Gaussian integration by parts

This identifies `finiteGaussianDivergence` as the Gaussian divergence: the
adjoint of the gradient in `L²(γ)`, with the convention of the E05 contract,

  `∫ φ · δF dγ = ∫ Dφ(x)(F x) dγ`,

where `δF(x) = ⟪x, F x⟫ - tr DF(x)`. The hypotheses: `φ` is real-valued, `C¹`
and compactly supported; `F` is a `C¹` vector field. This is the
finite-dimensional step of proof obligation 3. The closure to a Gaussian
Sobolev space and the `L²` estimate are NOT proved here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Gaussian density has derivative `-ρ(x) ⟪x, ·⟫`. -/
theorem hasFDerivAt_finiteGaussianDensity (x : V) :
    HasFDerivAt (finiteGaussianDensity V)
      ((-finiteGaussianDensity V x) • innerSL ℝ x) x := by
  set c : ℝ := (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2)
  have hfun : finiteGaussianDensity V = fun y => c * Real.exp ((-1 / 2 : ℝ) * ‖y‖ ^ 2) := by
    funext y; unfold finiteGaussianDensity; congr 2; ring
  have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := ((h1.const_mul (-1 / 2 : ℝ)).exp).const_mul c
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  ring

/-- Gaussian integration by parts in finite dimensions:
`∫ φ δF dγ = ∫ Dφ(F) dγ` for compactly supported `C¹` `φ` and `C¹` `F`. -/
theorem integral_mul_finiteGaussianDivergence (φ : V → ℝ) (F : V → V)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hF : ContDiff ℝ 1 F) :
    ∫ x, φ x * finiteGaussianDivergence F x ∂(finiteStdGaussian V) =
      ∫ x, fderiv ℝ φ x (F x) ∂(finiteStdGaussian V) := by
  set ρ := finiteGaussianDensity V with hρ
  -- reduce both integrals to Lebesgue measure
  have hconv : ∀ g : V → ℝ, ∫ x, g x ∂(finiteStdGaussian V) = ∫ x, ρ x * g x := by
    intro g
    rw [finiteStdGaussian, integral_withDensity_eq_integral_toReal_smul
      (continuous_finiteGaussianDensity.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    congr 1; funext x
    rw [ENNReal.toReal_ofReal (finiteGaussianDensity_pos x).le, smul_eq_mul]
  rw [hconv, hconv]
  -- notation and regularity
  have hφd : ∀ x, HasFDerivAt φ (fderiv ℝ φ x) x :=
    fun x => (hφ.differentiable (by norm_num) x).hasFDerivAt
  have hFd : ∀ x, HasFDerivAt F (fderiv ℝ F x) x :=
    fun x => (hF.differentiable (by norm_num) x).hasFDerivAt
  have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hF'c : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hFc : Continuous F := hF.continuous
  have hρc : Continuous ρ := continuous_finiteGaussianDensity
  let ψ : V → ℝ := fun x => φ x * ρ x
  let ψ' : V → (V →L[ℝ] ℝ) := fun x =>
    φ x • ((-ρ x) • innerSL ℝ x) + ρ x • fderiv ℝ φ x
  have hψd : ∀ x, HasFDerivAt ψ (ψ' x) x :=
    fun x => (hφd x).mul (hasFDerivAt_finiteGaussianDensity x)
  -- vanishing outside the compact support of φ
  have hvan : ∀ x, x ∉ tsupport φ → φ x = 0 ∧ fderiv ℝ φ x = 0 := by
    intro x hx
    exact ⟨image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))⟩
  have hint : ∀ h : V → ℝ, Continuous h → (∀ x, x ∉ tsupport φ → h x = 0) → Integrable h :=
    fun h hc hv => hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hφc hv)
  have hψ'c : Continuous ψ' := by
    have hin : Continuous (fun x : V => innerSL ℝ x) := (innerSL ℝ).continuous
    exact ((hφ.continuous.smul ((hρc.neg).smul hin))).add (hρc.smul hφ'c)
  -- orthonormal basis and one integration by parts per basis vector
  let b := stdOrthonormalBasis ℝ V
  have hibp : ∀ i, ∫ x, ψ x * ⟪b i, fderiv ℝ F x (b i)⟫ =
      -∫ x, ψ' x (b i) * ⟪b i, F x⟫ := by
    intro i
    have hg : ∀ x, HasFDerivAt (fun y => ⟪b i, F y⟫)
        ((innerSL ℝ (b i)).comp (fderiv ℝ F x)) x :=
      fun x => (innerSL ℝ (b i)).hasFDerivAt.comp x (hFd x)
    have key := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
      (μ := (volume : Measure V)) (f := ψ) (f' := ψ') (g := fun y => ⟪b i, F y⟫)
      (g' := fun x => (innerSL ℝ (b i)).comp (fderiv ℝ F x)) (v := b i)
      (B := ContinuousLinearMap.mul ℝ ℝ) ?_ ?_ ?_ (fun x _ => hψd x) (fun x _ => hg x)
    · simpa [ContinuousLinearMap.mul_apply', innerSL_apply_apply] using key
    · apply hint
      · exact ((hψ'c.clm_apply continuous_const)).mul (continuous_const.inner hFc)
      · intro x hx; simp [ψ', (hvan x hx).1, (hvan x hx).2]
    · apply hint
      · exact (hφ.continuous.mul hρc).mul (continuous_const.inner (hF'c.clm_apply continuous_const))
      · intro x hx; simp [ψ, (hvan x hx).1]
    · apply hint
      · exact (hφ.continuous.mul hρc).mul (continuous_const.inner hFc)
      · intro x hx; simp [ψ, (hvan x hx).1]
  -- sum over the basis
  have htrace : ∀ x, LinearMap.trace ℝ V ((fderiv ℝ F x : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      ∑ i, ⟪b i, fderiv ℝ F x (b i)⟫ := fun x => LinearMap.trace_eq_sum_inner _ b
  have hexpand : ∀ x, ψ' x (F x) = ∑ i, ψ' x (b i) * ⟪b i, F x⟫ := by
    intro x
    conv_lhs => rw [← b.sum_repr' (F x)]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul, mul_comm])
  have hA : ∫ x, ψ x * LinearMap.trace ℝ V ((fderiv ℝ F x : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      -∫ x, ψ' x (F x) := by
    have hi1 : ∀ i ∈ Finset.univ, Integrable (fun x => ψ x * ⟪b i, fderiv ℝ F x (b i)⟫) := by
      intro i _
      apply hint
      · exact (hφ.continuous.mul hρc).mul (continuous_const.inner (hF'c.clm_apply continuous_const))
      · intro x hx; simp [ψ, (hvan x hx).1]
    have hi2 : ∀ i ∈ Finset.univ, Integrable (fun x => ψ' x (b i) * ⟪b i, F x⟫) := by
      intro i _
      apply hint
      · exact ((hψ'c.clm_apply continuous_const)).mul (continuous_const.inner hFc)
      · intro x hx; simp [ψ', (hvan x hx).1, (hvan x hx).2]
    simp_rw [htrace, Finset.mul_sum, hexpand]
    rw [integral_finsetSum _ hi1, integral_finsetSum _ hi2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => hibp i)
  -- assemble
  have hpt : ∀ x, ρ x * (φ x * finiteGaussianDivergence F x) =
      ρ x * fderiv ℝ φ x (F x) -
        (ψ' x (F x) + ψ x * LinearMap.trace ℝ V ((fderiv ℝ F x : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
    intro x
    simp only [ψ', ψ, finiteGaussianDivergence, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  have hI1 : Integrable (fun x => ρ x * fderiv ℝ φ x (F x)) := by
    apply hint
    · exact hρc.mul (hφ'c.clm_apply hFc)
    · intro x hx; simp [(hvan x hx).2]
  have hI2 : Integrable (fun x => ψ' x (F x)) := by
    apply hint
    · exact hψ'c.clm_apply hFc
    · intro x hx; simp [ψ', (hvan x hx).1, (hvan x hx).2]
  have hI3 : Integrable (fun x => ψ x *
      LinearMap.trace ℝ V ((fderiv ℝ F x : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
    apply hint
    · have htc : Continuous (fun x => LinearMap.trace ℝ V
          ((fderiv ℝ F x : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
        simp_rw [htrace]
        exact continuous_finsetSum _ (fun i _ =>
          continuous_const.inner (hF'c.clm_apply continuous_const))
      exact (hφ.continuous.mul hρc).mul htc
    · intro x hx; simp [ψ, (hvan x hx).1]
  simp_rw [hpt]
  have hsub := integral_sub hI1 (hI2.add hI3)
  simp only [Pi.add_apply] at hsub
  rw [hsub, integral_add hI2 hI3, hA]
  ring

end NlsGge.Ramer
