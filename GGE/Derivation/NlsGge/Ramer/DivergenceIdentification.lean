import NlsGge.Ramer.FiniteGaussianIBP
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Ramer's and v2's divergence approximants in finite dimensions

Ramer (1974, Section 4) approximates the Gaussian divergence of `K` by
`a_n(x) = ⟨P_n K x, x⟩ - tr(P_n D K(x))` (range projected, argument not), while v2
(`prop:gaussiancommon`) uses the divergence of the cylindrical field
`G_N(x) = P_N G(P_N x)` (range and argument projected). See
`NlsGge/Ramer/DIVERGENCE_IDENTIFICATION.md` for the infinite-dimensional obligation.

This file proves the finite-dimensional identities underlying the identification, on a
finite-dimensional real inner product space `V` carrying its standard Gaussian:

* `finiteGaussianDivergence_eq_sum_orthonormalBasis`: the coordinate formula
  `δF(x) = Σ_i (ξ_i(x) ⟨e_i, F x⟩ - ⟨e_i, DF(x) e_i⟩)`;
* `finiteGaussianDivergence_comp_clm`: Ramer's `a_n` is the divergence of the
  range-projected field `P ∘ K`;
* `finiteGaussianDivergence_starProjection_comp`: v2's `δ(P G(P ·))(x)` is the divergence,
  on the subspace `U = range P`, of the head field `u ↦ P G(u)`, evaluated at `P x`;
* `finiteGaussianDivergence_sub`: linearity, so the difference of the two approximants is
  the divergence of the difference field;
* `eq_of_gaussian_duality`, `eq_finiteGaussianDivergence_of_duality`: a continuous function
  satisfying the Gaussian integration-by-parts duality for `F` against all smooth compactly
  supported test functions is `δF`. Hence any two constructions of the divergence that
  satisfy the duality coincide.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace ContDiff

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Ramer's approximant `a(x) = ⟨P K x, x⟩ - tr(P ∘ D K(x))` (range projected only). -/
def ramerApproximant (P : V →L[ℝ] V) (K : V → V) (x : V) : ℝ :=
  ⟪P (K x), x⟫ - LinearMap.trace ℝ V ((P.comp (fderiv ℝ K x) : V →L[ℝ] V) : V →ₗ[ℝ] V)

/-- Coordinate form of the finite Gaussian divergence in an orthonormal basis. -/
theorem finiteGaussianDivergence_eq_sum_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (F : V → V) (x : V) :
    finiteGaussianDivergence F x =
      ∑ i, (⟪x, b i⟫ * ⟪b i, F x⟫ - ⟪b i, fderiv ℝ F x (b i)⟫) := by
  unfold finiteGaussianDivergence
  rw [Finset.sum_sub_distrib, LinearMap.trace_eq_sum_inner _ b, b.sum_inner_mul_inner]
  rfl

/-- **Ramer's approximant is the divergence of the range-projected field.** -/
theorem finiteGaussianDivergence_comp_clm (P : V →L[ℝ] V) (K : V → V) (x : V)
    (hK : DifferentiableAt ℝ K x) :
    finiteGaussianDivergence (fun y => P (K y)) x = ramerApproximant P K x := by
  unfold finiteGaussianDivergence ramerApproximant
  have hd : fderiv ℝ (fun y => P (K y)) x = P.comp (fderiv ℝ K x) :=
    (P.hasFDerivAt.comp x hK.hasFDerivAt).fderiv
  rw [hd, real_inner_comm]

/-- Linearity of the finite divergence. -/
theorem finiteGaussianDivergence_sub (F G : V → V) (x : V) (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    finiteGaussianDivergence (fun y => F y - G y) x =
      finiteGaussianDivergence F x - finiteGaussianDivergence G x := by
  unfold finiteGaussianDivergence
  rw [fderiv_fun_sub hF hG, inner_sub_right]
  simp only [ContinuousLinearMap.coe_sub, map_sub]
  ring

section Projection

variable (U : Submodule ℝ V)

/-- `U` with the Borel structure of its own topology. -/
local instance subspaceMeasurableSpace : MeasurableSpace U := borel U

local instance subspaceBorelSpace : BorelSpace U := ⟨rfl⟩

/-- **v2's cylindrical approximant is the head divergence.** For the orthogonal projection
`P` onto `U`, the divergence on `V` of `x ↦ P G(P x)` equals the divergence on `U` of the
head field `u ↦ P G(u)`, evaluated at `P x`. -/
theorem finiteGaussianDivergence_starProjection_comp (G : V → V) (x : V)
    (hG : DifferentiableAt ℝ G (U.starProjection x)) :
    finiteGaussianDivergence (fun y => U.starProjection (G (U.starProjection y))) x =
      finiteGaussianDivergence (V := U) (fun u => U.orthogonalProjectionOnto (G u))
        (U.orthogonalProjectionOnto x) := by
  set p : V →L[ℝ] U := U.orthogonalProjectionOnto with hp
  set ι : U →L[ℝ] V := U.subtypeL with hι
  have hP : U.starProjection = ι.comp p := rfl
  set D := fderiv ℝ G (U.starProjection x) with hD
  have hdV : fderiv ℝ (fun y => U.starProjection (G (U.starProjection y))) x =
      (ι.comp p).comp (D.comp (ι.comp p)) := by
    have h1 : HasFDerivAt (fun y => U.starProjection y) (ι.comp p) x := by
      rw [hP]; exact (ι.comp p).hasFDerivAt
    have h2 := hG.hasFDerivAt.comp x h1
    have h3 := (ι.comp p).hasFDerivAt.comp x h2
    rw [← hP]
    exact h3.fderiv
  have hdU : fderiv ℝ (fun u : U => p (G u)) (p x) = p.comp (D.comp ι) := by
    have h1 : HasFDerivAt (fun u : U => (u : V)) ι (p x) := ι.hasFDerivAt
    have hG' : DifferentiableAt ℝ G ((p x : U) : V) := hG
    have h2 := hG'.hasFDerivAt.comp (p x) h1
    have h3 := p.hasFDerivAt.comp (p x) h2
    exact h3.fderiv
  unfold finiteGaussianDivergence
  rw [hdV, hdU]
  congr 1
  · -- the pairing
    change ⟪x, ((p (G (U.starProjection x)) : U) : V)⟫ =
      ⟪((p x : U) : V), ((p (G (U.starProjection x)) : U) : V)⟫
    rw [← Submodule.starProjection_apply, ← Submodule.starProjection_apply]
    set y := G (U.starProjection x)
    have hidem : U.starProjection (U.starProjection y) = U.starProjection y :=
      Submodule.starProjection_eq_self_iff.2 (by
        rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _)
    rw [Submodule.inner_starProjection_left_eq_right, hidem]
  · -- the trace
    have hpι : p.comp ι = ContinuousLinearMap.id ℝ U := by
      ext u; simp [hp, hι]
    set g : U →L[ℝ] V := (ι.comp p).comp (D.comp ι) with hg
    have := LinearMap.trace_comp_comm' (R := ℝ) (p : V →ₗ[ℝ] U) (g : U →ₗ[ℝ] V)
    have e1 : (((ι.comp p).comp (D.comp (ι.comp p)) : V →L[ℝ] V) : V →ₗ[ℝ] V) =
        (g : U →ₗ[ℝ] V) ∘ₗ (p : V →ₗ[ℝ] U) := by
      ext v; rfl
    have e2 : (p : V →ₗ[ℝ] U) ∘ₗ (g : U →ₗ[ℝ] V) =
        ((p.comp (D.comp ι) : U →L[ℝ] U) : U →ₗ[ℝ] U) := by
      refine LinearMap.ext fun u => ?_
      change p (ι (p (D (ι u)))) = p (D (ι u))
      rw [show ι (p (D (ι u))) = ((p (D (ι u)) : U) : V) from rfl,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rw [e1, this, e2]

end Projection

section Duality

/-- **The divergence is determined by duality.** Two continuous functions that both satisfy
the Gaussian integration-by-parts identity `∫ φ d dγ = ∫ Dφ(F) dγ` against every smooth
compactly supported `φ` are equal. -/
theorem eq_of_gaussian_duality (F : V → V) (d₁ d₂ : V → ℝ)
    (hd₁ : Continuous d₁) (hd₂ : Continuous d₂)
    (h₁ : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x * d₁ x ∂(finiteStdGaussian V) = ∫ x, fderiv ℝ φ x (F x) ∂(finiteStdGaussian V))
    (h₂ : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x * d₂ x ∂(finiteStdGaussian V) = ∫ x, fderiv ℝ φ x (F x) ∂(finiteStdGaussian V)) :
    d₁ = d₂ := by
  set ρ := finiteGaussianDensity V
  have hρc : Continuous ρ := continuous_finiteGaussianDensity
  have hconv : ∀ g : V → ℝ, ∫ x, g x ∂(finiteStdGaussian V) = ∫ x, ρ x * g x := by
    intro g
    rw [finiteStdGaussian, integral_withDensity_eq_integral_toReal_smul
      (continuous_finiteGaussianDensity.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    congr 1; funext x
    rw [ENNReal.toReal_ofReal (finiteGaussianDensity_pos x).le, smul_eq_mul]
  set f : V → ℝ := fun x => ρ x * (d₁ x - d₂ x) with hf
  have hfc : Continuous f := hρc.mul (hd₁.sub hd₂)
  have hzero : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x • f x = 0 := by
    intro φ hφ hφc
    have e1 := h₁ φ hφ hφc
    have e2 := h₂ φ hφ hφc
    rw [hconv, hconv] at e1 e2
    have i1 : Integrable (fun x => ρ x * (φ x * d₁ x)) :=
      (hρc.mul (hφ.continuous.mul hd₁)).integrable_of_hasCompactSupport
        ((hφc.mul_right).mul_left)
    have i2 : Integrable (fun x => ρ x * (φ x * d₂ x)) :=
      (hρc.mul (hφ.continuous.mul hd₂)).integrable_of_hasCompactSupport
        ((hφc.mul_right).mul_left)
    have : (fun x => φ x • f x) = fun x => ρ x * (φ x * d₁ x) - ρ x * (φ x * d₂ x) := by
      funext x; simp only [hf, smul_eq_mul]; ring
    rw [this, integral_sub i1 i2, e1, e2, sub_self]
  have hae : ∀ᵐ x ∂(volume : Measure V), f x = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hfc.locallyIntegrable hzero
  have hfeq : f = 0 := (Continuous.ae_eq_iff_eq volume hfc continuous_const).1 hae
  funext x
  have hx := congrFun hfeq x
  simp only [hf, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with h | h
  · exact absurd h (finiteGaussianDensity_pos x).ne'
  · exact sub_eq_zero.1 h

/-- Any continuous function satisfying the Gaussian duality for a `C¹` field `F` is the
finite Gaussian divergence `δF`. -/
theorem eq_finiteGaussianDivergence_of_duality (F : V → V) (hF : ContDiff ℝ 1 F)
    (d : V → ℝ) (hd : Continuous d)
    (h : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x * d x ∂(finiteStdGaussian V) = ∫ x, fderiv ℝ φ x (F x) ∂(finiteStdGaussian V)) :
    d = finiteGaussianDivergence F := by
  refine eq_of_gaussian_duality F d _ hd ?_ h ?_
  · unfold finiteGaussianDivergence
    have hF' : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
    have htr : Continuous (fun x => LinearMap.trace ℝ V
        ((fderiv ℝ F x : V →L[ℝ] V) : V →ₗ[ℝ] V)) := by
      let b := stdOrthonormalBasis ℝ V
      simp_rw [LinearMap.trace_eq_sum_inner _ b]
      exact continuous_finsetSum _ (fun i _ =>
        continuous_const.inner (hF'.clm_apply continuous_const))
    exact (continuous_id.inner hF.continuous).sub htr
  · intro φ hφ hφc
    exact integral_mul_finiteGaussianDivergence φ F (hφ.of_le (by norm_cast)) hφc hF

end Duality

end NlsGge.Ramer
