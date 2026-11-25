import NlsGge.Ramer.FiniteGaussian
import Mathlib.MeasureTheory.Function.Jacobian

/-! # W10a, file 1 (W10.01): the local change of variables for the finite standard Gaussian (B-free)

Source: `paper/v2.tex` l.1644-1655 (proof of `D:thm:localized`): "On a slightly larger open ball,
Lemma `D:lem:localinject` permits the ordinary finite-dimensional change of variables `z_N = T_N x_N`".

Abstract setting: `V` is a finite-dimensional real inner product space with its volume, `γ = finiteStdGaussian V`
(density `(2π)^{-d/2} exp(-‖x‖²/2)`), `φ : V → V` is differentiable on a measurable set `U` with derivative
`φ'`, injective on `U`, and `H : V → ℝ` vanishes off `U`. Then, with the push-forward integrand
`Ψ(z) = H(φ⁻¹ z) / |det φ'(φ⁻¹ z)|` on `φ(U)` and `0` elsewhere (`localPush38`),

`∫ H(v) exp(-(‖φ v‖² - ‖v‖²)/2) dγ(v) = ∫ Ψ(z) dγ(z)`.

No integrability hypothesis is needed (both sides are totalized integrals; the change of variables
theorem of mathlib holds without it). Measurability of `Ψ` is proved from the measurable embedding
`U.domRestrict φ` (`measurableEmbedding_of_fderivWithin`), so the null sets are explicit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Ramer
open scoped ENNReal

section LocalCoV

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The push-forward integrand `Ψ = (ψ ∘ (φ|_U)⁻¹) 1_{φ(U)}` (zero outside `φ(U)`). -/
def localPush38 (φ : V → V) (U : Set V) (ψ : U → ℝ) : V → ℝ :=
  Function.extend (U.domRestrict φ) ψ 0

theorem localPush38_apply (φ : V → V) (U : Set V) (hinj : Set.InjOn φ U) (ψ : U → ℝ) (x : V)
    (hx : x ∈ U) : localPush38 φ U ψ (φ x) = ψ ⟨x, hx⟩ := by
  have hi : Function.Injective (U.domRestrict φ) := hinj.injective
  exact hi.extend_apply ψ 0 ⟨x, hx⟩

theorem localPush38_eq_zero (φ : V → V) (U : Set V) (ψ : U → ℝ) (z : V) (hz : z ∉ φ '' U) :
    localPush38 φ U ψ z = 0 := by
  unfold localPush38
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨a, ha⟩
    exact hz ⟨a, a.2, ha⟩

theorem measurable_localPush38 (φ : V → V) (φ' : V → V →L[ℝ] V) (U : Set V)
    (hU : MeasurableSet U) (hd : ∀ x ∈ U, HasFDerivWithinAt φ (φ' x) U x)
    (hinj : Set.InjOn φ U) (ψ : U → ℝ) (hψ : Measurable ψ) :
    Measurable (localPush38 φ U ψ) :=
  (measurableEmbedding_of_fderivWithin hU hd hinj).measurable_extend hψ measurable_const

/-- **W10.01 (abstract).** The local change of variables for the standard Gaussian of `V`. -/
theorem localCoV_gaussian38 (φ : V → V) (φ' : V → V →L[ℝ] V) (U : Set V) (hU : MeasurableSet U)
    (hd : ∀ x ∈ U, HasFDerivWithinAt φ (φ' x) U x) (hinj : Set.InjOn φ U)
    (hdet : ∀ x ∈ U, (φ' x).det ≠ 0) (H : V → ℝ) (hHU : ∀ v, v ∉ U → H v = 0) :
    ∫ v, H v * Real.exp (-(‖φ v‖ ^ 2 - ‖v‖ ^ 2) / 2) ∂(finiteStdGaussian V) =
      ∫ z, localPush38 φ U (fun x => H x / |(φ' x).det|) z ∂(finiteStdGaussian V) := by
  set ρ : V → ℝ := finiteGaussianDensity V with hρ
  have hρm : Measurable (fun x : V => ENNReal.ofReal (ρ x)) :=
    (continuous_finiteGaussianDensity (V := V)).measurable.ennreal_ofReal
  have hρpos : ∀ x, 0 < ρ x := fun x => finiteGaussianDensity_pos x
  have hW : ∀ g : V → ℝ, ∫ v, g v ∂(finiteStdGaussian V) = ∫ v, ρ v * g v ∂(volume : Measure V) := by
    intro g
    unfold finiteStdGaussian
    rw [integral_withDensity_eq_integral_toReal_smul hρm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos v).le, smul_eq_mul]
  have hρφ : ∀ v, ρ v * Real.exp (-(‖φ v‖ ^ 2 - ‖v‖ ^ 2) / 2) = ρ (φ v) := by
    intro v
    simp only [hρ, finiteGaussianDensity]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hW, hW]
  have h1 : ∀ v, ρ v * (H v * Real.exp (-(‖φ v‖ ^ 2 - ‖v‖ ^ 2) / 2)) = H v * ρ (φ v) := by
    intro v; rw [← hρφ]; ring
  simp only [h1]
  set Ψ := localPush38 φ U (fun x => H x / |(φ' x).det|) with hΨ
  have hU0 : ∫ v, H v * ρ (φ v) ∂(volume : Measure V) =
      ∫ v in U, H v * ρ (φ v) ∂(volume : Measure V) := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by rw [hHU v hv, zero_mul])
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure V) hU hd hinj
    (fun z => ρ z * Ψ z)
  have hcongr : ∫ v in U, |(φ' v).det| • (ρ (φ v) * Ψ (φ v)) ∂(volume : Measure V) =
      ∫ v in U, H v * ρ (φ v) ∂(volume : Measure V) := by
    refine setIntegral_congr_fun hU (fun v hv => ?_)
    simp only [smul_eq_mul]
    rw [hΨ, localPush38_apply φ U hinj _ v hv]
    have hd0 : |(φ' v).det| ≠ 0 := abs_ne_zero.2 (hdet v hv)
    field_simp
  have hsupp : ∫ z in φ '' U, ρ z * Ψ z ∂(volume : Measure V) =
      ∫ z, ρ z * Ψ z ∂(volume : Measure V) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
    rw [hΨ, localPush38_eq_zero φ U _ z hz, mul_zero]
  rw [hU0, ← hcongr, ← hcov, hsupp]

end LocalCoV

end NlsGge.Birkhoff
end
