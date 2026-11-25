import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.ThirdConsultation.G3.G3006Host
import NlsGge.GK38.TauGamma
import NlsGge.GK38.XiSqCanonical
import Armstrong.Work.ActualCartesianXYModels

                                                                                         
                                                                               
                                                                                                                  
                                                                                                                          
                                                                               
                                                                                                               
                                                                                                     
                                                                                 
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5018M5Aux
noncomputable section

/-- Pure scalar algebra of the angle differential, `s' = s^-1`. -/
theorem angle_alg (ξ dξ c dc dθ s s' ds ds' : ℂ) (hξ : ξ ≠ 0) (hc : c ≠ 0) (hs : s ≠ 0)
    (hss : s * s' = 1) (hds : ds = s * Complex.I * dθ) (hds' : ds' = s' * (-Complex.I) * dθ) :
    let X := ξ / (Real.sqrt 8 : ℂ) * (c * (s + s'))
    let Y := ξ / ((Real.sqrt 8 : ℂ) * Complex.I) * (c * (s - s'))
    let dX := (dξ * (c * (s + s')) + ξ * (dc * (s + s') + c * (ds + ds'))) / (Real.sqrt 8 : ℂ)
    let dY := (dξ * (c * (s - s')) + ξ * (dc * (s - s') + c * (ds - ds'))) /
      ((Real.sqrt 8 : ℂ) * Complex.I)
    (X ^ 2 + Y ^ 2)⁻¹ * (X * dY - Y * dX) = dθ := by
  intro X Y dX dY
  have hs' : s' = s⁻¹ := eq_inv_of_mul_eq_one_right hss
  subst hs'
  have h8 : (Real.sqrt 8 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num)).ne'
  have h8sq : (Real.sqrt 8 : ℂ) ^ 2 = 8 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hX2 : X ^ 2 + Y ^ 2 = ξ ^ 2 * c ^ 2 / 2 := by
    simp only [X, Y]
    field_simp
    rw [h8sq]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hne : X ^ 2 + Y ^ 2 ≠ 0 := by
    rw [hX2]; exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hξ) (pow_ne_zero 2 hc)) two_ne_zero
  rw [inv_mul_eq_iff_eq_mul₀ hne, hX2]
  simp only [X, Y, dX, dY, hds, hds']
  field_simp
  rw [h8sq]
  ring_nf

/-- The angle differential identity at a point. -/
theorem angle_diff_eq (n : ℤ) (φ : PotPair) (V : Set PotPair) (hVo : IsOpen V) (hφV : φ ∈ V)
    (hVsub : V ⊆ sourceW \ collapsedSet n) (a b e : PotPair → ℂ)
    (haA : DifferentiableAt ℂ a φ) (hbA : DifferentiableAt ℂ b φ) (heA : DifferentiableAt ℂ e φ)
    (hpair : ∀ ψ ∈ V, ({a ψ, b ψ} : Set ℂ) = {lamMinus ψ n, lamPlus ψ n})
    (hZ : ∀ ψ ∈ V, gk16ActualScalarZPlus38 sourceF n ψ = (b ψ - a ψ) * Complex.exp (Complex.I * e ψ))
    (hξA : DifferentiableAt ℂ (xiN38 n) φ) (hξ0 : xiN38 n φ ≠ 0)
    (hβ : DifferentiableAt ℂ (betaSum n) φ) :
    angleDerivative n φ - fderiv ℂ (betaSum n) φ = fderiv ℂ e φ := by
  have hgk : ∀ ψ ∈ V, ψ ∈ gkW := fun ψ hψ => sourceFamily.W_gk (hVsub hψ).1
  have hc2 : ∀ ψ ∈ V, (b ψ - a ψ) ^ 2 = gamma2 ψ n := by
    intro ψ hψ
    rw [gamma2_value38 ψ (hgk ψ hψ) n]
    rcases Set.pair_eq_pair_iff.1 (hpair ψ hψ) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; ring
  have hcne : ∀ ψ ∈ V, b ψ - a ψ ≠ 0 := by
    intro ψ hψ h
    apply (hVsub hψ).2
    refine ⟨(hVsub hψ).1, ?_⟩
    rw [← hc2 ψ hψ, h]; ring
  have hZm : ∀ ψ ∈ V, gk16ActualScalarZMinus38 sourceF n ψ =
      (b ψ - a ψ) * Complex.exp (-(Complex.I * e ψ)) := by
    intro ψ hψ
    have hprod := gk16_actual_scalar_models_product38 sourceF n ψ (hgk ψ hψ)
    rw [hZ ψ hψ, ← hc2 ψ hψ] at hprod
    have hc := hcne ψ hψ
    have hE : Complex.exp (Complex.I * e ψ) ≠ 0 := Complex.exp_ne_zero _
    rw [Complex.exp_neg]
    field_simp
    field_simp at hprod
    linear_combination hprod
  set θ : PotPair → ℂ := fun ψ => e ψ + betaSum n ψ with hθ
  set c : PotPair → ℂ := fun ψ => b ψ - a ψ with hc
  set Xf : PotPair → ℂ := fun ψ => xiN38 n ψ * (Real.sqrt 8 : ℂ)⁻¹ *
    (c ψ * (Complex.exp (Complex.I * θ ψ) + Complex.exp (-Complex.I * θ ψ))) with hXf
  set Yf : PotPair → ℂ := fun ψ => xiN38 n ψ * ((Real.sqrt 8 : ℂ) * Complex.I)⁻¹ *
    (c ψ * (Complex.exp (Complex.I * θ ψ) - Complex.exp (-Complex.I * θ ψ))) with hYf
  have hev : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V := hVo.mem_nhds hφV
  have hXe : cartesianX n =ᶠ[𝓝 φ] Xf := by
    filter_upwards [hev] with ψ hψ
    show gk16ScalarXModel38 sourceF betaSum n ψ = _
    unfold gk16ScalarXModel38
    rw [hZ ψ hψ, hZm ψ hψ]
    simp only [hXf, hθ, hc]
    have e1 : Complex.exp (Complex.I * (e ψ + betaSum n ψ)) =
        Complex.exp (Complex.I * e ψ) * Complex.exp (Complex.I * betaSum n ψ) := by
      rw [mul_add, Complex.exp_add]
    have e2 : Complex.exp (-Complex.I * (e ψ + betaSum n ψ)) =
        Complex.exp (-(Complex.I * e ψ)) * Complex.exp (-Complex.I * betaSum n ψ) := by
      rw [show -Complex.I * (e ψ + betaSum n ψ) =
        -(Complex.I * e ψ) + -Complex.I * betaSum n ψ by ring, Complex.exp_add]
    rw [e1, e2]
    ring
  have hYe : cartesianY n =ᶠ[𝓝 φ] Yf := by
    filter_upwards [hev] with ψ hψ
    show gk16ScalarYModel38 sourceF betaSum n ψ = _
    unfold gk16ScalarYModel38
    rw [hZ ψ hψ, hZm ψ hψ]
    simp only [hYf, hθ, hc]
    have e1 : Complex.exp (Complex.I * (e ψ + betaSum n ψ)) =
        Complex.exp (Complex.I * e ψ) * Complex.exp (Complex.I * betaSum n ψ) := by
      rw [mul_add, Complex.exp_add]
    have e2 : Complex.exp (-Complex.I * (e ψ + betaSum n ψ)) =
        Complex.exp (-(Complex.I * e ψ)) * Complex.exp (-Complex.I * betaSum n ψ) := by
      rw [show -Complex.I * (e ψ + betaSum n ψ) =
        -(Complex.I * e ψ) + -Complex.I * betaSum n ψ by ring, Complex.exp_add]
    rw [e1, e2]
    ring
  have hXφ : cartesianX n φ = Xf φ := hXe.eq_of_nhds
  have hYφ : cartesianY n φ = Yf φ := hYe.eq_of_nhds
  -- derivatives
  have hξd : HasFDerivAt (xiN38 n) (fderiv ℂ (xiN38 n) φ) φ := hξA.hasFDerivAt
  have hcd : HasFDerivAt c (fderiv ℂ b φ - fderiv ℂ a φ) φ := hbA.hasFDerivAt.sub haA.hasFDerivAt
  have hθd : HasFDerivAt θ (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) φ :=
    heA.hasFDerivAt.add hβ.hasFDerivAt
  have hsd := (hθd.const_mul Complex.I).cexp
  have hsd' := (hθd.const_mul (-Complex.I)).cexp
  have hXd : HasFDerivAt Xf _ φ := (hξd.mul_const (Real.sqrt 8 : ℂ)⁻¹).mul (hcd.mul (hsd.add hsd'))
  have hYd : HasFDerivAt Yf _ φ := (hξd.mul_const ((Real.sqrt 8 : ℂ) * Complex.I)⁻¹).mul (hcd.mul (hsd.sub hsd'))
  have hcφ : c φ ≠ 0 := hcne φ hφV
  have hs0 : Complex.exp (Complex.I * θ φ) ≠ 0 := Complex.exp_ne_zero _
  have hss : Complex.exp (Complex.I * θ φ) * Complex.exp (-Complex.I * θ φ) = 1 := by
    rw [← Complex.exp_add]; simp
  refine ContinuousLinearMap.ext fun v => ?_
  have hfX : fderiv ℂ (cartesianX n) φ = fderiv ℂ Xf φ := hXe.fderiv_eq
  have hfY : fderiv ℂ (cartesianY n) φ = fderiv ℂ Yf φ := hYe.fderiv_eq
  have key := angle_alg (xiN38 n φ) (fderiv ℂ (xiN38 n) φ v) (c φ)
    ((fderiv ℂ b φ - fderiv ℂ a φ) v) ((fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v)
    (Complex.exp (Complex.I * θ φ)) (Complex.exp (-Complex.I * θ φ))
    (Complex.exp (Complex.I * θ φ) * Complex.I * (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v)
    (Complex.exp (-Complex.I * θ φ) * (-Complex.I) * (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v)
    hξ0 hcφ hs0 hss rfl rfl
  simp only at key
  have hXφ' : Xf φ = xiN38 n φ / (Real.sqrt 8 : ℂ) *
      (c φ * (Complex.exp (Complex.I * θ φ) + Complex.exp (-Complex.I * θ φ))) := by
    simp only [hXf, div_eq_mul_inv]
  have hYφ' : Yf φ = xiN38 n φ / ((Real.sqrt 8 : ℂ) * Complex.I) *
      (c φ * (Complex.exp (Complex.I * θ φ) - Complex.exp (-Complex.I * θ φ))) := by
    simp only [hYf, div_eq_mul_inv]
  have hXv : fderiv ℂ Xf φ v =
      (fderiv ℂ (xiN38 n) φ v * (c φ * (Complex.exp (Complex.I * θ φ) + Complex.exp (-Complex.I * θ φ))) +
        xiN38 n φ * ((fderiv ℂ b φ - fderiv ℂ a φ) v *
          (Complex.exp (Complex.I * θ φ) + Complex.exp (-Complex.I * θ φ)) +
        c φ * (Complex.exp (Complex.I * θ φ) * Complex.I * (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v +
          Complex.exp (-Complex.I * θ φ) * (-Complex.I) * (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v))) /
        (Real.sqrt 8 : ℂ) := by
    rw [hXd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.sub_apply]
    simp only [hXf, div_eq_mul_inv]
    ring
  have hYv : fderiv ℂ Yf φ v =
      (fderiv ℂ (xiN38 n) φ v * (c φ * (Complex.exp (Complex.I * θ φ) - Complex.exp (-Complex.I * θ φ))) +
        xiN38 n φ * ((fderiv ℂ b φ - fderiv ℂ a φ) v *
          (Complex.exp (Complex.I * θ φ) - Complex.exp (-Complex.I * θ φ)) +
        c φ * (Complex.exp (Complex.I * θ φ) * Complex.I * (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v -
          Complex.exp (-Complex.I * θ φ) * (-Complex.I) * (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v))) /
        ((Real.sqrt 8 : ℂ) * Complex.I) := by
    rw [hYd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.sub_apply]
    simp only [hYf, div_eq_mul_inv]
    ring
  have hang : angleDerivative n φ v = (fderiv ℂ e φ + fderiv ℂ (betaSum n) φ) v := by
    unfold angleDerivative
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul, hfX, hfY,
      hXφ, hYφ, hXφ', hYφ', hXv, hYv]
    exact key
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] at hang ⊢
  rw [hang]
  ring

end
end G5018M5Aux
end NlsGge.GKDefinitionDesign
