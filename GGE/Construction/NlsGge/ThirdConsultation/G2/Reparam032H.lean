import Mathlib
import NlsGge.ThirdConsultation.G2.Reparam032G

                                                                                                                    
                                                                                         
                                                                                                         
                                                                                                  
                                                            
                                                                                                   
set_option autoImplicit false
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Homo
noncomputable section

theorem ellF_contDiff (p q : ℂ) :
    ContDiff ℝ 2 (fun t : ℝ => NlsGge.GKDefinitionDesign.G2032Ellipse.ellF p q t) := by
  have hofR : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have h1 : ContDiff ℝ 2 (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp (hofR.mul contDiff_const)
  have h2 : ContDiff ℝ 2 (fun t : ℝ => Complex.exp (-((t : ℂ) * Complex.I))) :=
    Complex.contDiff_exp.comp (hofR.mul contDiff_const).neg
  unfold NlsGge.GKDefinitionDesign.G2032Ellipse.ellF
  exact (contDiff_const.mul h1).add (contDiff_const.mul h2)

theorem ellF_ne_zero_gen (p q : ℂ) (hpq : ‖q‖ < ‖p‖) (t : ℝ) :
    NlsGge.GKDefinitionDesign.G2032Ellipse.ellF p q t ≠ 0 := by
  intro h
  have h1 := NlsGge.GKDefinitionDesign.G2032Ellipse.norm_ellF_eq p q hpq t
  rw [h, norm_zero] at h1
  have hp : 0 < ‖p‖ := lt_of_le_of_lt (norm_nonneg q) hpq
  have hw := NlsGge.GKDefinitionDesign.G2032Ellipse.one_add_ellZ_ne_zero p q hpq t
  have hw' : 0 < ‖1 + NlsGge.GKDefinitionDesign.G2032Ellipse.ellZ p q t‖ := norm_pos_iff.mpr hw
  nlinarith [mul_pos hp hw']

theorem rayR_contDiff (w : ℂ) (R : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2) :
    ContDiff ℝ 2 (fun α : ℝ => NlsGge.GKDefinitionDesign.G2032Homotopy.rayR w R α) := by
  have hpos : ∀ α : ℝ,
      0 < (w.re * Real.cos α + w.im * Real.sin α) ^ 2 - (w.re ^ 2 + w.im ^ 2) + R ^ 2 := by
    intro α
    nlinarith [sq_nonneg (w.re * Real.cos α + w.im * Real.sin α)]
  have hB : ContDiff ℝ 2 (fun α : ℝ => w.re * Real.cos α + w.im * Real.sin α) :=
    (contDiff_const.mul Real.contDiff_cos).add (contDiff_const.mul Real.contDiff_sin)
  have hD : ContDiff ℝ 2 (fun α : ℝ =>
      (w.re * Real.cos α + w.im * Real.sin α) ^ 2 - (w.re ^ 2 + w.im ^ 2) + R ^ 2) :=
    ((hB.pow 2).sub contDiff_const).add contDiff_const
  unfold NlsGge.GKDefinitionDesign.G2032Homotopy.rayR NlsGge.GKDefinitionDesign.G2032Homotopy.rayB
    NlsGge.GKDefinitionDesign.G2032Homotopy.rayD
  exact hB.neg.add (ContDiff.sqrt hD (fun α => (hpos α).ne'))

theorem homH_contDiff (τ C γ : ℂ) (R ρ : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ)
    (hw : (τ - C).re ^ 2 + (τ - C).im ^ 2 < R ^ 2) :
    ContDiff ℝ 2 (fun st : ℝ × ℝ => NlsGge.GKDefinitionDesign.G2032Homo.homH τ C γ R ρ st.1 st.2) := by
  have hpq := NlsGge.GKDefinitionDesign.G2032Homo.pq_norm_lt γ ρ hγ hρ
  have hofR : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hβ : ContDiff ℝ 2 (fun st : ℝ × ℝ =>
      NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) st.2) :=
    (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg_contDiff _ _ hpq).comp contDiff_snd
  have hr : ContDiff ℝ 2 (fun st : ℝ × ℝ =>
      NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R
        (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) st.2)) :=
    (rayR_contDiff _ _ hw).comp hβ
  have hN : ContDiff ℝ 2 (fun st : ℝ × ℝ =>
      ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) st.2‖) :=
    ContDiff.norm ℝ ((ellF_contDiff _ _).comp contDiff_snd)
      (fun st : ℝ × ℝ => ellF_ne_zero_gen _ _ hpq st.2)
  have he : ContDiff ℝ 2 (fun st : ℝ × ℝ =>
      Complex.exp ((NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) st.2 : ℂ) *
        Complex.I)) :=
    Complex.contDiff_exp.comp ((hofR.comp hβ).mul contDiff_const)
  have hreal : ContDiff ℝ 2 (fun st : ℝ × ℝ =>
      (1 - st.1) * NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R
        (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) st.2) +
      st.1 * ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) st.2‖) :=
    ((contDiff_const.sub contDiff_fst).mul hr).add (contDiff_fst.mul hN)
  have hcx : ContDiff ℝ 2 (fun st : ℝ × ℝ =>
      (((1 - st.1) * NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R
        (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) st.2) +
      st.1 * ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) st.2‖ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  unfold NlsGge.GKDefinitionDesign.G2032Homo.homH
  exact contDiff_const.add (hcx.mul he)

/-- Convex bound on the segment between the two endpoints. -/
theorem endpoint_convex_bound (w γ : ℂ) (M : ℝ) (hA : ‖w + γ / 2‖ ≤ M) (hB : ‖w - γ / 2‖ ≤ M)
    (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    ‖w + (x : ℂ) * (γ / 2)‖ ≤ M := by
  have hid : w + (x : ℂ) * (γ / 2) =
      ((((1 + x) / 2 : ℝ)) : ℂ) * (w + γ / 2) + ((((1 - x) / 2 : ℝ)) : ℂ) * (w - γ / 2) := by
    push_cast
    ring
  rw [hid]
  have h1 : 0 ≤ (1 + x) / 2 := by linarith
  have h2 : 0 ≤ (1 - x) / 2 := by linarith
  calc ‖((((1 + x) / 2 : ℝ)) : ℂ) * (w + γ / 2) + ((((1 - x) / 2 : ℝ)) : ℂ) * (w - γ / 2)‖
      ≤ ‖((((1 + x) / 2 : ℝ)) : ℂ) * (w + γ / 2)‖ + ‖((((1 - x) / 2 : ℝ)) : ℂ) * (w - γ / 2)‖ :=
        norm_add_le _ _
    _ = ((1 + x) / 2) * ‖w + γ / 2‖ + ((1 - x) / 2) * ‖w - γ / 2‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h1,
          Real.norm_of_nonneg h2]
    _ ≤ ((1 + x) / 2) * M + ((1 - x) / 2) * M :=
        add_le_add (mul_le_mul_of_nonneg_left hA h1) (mul_le_mul_of_nonneg_left hB h2)
    _ = M := by ring

/-- Exponential sum identity: `e^{it} + e^{−it} = 2 cos t`. -/
theorem exp_add_exp_neg_eq (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (((-t : ℝ) : ℂ) * Complex.I) =
      2 * (Real.cos t : ℂ) := by
  rw [Complex.ofReal_cos, Complex.cos, show ((-t : ℝ) : ℂ) * Complex.I = -(t : ℂ) * Complex.I by
    push_cast
    ring]
  ring

/-- The ellipse minus its cut-centre term: `E_ρ(t) − (γ/2)cos t = (γ/4)((ρ−1)e^{it} + (ρ⁻¹−1)e^{−it})`. -/
theorem ellF_sub_cos (γ : ℂ) (ρ t : ℝ) :
    NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t - γ / 2 * (Real.cos t : ℂ) =
      γ / 4 * (((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
        ((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) := by
  rw [NlsGge.GKDefinitionDesign.G2032Homo.ellF_pq γ ρ t]
  have hc := exp_add_exp_neg_eq t
  push_cast at hc ⊢
  linear_combination (γ / 4) * hc


/-- ρ-choice: a radius `ρ0 > 1` such that every `1 < ρ ≤ ρ0` keeps the whole ellipse strictly inside the
open disc of radius `R` about `C` (in the translated coordinate `w = τ − C`). -/
theorem rho_choice (w γ : ℂ) (R : ℝ) (hγ : γ ≠ 0) (hA : ‖w + γ / 2‖ < R) (hB : ‖w - γ / 2‖ < R) :
    ∃ ρ0 : ℝ, 1 < ρ0 ∧ ∀ ρ : ℝ, 1 < ρ → ρ ≤ ρ0 → ∀ t : ℝ,
      ‖w + NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t‖ < R := by
  have hγn : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hMlt : max ‖w + γ / 2‖ ‖w - γ / 2‖ < R := max_lt hA hB
  have hRM : 0 < R - max ‖w + γ / 2‖ ‖w - γ / 2‖ := by linarith
  refine ⟨1 + (R - max ‖w + γ / 2‖ ‖w - γ / 2‖) / ‖γ‖, ?_, ?_⟩
  · have : 0 < (R - max ‖w + γ / 2‖ ‖w - γ / 2‖) / ‖γ‖ := div_pos hRM hγn
    linarith
  · intro ρ hρ1 hρ0 t
    have hcos := endpoint_convex_bound w γ (max ‖w + γ / 2‖ ‖w - γ / 2‖) (le_max_left _ _)
      (le_max_right _ _) (Real.cos t) (Real.neg_one_le_cos t) (Real.cos_le_one t)
    have hsplit : w + NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t =
        (w + (Real.cos t : ℂ) * (γ / 2)) +
          (NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t -
            γ / 2 * (Real.cos t : ℂ)) := by
      ring
    have hρinv : ρ⁻¹ < ρ := by
      have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      have h2 : 0 < ρ⁻¹ := inv_pos.mpr (by linarith)
      nlinarith
    have hρinv2 : 2 - ρ ≤ ρ⁻¹ := by
      have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
      have h2 : 0 < ρ⁻¹ := inv_pos.mpr (by linarith)
      nlinarith [sq_nonneg (ρ - 1)]
    have hX : ‖((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
        ((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * (ρ - 1) := by
      have e1 : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
      have e2 : ‖Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ = 1 :=
        Complex.norm_exp_ofReal_mul_I (-t)
      calc ‖((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
            ((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖
          ≤ ‖((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ +
            ‖((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ := norm_add_le _ _
        _ = |ρ - 1| + |ρ⁻¹ - 1| := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, e1, e2, mul_one, mul_one]
        _ ≤ 2 * (ρ - 1) := by
            have ha : |ρ - 1| = ρ - 1 := abs_of_nonneg (by linarith)
            have hb : |ρ⁻¹ - 1| ≤ ρ - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
            linarith
    have hbound : ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t -
        γ / 2 * (Real.cos t : ℂ)‖ ≤ ‖γ‖ * (ρ - 1) / 2 := by
      rw [ellF_sub_cos γ ρ t, norm_mul]
      have h4 : ‖γ / 4‖ = ‖γ‖ / 4 := by
        rw [norm_div]
        norm_num
      rw [h4]
      nlinarith [hX, hγn]
    have hρle : ‖γ‖ * (ρ - 1) ≤ R - max ‖w + γ / 2‖ ‖w - γ / 2‖ := by
      have h := (le_div_iff₀ hγn).mp
        (show ρ - 1 ≤ (R - max ‖w + γ / 2‖ ‖w - γ / 2‖) / ‖γ‖ by linarith)
      linarith [mul_comm (ρ - 1) ‖γ‖]
    rw [hsplit]
    calc ‖(w + (Real.cos t : ℂ) * (γ / 2)) +
          (NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t -
            γ / 2 * (Real.cos t : ℂ))‖
        ≤ ‖w + (Real.cos t : ℂ) * (γ / 2)‖ + ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF
            (pOf γ ρ) (qOf γ ρ) t - γ / 2 * (Real.cos t : ℂ)‖ := norm_add_le _ _
      _ ≤ max ‖w + γ / 2‖ ‖w - γ / 2‖ + ‖γ‖ * (ρ - 1) / 2 := add_le_add hcos hbound
      _ < R := by linarith
end
end G2032Homo
end NlsGge.GKDefinitionDesign

