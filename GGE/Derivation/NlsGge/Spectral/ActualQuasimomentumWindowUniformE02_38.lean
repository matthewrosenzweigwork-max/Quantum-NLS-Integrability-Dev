import NlsGge.Spectral.ActualQuasimomentumFullInfinityE02_38
import NlsGge.Spectral.ActualGapsActionsE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # Uniform Window hypothesis (WU, campaign 38) -/

/-- Root separation at height `≥ 1`: the inside root `w` of `w² - 2Dw + 1 = 0` is close to the
vacuum root `ζ` in RATIO, controlled by the normalized error `ζ(D - (ζ+ζ⁻¹)/2)`. -/
theorem root_ratio_close_of_separated_E02_38 (w ζ D : ℂ) (hζ0 : ζ ≠ 0)
    (hζ : ‖ζ‖ ≤ Real.exp (-1)) (hroot : w^2 - 2*D*w + 1 = 0) (hw : ‖w‖ < 1) (ε : ℝ)
    (hε : ‖ζ * (D - (ζ + ζ⁻¹)/2)‖ ≤ ε) (hε8 : ε ≤ 1/8) :
    ‖w/ζ - 1‖ ≤ 8*ε := by
  have hζpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have he1 : Real.exp (-1) < 1/2 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1:ℝ) ≠ 0)
    rw [Real.exp_neg]; rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hε
  set Δ' := D - (ζ + ζ⁻¹)/2
  have hprod : (w - ζ) * (w - ζ⁻¹) = 2*w*Δ' := by
    have : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
    simp only [Δ']
    linear_combination hroot + this
  have hsep : (1 - ‖ζ‖)/‖ζ‖ ≤ ‖w - ζ⁻¹‖ := by
    have h1 : ‖ζ⁻¹‖ ≤ ‖w - ζ⁻¹‖ + ‖w‖ := by
      have := norm_sub_le w (w - ζ⁻¹); simp only [sub_sub_cancel] at this; linarith [norm_sub_rev w ζ⁻¹]
    rw [norm_inv] at h1
    rw [sub_div, div_self hζpos.ne', one_div]
    linarith
  have hsep0 : 0 < (1 - ‖ζ‖)/‖ζ‖ := div_pos (by linarith) hζpos
  have hΔ : ‖Δ'‖ ≤ ε/‖ζ‖ := by
    rw [le_div_iff₀ hζpos, mul_comm, ← norm_mul]; exact hε
  have hwz : ‖w - ζ‖ ≤ 4*ε*‖w‖ := by
    have h := congrArg norm hprod
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_two] at h
    have hpos : 0 < ‖w - ζ⁻¹‖ := lt_of_lt_of_le hsep0 hsep
    have : ‖w - ζ‖ = 2*‖w‖*‖Δ'‖/‖w - ζ⁻¹‖ := by
      rw [eq_div_iff hpos.ne', h]
    rw [this, div_le_iff₀ hpos]
    calc 2*‖w‖*‖Δ'‖ ≤ 2*‖w‖*(ε/‖ζ‖) := by gcongr
      _ = 2*ε*‖w‖ * (1/‖ζ‖) := by ring
      _ ≤ 2*ε*‖w‖ * (2*((1 - ‖ζ‖)/‖ζ‖)) := by
          gcongr
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hζpos]; linarith
      _ = 4*ε*‖w‖ * ((1 - ‖ζ‖)/‖ζ‖) := by ring
      _ ≤ 4*ε*‖w‖ * ‖w - ζ⁻¹‖ := by gcongr
  have hw2 : ‖w‖ ≤ 2*‖ζ‖ := by
    have : ‖w‖ ≤ ‖ζ‖ + ‖w - ζ‖ := by
      have := norm_add_le ζ (w - ζ); simpa using this
    nlinarith
  rw [show w/ζ - 1 = (w - ζ)/ζ by field_simp, norm_div, div_le_iff₀ hζpos]
  nlinarith


theorem exp_I_mul_cos_E02_38 (z : ℂ) :
    Complex.exp (Complex.I*z) * Complex.cos z = (1 + Complex.exp (2*Complex.I*z))/2 := by
  rw [Complex.cos, mul_div_assoc', mul_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [show Complex.I*z + -z*Complex.I = 0 by ring, show Complex.I*z + z*Complex.I = 2*Complex.I*z by ring,
    Complex.exp_zero]
  ring

/-- WU, conditional on the normalized coupled strip bound with error `ε ≤ 1/20000`:
the Window hypothesis holds. -/
theorem actualQuasimomentumWindow_of_normalizedStrip_E02_38 (u : PhysicalL2) (n : ℤ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1/20000)
    (hstrip : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z : ℂ, |z.re - n*Real.pi| ≤ 1 → 0 ≤ z.im →
      ‖Complex.exp (Complex.I*z) * actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z -
        (1 + Complex.exp (2*Complex.I*z))/2‖ ≤ ε) :
    ActualQuasimomentumWindowE02_38 u n := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set k := actualQuasimomentumE02_38 u
  have he3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set η : ℝ := max (3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * ε)) (8*ε)
  have hη : η < 1/6 := by
    apply max_lt
    · have h1 : 2 * Real.exp 1 * ε ≤ 6/20000 := by nlinarith
      have h2 : Real.sqrt (2 * Real.exp 1 * ε) ≤ Real.sqrt (6/20000) := Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt (6/20000) < 1/57 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have h4 : Real.sqrt (2 * Real.exp 1 * ε) < 1/57 := lt_of_le_of_lt h2 h3
      have h5 : 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * ε) ≤ 3 * 3 * (1/57) := by
        apply mul_le_mul (by linarith) h4.le (Real.sqrt_nonneg _) (by norm_num)
      linarith
    · linarith
  have h1u : (((1:ℝ):ℂ) • u) = u := by simp
  -- closeness of exp(i(k - z)) to 1 on the half-strip
  let S : Set ℂ := {z : ℂ | |z.re - n*Real.pi| ≤ 1/2} ∩ {z : ℂ | 0 < z.im}
  have hnear : ∀ z ∈ S, ‖Complex.exp (Complex.I * (k z - z)) - 1‖ ≤ η := by
    rintro z ⟨hzr, hzi⟩
    have hzi' : 0 < z.im := hzi
    have hzr' : |z.re - n*Real.pi| ≤ 1 := le_trans hzr (by norm_num)
    have hexp_neg : ‖Complex.exp (-(Complex.I*z))‖ = Real.exp z.im := by
      rw [Complex.norm_exp]; simp
    have hexp : ‖Complex.exp (Complex.I*z)‖ = Real.exp (-z.im) := by
      rw [Complex.norm_exp]; simp
    have hfac : Complex.exp (Complex.I * (k z - z)) - 1 =
        (Complex.exp (Complex.I * k z) - Complex.exp (Complex.I * z)) *
          Complex.exp (-(Complex.I*z)) := by
      rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      ring_nf
    rcases le_or_gt z.im 1 with hY | hY
    · -- coupling path
      have htr : ∀ τ ∈ Set.Icc (0:ℝ) 1,
          ‖actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - Complex.cos z‖ ≤ Real.exp 1 * ε := by
        intro τ hτ
        have h := hstrip τ hτ z hzr' hzi'.le
        have heq : actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - Complex.cos z =
            Complex.exp (-(Complex.I*z)) * (Complex.exp (Complex.I*z) *
              actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - (1 + Complex.exp (2*Complex.I*z))/2) := by
          rw [← exp_I_mul_cos_E02_38, ← mul_sub, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
            Complex.exp_zero, one_mul]
        rw [heq, norm_mul, hexp_neg]
        exact mul_le_mul (Real.exp_le_exp.mpr hY) h (norm_nonneg _) he0.le
      have hc := norm_exp_actualQuasimomentum_sub_le_E02_38 u z hzi' _ (by positivity) htr
      rw [hfac, norm_mul, hexp_neg]
      calc ‖Complex.exp (Complex.I * k z) - Complex.exp (Complex.I * z)‖ * Real.exp z.im
          ≤ 3 * Real.sqrt (2 * (Real.exp 1 * ε)) * Real.exp 1 :=
            mul_le_mul hc (Real.exp_le_exp.mpr hY) (Real.exp_pos _).le (by positivity)
        _ = 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * ε) := by ring_nf
        _ ≤ η := le_max_left _ _
    · -- root separation
      set w := Complex.exp (Complex.I * k z)
      set ζ := Complex.exp (Complex.I * z)
      have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
      have hζ : ‖ζ‖ ≤ Real.exp (-1) := by rw [hexp]; exact Real.exp_le_exp.mpr (by linarith)
      have hroot : w^2 - 2*actualPhysicalUnitHalfTrace32 u z*w + 1 = 0 := by
        rw [← hk.2.1 z hzi', Complex.cos]
        have he : w * Complex.exp (-(Complex.I*k z)) = 1 := by
          rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
        rw [show k z*Complex.I = Complex.I*k z by ring, show -k z*Complex.I = -(Complex.I*k z) by ring]
        linear_combination -he
      have hw : ‖w‖ < 1 := by
        rw [Complex.norm_exp]
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
        exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (hk.2.2.1 z hzi'))
      have hnorm : ζ * (actualPhysicalUnitHalfTrace32 u z - (ζ + ζ⁻¹)/2) =
          Complex.exp (Complex.I*z) * actualPhysicalUnitHalfTrace32 u z -
            (1 + Complex.exp (2*Complex.I*z))/2 := by
        have h2 : ζ^2 = Complex.exp (2*Complex.I*z) := by
          rw [← Complex.exp_nat_mul]; push_cast; ring_nf
        rw [← h2]; field_simp; ring
      have hst := hstrip 1 (by simp) z hzr' hzi'.le
      rw [h1u, ← hnorm] at hst
      have hr := root_ratio_close_of_separated_E02_38 w ζ _ hζ0 hζ hroot hw ε hst
        (by linarith)
      have hq : Complex.exp (Complex.I * (k z - z)) = w/ζ := by
        rw [mul_sub, Complex.exp_sub]
      rw [hq]
      exact hr.trans (le_max_right _ _)
  have hSconv : Convex ℝ S := by
    apply Convex.inter
    · have : {z : ℂ | |z.re - n*Real.pi| ≤ 1/2} =
          Complex.re ⁻¹' Set.Icc (n*Real.pi - 1/2) (n*Real.pi + 1/2) := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [this]
      exact (convex_Icc _ _).linear_preimage (Complex.reLm : ℂ →ₗ[ℝ] ℝ)
    · exact convex_halfSpace_im_gt 0
  have hcont : ContinuousOn (fun z => k z - z) S :=
    (hk.1.continuousOn.mono (fun z hz => hz.2)).sub continuousOn_id
  obtain ⟨R₁, hR₁, hhigh⟩ := hk.2.2.2 1 one_pos
  let z₁ : ℂ := (((n:ℝ)*Real.pi : ℝ):ℂ) + Complex.I*((R₁:ℝ):ℂ)
  have hz₁ : z₁ ∈ S := ⟨by simp [z₁], by simp [z₁, hR₁]⟩
  have hz₁s : ‖k z₁ - z₁‖ < 1 := hhigh R₁ le_rfl _
  have hall := norm_le_of_exp_mul_I_near_one_E02_38 S hSconv.isPreconnected _ hcont η
    (by linarith) hnear z₁ hz₁ hz₁s
  intro z hz0 hz1 hzr
  have := hall z ⟨hzr, hz0⟩
  linarith

end NlsGge.SpectralFoundations
end
