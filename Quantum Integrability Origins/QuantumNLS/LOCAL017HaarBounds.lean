import QuantumNLS.LOCAL017HaarAnalytic

/-! Full operator bounds, including the origin.  The pointwise fourth-order
bound is combined with the proved GP-05 Cauchy estimates on balls whose radii
scale with the base point.  No support size occurs in these estimates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Metric Filter Topology MeasureTheory Asymptotics
namespace QuantumNLS.LOCAL017Haar
open Ext025B7LocalPath GP05CauchyMajorantsR14
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {β : H → Cov} {R C : ℝ} (D : ComplexData (E := E) β R C)

/-- The full n-linear complex operator estimate on a scaled ball. -/
theorem cauchy_scaled (hR : 0 < R) (hC : 0 ≤ C) (n : ℕ) {z : E} {r : ℝ}
    (hr : 0 < r) (hzr : ‖z‖ + r ≤ R) :
    ‖iteratedFDeriv ℂ n (complexPrimitive D) z‖ ≤
      (2 * (n+1 : ℕ) / r)^n * (C * Real.pi * (‖z‖ + r)^4) := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have he : (n+1 : ℕ) * (r / (n+1 : ℕ)) = r := by field_simp
  have hs : ball z r ⊆ ball (0 : E) R := by
    intro y hy
    rw [mem_ball_zero_iff]
    have ht : ‖y‖ ≤ dist y z + ‖z‖ := by
      simpa only [dist_zero_right] using dist_triangle y z 0
    have : dist y z < r := hy
    linarith
  have hb : ∀ y ∈ ball z r, ‖complexPrimitive D y‖ ≤ C * Real.pi * (‖z‖ + r)^4 := by
    intro y hy
    apply (complex_bound D hC (hs hy)).trans
    have ht : ‖y‖ ≤ dist y z + ‖z‖ := by
      simpa only [dist_zero_right] using dist_triangle y z 0
    have hyd : dist y z < r := hy
    gcongr
    linarith
  have hh := norm_iterated_steps n (show 0 < r / (n+1 : ℕ) by positivity)
    (show 0 ≤ C * Real.pi * (‖z‖ + r)^4 by positivity)
    (he.symm ▸ (complex_analytic D hR hC).mono hs) (he.symm ▸ hb)
  convert hh using 1
  congr 2
  field_simp

theorem complex_first_nonzero (hR : 0 < R) (hC : 0 ≤ C)
    {z : E} (hz : ‖z‖ < R/2) (hne : z ≠ 0) :
    ‖fderiv ℂ (complexPrimitive D) z‖ ≤ 64 * C * Real.pi * ‖z‖^3 := by
  have hh := cauchy_scaled D hR hC 1 (norm_pos_iff.mpr hne) (by linarith : ‖z‖ + ‖z‖ ≤ R)
  rw [norm_iteratedFDeriv_one] at hh
  convert hh using 1
  field_simp [norm_ne_zero_iff.mpr hne]
  ring

theorem complex_zero (hR : 0 < R) (hC : 0 ≤ C) : complexPrimitive D 0 = 0 := by
  apply norm_eq_zero.mp
  have hz : ‖complexPrimitive D (0 : E)‖ ≤ 0 := by
    simpa using complex_bound D hC (mem_ball_self hR)
  exact le_antisymm hz (norm_nonneg _)

/-- A fourth-order zero gives zero first differential; no continuity argument
through a nonzero coordinate stratum is needed at the origin. -/
theorem complex_first_zero (hR : 0 < R) (hC : 0 ≤ C) :
    fderiv ℂ (complexPrimitive D) 0 = 0 := by
  have hb : (complexPrimitive D) =O[𝓝 (0 : E)] (fun z => ‖z‖^4) := by
    apply IsBigO.of_bound (C * Real.pi)
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using complex_bound D hC hz
  have ho := hb.trans_isLittleO (isLittleO_norm_pow_id (E' := E) (by norm_num : 1 < 4))
  have hd : HasFDerivAt (complexPrimitive D) (0 : E →L[ℂ] ℂ) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simpa only [zero_add, complex_zero D hR hC, sub_zero, zero_apply] using ho
  exact hd.fderiv

theorem complex_first_bound (hR : 0 < R) (hC : 0 ≤ C)
    {z : E} (hz : ‖z‖ < R/2) :
    ‖fderiv ℂ (complexPrimitive D) z‖ ≤ 64 * C * Real.pi * ‖z‖^3 := by
  by_cases hn : z = 0
  · subst z; simp [complex_first_zero D hR hC]
  · exact complex_first_nonzero D hR hC hz hn

theorem complex_second_bound (hR : 0 < R) (hC : 0 ≤ C)
    {z : E} (hz : ‖z‖ < R/2) :
    ‖iteratedFDeriv ℂ 2 (complexPrimitive D) z‖ ≤ 576 * C * Real.pi * ‖z‖^2 := by
  by_cases hn : z = 0
  · subst z
    have hb : (fderiv ℂ (complexPrimitive D)) =O[𝓝 (0 : E)] (fun z => ‖z‖^3) := by
      apply IsBigO.of_bound (64 * C * Real.pi)
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by linarith : 0 < R/2))] with z hz
      simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using
        complex_first_bound D hR hC (mem_ball_zero_iff.mp hz)
    have ho := hb.trans_isLittleO (isLittleO_norm_pow_id (E' := E) (by norm_num : 1 < 3))
    have hd : HasFDerivAt (fderiv ℂ (complexPrimitive D)) (0 : E →L[ℂ] (E →L[ℂ] ℂ)) 0 := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      simpa only [zero_add, complex_first_zero D hR hC, sub_zero,
        zero_apply] using ho
    have he : ‖iteratedFDeriv ℂ 2 (complexPrimitive D) (0 : E)‖ = 0 := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, hd.fderiv, norm_zero]
    simp only [he, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · have hh := cauchy_scaled D hR hC 2 (norm_pos_iff.mpr hn) (by linarith : ‖z‖ + ‖z‖ ≤ R)
    convert hh using 1
    field_simp [norm_ne_zero_iff.mpr hn]
    ring

/-- Restriction to the physical Hilbert space cannot increase any full
multilinear derivative norm. -/
theorem physical_derivative_le (hR : 0 < R) (hC : 0 ≤ C)
    (n : ℕ) {z : H} (hz : z ∈ ball 0 R) :
    ‖iteratedFDeriv ℝ n (primitive β) z‖ ≤
      ‖iteratedFDeriv ℂ n (complexPrimitive D) (D.embed z)‖ := by
  let f := complexPrimitive D
  have ha : AnalyticOnNhd ℝ f (ball (0 : E) R) := (complex_analytic D hR hC).restrictScalars
  have hcd : ContDiffOn ℝ n f (ball (0 : E) R) := ha.contDiffOn_of_completeSpace
  have hp : D.embed ⁻¹' ball (0 : E) R = ball (0 : H) R := by
    ext w
    simp only [mem_preimage, mem_ball_zero_iff, D.embed_norm]
  have hzE : D.embed z ∈ ball (0 : E) R := by
    simpa only [mem_ball_zero_iff, D.embed_norm] using hz
  have he := D.embed.iteratedFDerivWithin_comp_right hcd isOpen_ball.uniqueDiffOn
    (hp.symm ▸ isOpen_ball.uniqueDiffOn) hzE (i := n) le_rfl
  rw [hp, iteratedFDerivWithin_of_isOpen n isOpen_ball hz,
    iteratedFDerivWithin_of_isOpen n isOpen_ball hzE] at he
  have hEmb : ‖D.embed‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by simp [D.embed_norm])
  have hRight : ‖iteratedFDeriv ℝ n (f ∘ D.embed) z‖ ≤ ‖iteratedFDeriv ℝ n f (D.embed z)‖ := by
    rw [he]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hn : ‖D.embed‖^n ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg D.embed) hEmb n
    exact mul_le_of_le_one_right (norm_nonneg _) hn
  have hlocal : primitive β =ᶠ[𝓝 z] Complex.reCLM ∘ (f ∘ D.embed) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    simp only [Function.comp_apply, f, complex_real D hw, Complex.reCLM_apply,
      Complex.ofReal_re]
  rw [(hlocal.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds]
  have hc : ContDiffAt ℝ n (f ∘ D.embed) z :=
    ((ha _ hzE).contDiffAt.comp z D.embed.contDiff.contDiffAt)
  have hl := Complex.reCLM.norm_iteratedFDeriv_comp_left hc (n := n) le_rfl
  have hRe : ‖Complex.reCLM‖ ≤ 1 := by
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm w
  have hTrans : ‖iteratedFDeriv ℝ n (Complex.reCLM ∘ (f ∘ D.embed)) z‖ ≤
      ‖iteratedFDeriv ℝ n f (D.embed z)‖ := by
    exact hl.trans ((mul_le_mul_of_nonneg_right hRe (norm_nonneg _)).trans (by simpa using hRight))
  have hcC : ContDiffAt ℂ n f (D.embed z) := (complex_analytic D hR hC _ hzE).contDiffAt
  rw [← hcC.restrictScalars_iteratedFDeriv (𝕜 := ℝ)] at hTrans
  simpa only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars] using hTrans

include D

theorem primitive_first_bound (hR : 0 < R) (hC : 0 ≤ C)
    {z : H} (hz : z ∈ ball 0 (R/2)) :
    ‖fderiv ℝ (primitive β) z‖ ≤ 64 * C * Real.pi * ‖z‖^3 := by
  have hzR : z ∈ ball (0 : H) R := (ball_subset_ball (by linarith : R/2 ≤ R)) hz
  have hh := physical_derivative_le D hR hC 1 hzR
  rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at hh
  exact hh.trans (by
    simpa only [D.embed_norm] using complex_first_bound D hR hC
      (show ‖D.embed z‖ < R/2 by simpa only [D.embed_norm] using mem_ball_zero_iff.mp hz))

theorem primitive_second_bound (hR : 0 < R) (hC : 0 ≤ C)
    {z : H} (hz : z ∈ ball 0 (R/2)) :
    ‖iteratedFDeriv ℝ 2 (primitive β) z‖ ≤ 576 * C * Real.pi * ‖z‖^2 := by
  have hzR : z ∈ ball (0 : H) R := (ball_subset_ball (by linarith : R/2 ≤ R)) hz
  exact (physical_derivative_le D hR hC 2 hzR).trans (by
    simpa only [D.embed_norm] using complex_second_bound D hR hC
      (show ‖D.embed z‖ < R/2 by simpa only [D.embed_norm] using mem_ball_zero_iff.mp hz))

end QuantumNLS.LOCAL017Haar
