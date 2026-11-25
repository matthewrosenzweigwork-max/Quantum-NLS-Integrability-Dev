import QuantumNLS.ResetMoserInst
import QuantumNLS.ResetMoserHyp

/-!
# `thm:reset-moser` (LOCAL-017), stage 4a: the uniform analytic bounds near zero, and conservation of the norm

Source: `symplectic_correction.tex`, proof of `thm:reset-moser`, first paragraph: "Real analyticity at zero in the operator-valued
sense gives ... Shrinking that ball gives uniform bounds ... Since its terms of degrees zero and one vanish for `Ω − ω`, we may use
`‖Ω_z − ω‖ ≤ C‖z‖²`, `‖DΩ_z‖ ≤ C‖z‖`, `‖D²Ω_z‖ ≤ C` (eq:reset-moser-form-bounds)" (here for the real ball, from the real analytic
(`C²`) structure of `Ω` at `0`, DEF-017 via `analyticAt_of_isRealAnalyticPoly`), and "Summing these exact equalities gives
conservation of `‖z‖²`; no differentiation of an infinite sum is needed" (here for the flows `φ_j`).

* `local_bounds`: `∃ ρ ≤ R, M`, on `B_ρ`: `‖Ω_z − ω‖ ≤ M‖z‖²`, `‖DΩ_z‖ ≤ M‖z‖`, `‖D²Ω_z‖ ≤ M`;
* `tsum_norm_sq`, `Hyp.norm_flow`: `‖φ_j^t z‖ = ‖z‖` (sum of the conserved `q_k`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef

instance instForm2NormedAddCommGroup : NormedAddCommGroup (K →L[ℝ] Form) :=
  ContinuousLinearMap.toNormedAddCommGroup
instance instForm2NormedSpace : NormedSpace ℝ (K →L[ℝ] Form) := ContinuousLinearMap.toNormedSpace

theorem tsum_norm_sq (w : K) : ‖w‖ ^ 2 = ∑' n, ‖w n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) w
  simpa [ENNReal.toReal_ofNat] using h

theorem Hyp.norm_flow (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) (j : ℤ) (t : ℝ) :
    ‖S.φ j t z‖ = ‖z‖ := by
  have h : ‖S.φ j t z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [tsum_norm_sq, tsum_norm_sq]
    congr 1
    funext n
    exact S.flow_q hz n j t
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem Hyp.Ω_contDiffAt (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) : ContDiffAt ℝ 2 S.Ω z :=
  (analyticAt_of_isRealAnalyticPoly (S.Ω_analytic z hz)).contDiffAt

theorem Hyp.fderiv_Ω_zero (S : Hyp) : fderiv ℝ S.Ω 0 = 0 := by
  obtain ⟨C, hC⟩ := S.Ω_quad
  have h0 : S.Ω 0 = omegaF := by
    have := hC 0 (mem_ball_self S.R_pos)
    simp at this
    exact sub_eq_zero.1 this
  have hd : HasFDerivAt S.Ω (0 : K →L[ℝ] Form) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    have hδ : 0 < min S.R (c / (|C| + 1)) := lt_min S.R_pos (by positivity)
    filter_upwards [ball_mem_nhds (0 : K) hδ] with h hh
    rw [mem_ball_zero_iff] at hh
    have hhR : ‖h‖ < S.R := lt_of_lt_of_le hh (min_le_left _ _)
    have hhc : ‖h‖ < c / (|C| + 1) := lt_of_lt_of_le hh (min_le_right _ _)
    have h1 := hC h (by rwa [mem_ball_zero_iff])
    simp only [zero_add, h0, ContinuousLinearMap.zero_apply, sub_zero, id_eq]
    have hC1 : C * ‖h‖ ^ 2 ≤ (|C| + 1) * ‖h‖ * ‖h‖ := by
      have : C ≤ |C| + 1 := by linarith [le_abs_self C]
      nlinarith [norm_nonneg h, mul_nonneg (norm_nonneg h) (norm_nonneg h)]
    have hc1 : (|C| + 1) * ‖h‖ ≤ c := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |C| + 1)).1 hhc
      linarith
    calc ‖S.Ω h - omegaF‖ ≤ C * ‖h‖ ^ 2 := h1
      _ ≤ (|C| + 1) * ‖h‖ * ‖h‖ := hC1
      _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg h)
  exact hd.fderiv

/-- **eq:reset-moser-form-bounds** on a small real ball. -/
theorem Hyp.local_bounds (S : Hyp) :
    ∃ ρ M : ℝ, 0 < ρ ∧ ρ ≤ S.R ∧ 0 ≤ M ∧ ∀ z ∈ ball (0 : K) ρ,
      ‖S.Ω z - omegaF‖ ≤ M * ‖z‖ ^ 2 ∧ ‖fderiv ℝ S.Ω z‖ ≤ M * ‖z‖ ∧
        ‖fderiv ℝ (fderiv ℝ S.Ω) z‖ ≤ M := by
  obtain ⟨C, hC⟩ := S.Ω_quad
  have h0 : (0 : K) ∈ ball (0 : K) S.R := mem_ball_self S.R_pos
  have hc2 : ContDiffAt ℝ 2 S.Ω 0 := S.Ω_contDiffAt h0
  have hc1 : ContDiffAt ℝ 1 (fderiv ℝ S.Ω) 0 := hc2.fderiv_right (m := 1) (by norm_num)
  have hc0 : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ S.Ω)) 0 := hc1.fderiv_right (m := 0) (by norm_num)
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ S.Ω)) 0 := hc0.continuousAt
  obtain ⟨ρ1, hρ1, hb1⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  set M0 : ℝ := ‖fderiv ℝ (fderiv ℝ S.Ω) 0‖ + 1 with hM0
  set ρ : ℝ := min S.R ρ1 with hρ
  have hρ0 : 0 < ρ := lt_min S.R_pos hρ1
  have hD2 : ∀ z ∈ ball (0 : K) ρ, ‖fderiv ℝ (fderiv ℝ S.Ω) z‖ ≤ M0 := by
    intro z hz
    have hz1 : dist z 0 < ρ1 := by
      rw [mem_ball] at hz; exact lt_of_lt_of_le hz (min_le_right _ _)
    have := hb1 hz1
    rw [dist_eq_norm] at this
    have := norm_sub_norm_le (fderiv ℝ (fderiv ℝ S.Ω) z) (fderiv ℝ (fderiv ℝ S.Ω) 0)
    linarith
  have hdiff : ∀ z ∈ ball (0 : K) ρ, HasFDerivAt (fderiv ℝ S.Ω) (fderiv ℝ (fderiv ℝ S.Ω) z) z := by
    intro z hz
    have hzR : z ∈ ball (0 : K) S.R := by
      rw [mem_ball] at hz ⊢; exact lt_of_lt_of_le hz (min_le_left _ _)
    have hz1 : ContDiffAt ℝ 1 (fderiv ℝ S.Ω) z := (S.Ω_contDiffAt hzR).fderiv_right (m := 1) (by norm_num)
    exact (hz1.differentiableAt one_ne_zero).hasFDerivAt
  refine ⟨ρ, max C M0, hρ0, min_le_left _ _, le_max_of_le_right (by positivity), fun z hz => ⟨?_, ?_, ?_⟩⟩
  · have hzR : z ∈ ball (0 : K) S.R := by
      rw [mem_ball] at hz ⊢; exact lt_of_lt_of_le hz (min_le_left _ _)
    exact (hC z hzR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ S.Ω) (s := ball (0 : K) ρ)
      (C := M0) (fun x hx => (hdiff x hx).differentiableAt)
      (fun x hx => by rw [(hdiff x hx).fderiv]; exact hD2 x hx) (convex_ball _ _)
      (mem_ball_self hρ0) hz
    rw [S.fderiv_Ω_zero, sub_zero, sub_zero] at hmv
    exact hmv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · exact (hD2 z hz).trans (le_max_right _ _)

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.tsum_norm_sq
#print axioms QuantumNLS.ResetMoser.Hyp.norm_flow
#print axioms QuantumNLS.ResetMoser.Hyp.fderiv_Ω_zero
#print axioms QuantumNLS.ResetMoser.Hyp.local_bounds
