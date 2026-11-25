import QuantumNLS.ResetMoserMoserData

/-!
# `thm:reset-moser` (LOCAL-017), item 5a: the cut-off autonomous field `Fc` on `K × ℝ`

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "The nonautonomous integral equation for `Y_t` has a unique local solution
by the uniform derivative bound".  The nonautonomous field `(z, t) ↦ Y_t z` is the autonomous field `(z, t) ↦ (Y_t z, 1)` on `K × ℝ`.  To get a
*complete* flow, the field is multiplied by a smooth cutoff `χ(‖z‖²)` (`χ = 1` for `‖z‖ ≤ R0/4`, `χ = 0` for `‖z‖ ≥ R0/2`) and the time is clamped
(`sig`).  `Fc (z, s) = (χ(‖z‖²) Yf(sig s)(z), 1)`.

* `Fc_contDiff`: `Fc` is `C¹` on all of `K × ℝ`;
* `Fc_norm_le`: `Fc` is bounded;
* `Fc_lipschitz`: `Fc` is globally Lipschitz (bounded Fréchet derivative: `Fc_fderiv_bound`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal NNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp

namespace MoserData

variable {S : Hyp} (MD : MoserData S)

theorem cut_a_pos : 0 < (MD.R0 / 4) ^ 2 := by have := MD.R0_pos; positivity

theorem cut_ab : (MD.R0 / 4) ^ 2 < (MD.R0 / 2) ^ 2 := by have := MD.R0_pos; nlinarith

/-- The radial cutoff: `1` on `‖z‖ ≤ R0/4`, `0` on `‖z‖ ≥ R0/2`. -/
def cutF : ℝ → ℝ := cut ((MD.R0 / 4) ^ 2) ((MD.R0 / 2) ^ 2) MD.cut_a_pos MD.cut_ab

theorem cutF_contDiff : ContDiff ℝ 1 MD.cutF := cut_contDiff_one _ _ _ _

theorem cutF_one {w : K} (hw : ‖w‖ ≤ MD.R0 / 4) : MD.cutF (‖w‖ ^ 2) = 1 :=
  cut_one _ _ _ _ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hw 2)

theorem cutF_zero {w : K} (hw : MD.R0 / 2 ≤ ‖w‖) : MD.cutF (‖w‖ ^ 2) = 0 :=
  cut_zero _ _ _ _ (pow_le_pow_left₀ (by have := MD.R0_pos; positivity) hw 2)

theorem cutF_nonneg (x : ℝ) : 0 ≤ MD.cutF x := cut_nonneg _ _ _ _ x

theorem cutF_le_one (x : ℝ) : MD.cutF x ≤ 1 := cut_le_one _ _ _ _ x

theorem lt_of_cutF_ne {w : K} (h : MD.cutF (‖w‖ ^ 2) ≠ 0) : ‖w‖ < MD.R0 / 2 := by
  by_contra hc
  exact h (MD.cutF_zero (not_lt.mp hc))

theorem mem_ball_of_cutF_ne {w : K} (h : MD.cutF (‖w‖ ^ 2) ≠ 0) : w ∈ ball (0 : K) MD.R0 := by
  have := MD.lt_of_cutF_ne h
  have := MD.R0_pos
  rw [mem_ball_zero_iff]; linarith

/-- The autonomous cut-off field on `K × ℝ`. -/
def Fc (p : K × ℝ) : K × ℝ := (MD.cutF (‖p.1‖ ^ 2) • MD.Ghat p, 1)

theorem Fc_fst (p : K × ℝ) : (MD.Fc p).1 = MD.cutF (‖p.1‖ ^ 2) • MD.Ghat p := rfl

theorem Fc_snd (p : K × ℝ) : (MD.Fc p).2 = 1 := rfl

theorem Fc_eq_of_small {p : K × ℝ} (hp : ‖p.1‖ ≤ MD.R0 / 4) : MD.Fc p = (MD.Ghat p, 1) := by
  simp [Fc, MD.cutF_one hp]

theorem Fc_eq_of_large {p : K × ℝ} (hp : MD.R0 / 2 ≤ ‖p.1‖) : MD.Fc p = (0, 1) := by
  simp [Fc, MD.cutF_zero hp]

theorem Fc_contDiff : ContDiff ℝ 1 MD.Fc := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : ‖p.1‖ < MD.R0
  · have hG := MD.Ghat_contDiffAt (p := p) (by simpa using hp)
    have hn : ContDiffAt ℝ 1 (fun q : K × ℝ => ‖q.1‖ ^ 2) p :=
      ContDiffAt.comp p (contDiff_norm_sq ℝ).contDiffAt contDiffAt_fst
    have hχ : ContDiffAt ℝ 1 (fun q : K × ℝ => MD.cutF (‖q.1‖ ^ 2)) p :=
      ContDiffAt.comp p MD.cutF_contDiff.contDiffAt hn
    exact (hχ.smul hG).prodMk contDiffAt_const
  · have hp' : MD.R0 / 2 < ‖p.1‖ := by have := MD.R0_pos; linarith [not_lt.mp hp]
    have hev : MD.Fc =ᶠ[𝓝 p] fun _ => ((0 : K), (1 : ℝ)) := by
      filter_upwards [(continuous_norm.comp continuous_fst).continuousAt.eventually
        (lt_mem_nhds hp')] with q hq
      exact MD.Fc_eq_of_large hq.le
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem Fc_norm_le (p : K × ℝ) : ‖MD.Fc p‖ ≤ MD.B * MD.R0 ^ 3 + 1 := by
  have hB := MD.B_nonneg
  have hR := MD.R0_pos
  have h1 : ‖MD.cutF (‖p.1‖ ^ 2) • MD.Ghat p‖ ≤ MD.B * MD.R0 ^ 3 := by
    by_cases h0 : MD.cutF (‖p.1‖ ^ 2) = 0
    · rw [h0, zero_smul, norm_zero]; positivity
    · have hp := MD.mem_ball_of_cutF_ne h0
      have hn := mem_ball_zero_iff.1 hp
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (MD.cutF_nonneg _)]
      calc MD.cutF (‖p.1‖ ^ 2) * ‖MD.Ghat p‖ ≤ 1 * (MD.B * ‖p.1‖ ^ 3) :=
            mul_le_mul (MD.cutF_le_one _) (MD.norm_Ghat_le hp) (norm_nonneg _) zero_le_one
        _ ≤ MD.B * MD.R0 ^ 3 := by
            rw [one_mul]
            gcongr
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · exact h1.trans (by linarith)
  · simp [Fc]; positivity

/-- A uniform bound on the Fréchet derivative of `Fc` over all of `K × ℝ`. -/
theorem Fc_fderiv_bound : ∃ Lf : ℝ, ∀ p : K × ℝ, ‖fderiv ℝ MD.Fc p‖ ≤ Lf := by
  obtain ⟨cσ, hcσ⟩ := exists_deriv_sig_bound
  obtain ⟨cχ, hcχ⟩ := exists_deriv_cut_bound _ _ MD.cut_a_pos MD.cut_ab
  have hB := MD.B_nonneg
  have hM := MD.M_nonneg
  have hR := MD.R0_pos
  have hcσ0 : 0 ≤ cσ := (norm_nonneg _).trans (hcσ 0)
  have hcχ0 : 0 ≤ cχ := (norm_nonneg _).trans (hcχ 0)
  refine ⟨((3 / 2 * (MD.M * MD.R0) + cσ * (MD.M * MD.R0 ^ 2)) * (MD.B * MD.R0 ^ 3) + MD.B * MD.R0 ^ 2)
    + cχ * (2 * MD.R0) * (MD.B * MD.R0 ^ 3), fun p => ?_⟩
  by_cases hp : ‖p.1‖ < MD.R0
  · obtain ⟨L, hL, hLn⟩ := MD.Ghat_deriv hcσ (p := p) (mem_ball_zero_iff.2 hp)
    have hn : HasFDerivAt (fun q : K × ℝ => ‖q.1‖ ^ 2)
        (2 • (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ K ℝ)) p :=
      (hasFDerivAt_fst (p := p)).norm_sq
    have hχ := ((MD.cutF_contDiff).differentiable one_ne_zero (‖p.1‖ ^ 2)).hasDerivAt.comp_hasFDerivAt p hn
    have hsm := hχ.smul hL
    have hF := hsm.prodMk (hasFDerivAt_const (1 : ℝ) p)
    have hF' : HasFDerivAt MD.Fc _ p := hF
    rw [hF'.fderiv]
    set c' : K × ℝ →L[ℝ] ℝ := (deriv MD.cutF (‖p.1‖ ^ 2)) • (2 • (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ K ℝ)) with hc'
    set A : K × ℝ →L[ℝ] K := (MD.cutF (‖p.1‖ ^ 2)) • L + c'.smulRight (MD.Ghat p) with hA
    have hAn : ‖A‖ ≤ ((3 / 2 * (MD.M * MD.R0) + cσ * (MD.M * MD.R0 ^ 2)) * (MD.B * MD.R0 ^ 3) + MD.B * MD.R0 ^ 2)
        + cχ * (2 * MD.R0) * (MD.B * MD.R0 ^ 3) := by
      have hpn := norm_nonneg p.1
      have hL1 : ‖L‖ ≤ (3 / 2 * (MD.M * MD.R0) + cσ * (MD.M * MD.R0 ^ 2)) * (MD.B * MD.R0 ^ 3) + MD.B * MD.R0 ^ 2 := by
        refine hLn.trans ?_
        have h1 : ‖p.1‖ ≤ MD.R0 := hp.le
        gcongr
      have hc'n : ‖c'‖ ≤ cχ * (2 * MD.R0) := by
        have h2 : ‖(2 : ℕ) • (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ K ℝ)‖ ≤ 2 * ‖p.1‖ := by
          have h3 : ‖(innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ K ℝ)‖ ≤ ‖p.1‖ := by
            refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
            have h5 : ‖((innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ K ℝ)) v‖ = |innerSL ℝ p.1 v.1| := by
              rw [Real.norm_eq_abs]; rfl
            rw [h5]
            calc |innerSL ℝ p.1 v.1| ≤ ‖p.1‖ * ‖v.1‖ := by
                  rw [innerSL_apply_apply]
                  exact abs_real_inner_le_norm p.1 v.1
              _ ≤ ‖p.1‖ * ‖v‖ := mul_le_mul_of_nonneg_left
                  (by rw [Prod.norm_def]; exact le_max_left _ _) (norm_nonneg _)
          have h4 := norm_nsmul_le (n := 2) (a := (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ K ℝ))
          push_cast at h4
          linarith
        rw [hc', norm_smul]
        calc ‖deriv MD.cutF (‖p.1‖ ^ 2)‖ * ‖(2 : ℕ) • (innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ K ℝ)‖
            ≤ cχ * (2 * ‖p.1‖) := mul_le_mul (hcχ _) h2 (norm_nonneg _) hcχ0
          _ ≤ cχ * (2 * MD.R0) := by gcongr
      have hG : ‖MD.Ghat p‖ ≤ MD.B * MD.R0 ^ 3 :=
        (MD.norm_Ghat_le (mem_ball_zero_iff.2 hp)).trans (by gcongr)
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (MD.cutF_nonneg _)]
        calc MD.cutF (‖p.1‖ ^ 2) * ‖L‖ ≤ 1 * ‖L‖ :=
              mul_le_mul_of_nonneg_right (MD.cutF_le_one _) (norm_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hL1
      · rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul hc'n hG (norm_nonneg _) (by positivity)
    refine le_trans ?_ hAn
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (fun h => ?_)
    simp only [ContinuousLinearMap.prod_apply, Prod.norm_def, ContinuousLinearMap.zero_apply, norm_zero]
    rw [max_eq_left (norm_nonneg _)]
    exact A.le_opNorm h
  · have hp' : MD.R0 / 2 < ‖p.1‖ := by linarith [not_lt.mp hp]
    have hev : MD.Fc =ᶠ[𝓝 p] fun _ => ((0 : K), (1 : ℝ)) := by
      filter_upwards [(continuous_norm.comp continuous_fst).continuousAt.eventually
        (lt_mem_nhds hp')] with q hq
      exact MD.Fc_eq_of_large hq.le
    rw [hev.fderiv_eq, (hasFDerivAt_const ((0 : K), (1 : ℝ)) p).fderiv]
    simp only [norm_zero]
    positivity

theorem Fc_lipschitz : ∃ Kc : ℝ≥0, LipschitzWith Kc MD.Fc := by
  obtain ⟨Lf, hLf⟩ := MD.Fc_fderiv_bound
  refine ⟨Real.toNNReal Lf, lipschitzWith_of_nnnorm_fderiv_le
    (MD.Fc_contDiff.differentiable one_ne_zero) (fun x => ?_)⟩
  exact (NNReal.coe_le_coe).1 (by simpa using (hLf x).trans (le_max_left Lf 0))

end MoserData

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.MoserData.Fc_contDiff
#print axioms QuantumNLS.ResetMoser.MoserData.Fc_norm_le
#print axioms QuantumNLS.ResetMoser.MoserData.Fc_lipschitz
