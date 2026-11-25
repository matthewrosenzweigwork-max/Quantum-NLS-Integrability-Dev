import NlsGge.GK38.PairAsymptoticsScalar

/-! # F5: discriminant derivative asymptotics by Cauchy's estimate (GK Theorem 2.2) -/

set_option autoImplicit false

open Filter Topology MeasureTheory Set Metric

namespace NlsGge.GK38

noncomputable section

theorem discrimDeriv_asymp (φ₀ : PotPair) : ∀ ε > 0, ∃ U ∈ 𝓝 φ₀, ∃ R : ℝ,
    ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖deriv (discrim φ) z - (-2 * Complex.sin z)‖ ≤ ε * Real.exp |z.im| := by
  intro ε hε
  let δ : ℝ := ε / Real.exp 1
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  obtain ⟨U, hU, R, hR⟩ := discrim_asymp φ₀ δ hδ
  refine ⟨U, hU, R + 1, fun φ hφ z hz => ?_⟩
  let F : ℂ → ℂ := fun w => discrim φ w - 2 * Complex.cos w
  have hd : Differentiable ℂ (discrim φ) :=
    fun w => (analyticOnNhd_discrim_z φ w (mem_univ w)).differentiableAt
  have hF : Differentiable ℂ F := hd.sub (by fun_prop)
  have hcircle : ∀ w ∈ sphere z 1, ‖F w‖ ≤ ε * Real.exp |z.im| := by
    intro w hw
    have hnorm : ‖w - z‖ = 1 := mem_sphere_iff_norm.mp hw
    have hwR : R ≤ ‖w‖ := by
      have hn := norm_sub_norm_le z w
      rw [norm_sub_rev, hnorm] at hn
      linarith
    have him : |w.im| ≤ |z.im| + 1 := by
      have hi := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, hnorm] at hi
      have ht := abs_add_le z.im (w.im - z.im)
      have heq : z.im + (w.im - z.im) = w.im := by ring
      rw [heq] at ht
      linarith
    have hb := hR φ hφ w hwR
    change ‖F w‖ ≤ δ * Real.exp |w.im| at hb
    refine hb.trans ?_
    calc δ * Real.exp |w.im| ≤ δ * Real.exp (|z.im| + 1) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr him) hδ.le
      _ = ε * Real.exp |z.im| := by
        rw [Real.exp_add]
        dsimp [δ]
        field_simp
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : 0 < (1 : ℝ)) hF.diffContOnCl hcircle
  have heq : deriv F z = deriv (discrim φ) z - (-2 * Complex.sin z) := by
    have hh := ((hd z).hasDerivAt.sub ((Complex.hasDerivAt_cos z).const_mul 2)).deriv
    convert hh using 1 <;> ring
  simpa only [heq, div_one] using hb

end

end NlsGge.GK38
