import NlsGge.NLS38.NonlinCarrier38
import NlsGge.NLS38.SolutionNotion38a

/-! # GWP piece A5a: the cutoff nonlinearity is globally Lipschitz and bounded

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A5a.  The cutoff `χ_R(r) = max 0 (min 1 (2 - r/R))`
(`1` for `r ≤ R`, `0` for `r ≥ 2R`, `1/R`-Lipschitz) turns the locally Lipschitz nonlinearity `N` on
`h^1` into the bounded, globally Lipschitz field `v ↦ χ_R(‖v‖) N(v)`.

The generic part (an arbitrary cutoff profile `χ`, an arbitrary normed space and an arbitrary map
`N` that is Lipschitz and bounded on a ball) does not depend on A4.  The specialisation uses only the
definitions `cutoff`, `Gc` of `SolutionNotion38a` (A4); nothing of A4 is redefined here.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped NNReal

/-! ## Generic cutoff lemma -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One-sided case: `x` in the ball, `y` outside (so the cutoff kills `y`). -/
theorem cut_sub_le_of_out (χ : ℝ → ℝ) (N : E → E) {ρ L B : ℝ}
    (hχL : ∀ r s, |χ r - χ s| ≤ L * |r - s|)
    (hχz : ∀ r, ρ < r → χ r = 0) (hL : 0 ≤ L)
    (hB : ∀ x ∈ Metric.closedBall (0 : E) ρ, ‖N x‖ ≤ B) {x y : E}
    (hx : x ∈ Metric.closedBall (0 : E) ρ) (hy : y ∉ Metric.closedBall (0 : E) ρ) :
    ‖χ ‖x‖ • N x - χ ‖y‖ • N y‖ ≤ L * B * ‖x - y‖ := by
  have hyr : ρ < ‖y‖ := by
    by_contra h
    exact hy (by simpa using not_lt.1 h)
  have hy0 : χ ‖y‖ = 0 := hχz _ hyr
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x hx)
  have h1 : |χ ‖x‖| ≤ L * ‖x - y‖ := by
    have := hχL ‖x‖ ‖y‖
    rw [hy0, sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
    exact (abs_norm_sub_norm_le x y)
  rw [hy0, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs]
  calc |χ ‖x‖| * ‖N x‖ ≤ (L * ‖x - y‖) * B :=
        mul_le_mul h1 (hB x hx) (norm_nonneg _) (by positivity)
    _ = L * B * ‖x - y‖ := by ring

/-- Global Lipschitz estimate for `x ↦ χ ‖x‖ • N x`, `N` Lipschitz and bounded on the ball `ρ`. -/
theorem cut_lipschitz_aux (χ : ℝ → ℝ) (N : E → E) {ρ L K B : ℝ}
    (hχ0 : ∀ r, 0 ≤ χ r) (hχ1 : ∀ r, χ r ≤ 1) (hχL : ∀ r s, |χ r - χ s| ≤ L * |r - s|)
    (hχz : ∀ r, ρ < r → χ r = 0) (hL : 0 ≤ L) (hK : 0 ≤ K) (hB0 : 0 ≤ B)
    (hN : ∀ x ∈ Metric.closedBall (0 : E) ρ, ∀ y ∈ Metric.closedBall (0 : E) ρ,
      ‖N x - N y‖ ≤ K * ‖x - y‖)
    (hB : ∀ x ∈ Metric.closedBall (0 : E) ρ, ‖N x‖ ≤ B) (x y : E) :
    ‖χ ‖x‖ • N x - χ ‖y‖ • N y‖ ≤ (L * B + K) * ‖x - y‖ := by
  by_cases hx : x ∈ Metric.closedBall (0 : E) ρ <;> by_cases hy : y ∈ Metric.closedBall (0 : E) ρ
  · have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x hx)
    have e : χ ‖x‖ • N x - χ ‖y‖ • N y = (χ ‖x‖ - χ ‖y‖) • N x + χ ‖y‖ • (N x - N y) := by
      rw [sub_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hχ0 ‖y‖)]
    have h1 : |χ ‖x‖ - χ ‖y‖| ≤ L * ‖x - y‖ :=
      (hχL _ _).trans (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) hL)
    have h2 : χ ‖y‖ * ‖N x - N y‖ ≤ K * ‖x - y‖ :=
      (mul_le_mul (hχ1 _) (hN x hx y hy) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
    have h3 : |χ ‖x‖ - χ ‖y‖| * ‖N x‖ ≤ (L * ‖x - y‖) * B :=
      mul_le_mul h1 (hB x hx) (norm_nonneg _) (by positivity)
    nlinarith
  · have := cut_sub_le_of_out χ N hχL hχz hL hB hx hy
    nlinarith [mul_nonneg hK (norm_nonneg (x - y)), mul_nonneg hK (norm_nonneg (y - x))]
  · have := cut_sub_le_of_out χ N hχL hχz hL hB hy hx
    rw [norm_sub_rev (χ ‖x‖ • N x), norm_sub_rev x y]
    nlinarith [mul_nonneg hK (norm_nonneg (x - y)), mul_nonneg hK (norm_nonneg (y - x))]
  · have hxr : ρ < ‖x‖ := by
      by_contra h
      exact hx (by simpa using not_lt.1 h)
    have hyr : ρ < ‖y‖ := by
      by_contra h
      exact hy (by simpa using not_lt.1 h)
    rw [hχz _ hxr, hχz _ hyr]
    simp only [zero_smul, sub_self, norm_zero]
    positivity

end Generic

/-! ## The profile `cutoff R` -/

theorem cutoff_nonneg (R r : ℝ) : 0 ≤ cutoff R r := le_max_left _ _

theorem cutoff_le_one (R r : ℝ) : cutoff R r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem cutoff_lip {R : ℝ} (hR : 0 < R) (r s : ℝ) :
    |cutoff R r - cutoff R s| ≤ R⁻¹ * |r - s| := by
  unfold cutoff
  have h1 : |max 0 (min 1 (2 - r / R)) - max 0 (min 1 (2 - s / R))| ≤
      |min 1 (2 - r / R) - min 1 (2 - s / R)| := by
    have := abs_max_sub_max_le_max 0 (min 1 (2 - r / R)) 0 (min 1 (2 - s / R))
    simpa using this
  have h2 : |min 1 (2 - r / R) - min 1 (2 - s / R)| ≤ |(2 - r / R) - (2 - s / R)| := by
    have := abs_min_sub_min_le_max 1 (2 - r / R) 1 (2 - s / R)
    simpa using this
  have h3 : |(2 - r / R) - (2 - s / R)| = R⁻¹ * |r - s| := by
    have : (2 - r / R) - (2 - s / R) = -(R⁻¹ * (r - s)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_pos (inv_pos.2 hR)]
  exact h1.trans (h2.trans h3.le)

theorem cutoff_eq_zero {R r : ℝ} (hR : 0 < R) (hr : 2 * R ≤ r) : cutoff R r = 0 := by
  unfold cutoff
  have h : 2 - r / R ≤ 0 := by
    have : 2 ≤ r / R := (le_div_iff₀ hR).2 (by linarith)
    linarith
  rw [min_eq_right (h.trans zero_le_one), max_eq_left h]

/-! ## The cutoff nonlinearity on `h^1` -/

/-- `v ↦ χ_R(‖v‖_{h¹}) N(v)` is globally Lipschitz on `h¹`. -/
theorem cutNonlin_lipschitz (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun v : SobolevCarrier38 ((1 : ℕ) : ℝ) => cutoff R ‖v‖ • nonlinC 1 le_rfl v) := by
  obtain ⟨K, hK⟩ := nonlinC_lipschitzOn 1 le_rfl (2 * R)
  obtain ⟨B, hB⟩ := nonlinC_bounded 1 le_rfl (2 * R)
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hBm : ∀ x ∈ Metric.closedBall (0 : SobolevCarrier38 ((1 : ℕ) : ℝ)) (2 * R),
      ‖nonlinC 1 le_rfl x‖ ≤ max B 0 := fun x hx => (hB x hx).trans (le_max_left _ _)
  refine ⟨(R⁻¹ * max B 0 + K).toNNReal, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hKn : 0 ≤ (K : ℝ) := K.2
  have hnn : 0 ≤ R⁻¹ * max B 0 + K := by positivity
  rw [Real.coe_toNNReal _ hnn, dist_eq_norm, dist_eq_norm]
  exact cut_lipschitz_aux (cutoff R) (nonlinC 1 le_rfl) (cutoff_nonneg R) (cutoff_le_one R)
    (cutoff_lip hR) (fun r (hr : 2 * R < r) => cutoff_eq_zero hR hr.le) (by positivity) hKn hB0
    (fun x hx y hy => by
      have := hK.dist_le_mul x hx y hy
      rwa [dist_eq_norm, dist_eq_norm] at this)
    hBm x y

/-- The cutoff nonlinearity is bounded on `h¹`. -/
theorem cutNonlin_bounded (R : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, ∀ v : SobolevCarrier38 ((1 : ℕ) : ℝ), ‖cutoff R ‖v‖ • nonlinC 1 le_rfl v‖ ≤ B := by
  obtain ⟨B, hB⟩ := nonlinC_bounded 1 le_rfl (2 * R)
  refine ⟨max B 0, fun v => ?_⟩
  by_cases hv : ‖v‖ ≤ 2 * R
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg R _)]
    have h1 : ‖nonlinC 1 le_rfl v‖ ≤ max B 0 :=
      (hB v (by simpa using hv)).trans (le_max_left _ _)
    calc cutoff R ‖v‖ * ‖nonlinC 1 le_rfl v‖ ≤ 1 * max B 0 :=
          mul_le_mul (cutoff_le_one R _) h1 (norm_nonneg _) zero_le_one
      _ = max B 0 := one_mul _
  · rw [cutoff_eq_zero hR (not_le.1 hv).le, zero_smul, norm_zero]
    exact le_max_right _ _

/-! ## The interaction-picture field `Gc` at `m = 1` -/

/-- At `m = 1` the inclusion `h¹ → h¹` of the cutoff argument is the identity. -/
theorem carrierIncl38_one_eq (h : ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ))
    (v : SobolevCarrier38 ((1 : ℕ) : ℝ)) : carrierIncl38 h v = v :=
  carrierExt38 (carrierCoe38_incl38 h v)

/-- `Gc 1 R t` is the cutoff nonlinearity conjugated by the isometries `phaseC` and `J38`. -/
theorem Gc_one_eq (R t : ℝ) (v : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    Gc 1 le_rfl R t v = phaseC ((1 : ℕ) : ℝ) (-t) (-(J38 ((1 : ℕ) : ℝ)
      ((fun w : SobolevCarrier38 ((1 : ℕ) : ℝ) => cutoff R ‖w‖ • nonlinC 1 le_rfl w)
        (phaseC ((1 : ℕ) : ℝ) t v)))) := by
  unfold Gc
  rw [carrierIncl38_one_eq, ← norm_phaseC ((1 : ℕ) : ℝ) t v]

theorem norm_Gc_one_sub (R t : ℝ) (v w : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    ‖Gc 1 le_rfl R t v - Gc 1 le_rfl R t w‖ =
      ‖(fun x : SobolevCarrier38 ((1 : ℕ) : ℝ) => cutoff R ‖x‖ • nonlinC 1 le_rfl x)
          (phaseC ((1 : ℕ) : ℝ) t v) -
        (fun x : SobolevCarrier38 ((1 : ℕ) : ℝ) => cutoff R ‖x‖ • nonlinC 1 le_rfl x)
          (phaseC ((1 : ℕ) : ℝ) t w)‖ := by
  rw [Gc_one_eq, Gc_one_eq, ← map_sub, norm_phaseC, neg_sub_neg, norm_sub_rev, ← map_sub, norm_J38]

/-- `Gc 1 R` is bounded and globally Lipschitz in `v`, uniformly in `t`. -/
theorem Gc_lipschitz (R : ℝ) (hR : 0 < R) :
    (∃ K : ℝ≥0, ∀ t, LipschitzWith K (Gc 1 le_rfl R t)) ∧
      ∃ B : ℝ, ∀ t v, ‖Gc 1 le_rfl R t v‖ ≤ B := by
  obtain ⟨K, hK⟩ := cutNonlin_lipschitz R hR
  obtain ⟨B, hB⟩ := cutNonlin_bounded R hR
  refine ⟨⟨K, fun t => LipschitzWith.of_dist_le_mul fun v w => ?_⟩, B, fun t v => ?_⟩
  · rw [dist_eq_norm, dist_eq_norm, norm_Gc_one_sub]
    have := hK.dist_le_mul (phaseC ((1 : ℕ) : ℝ) t v) (phaseC ((1 : ℕ) : ℝ) t w)
    have e : phaseC ((1 : ℕ) : ℝ) t v - phaseC ((1 : ℕ) : ℝ) t w =
        phaseC ((1 : ℕ) : ℝ) t (v - w) := (map_sub _ _ _).symm
    rw [dist_eq_norm, dist_eq_norm, e, norm_phaseC ((1 : ℕ) : ℝ) t (v - w)] at this
    exact this
  · rw [Gc_one_eq, norm_phaseC, norm_neg, norm_J38]
    exact hB _

/-! ## Probes -/

/-- Below the radius `R` the cutoff is inactive. -/
theorem cutNonlin_eq_of_norm_le {R : ℝ} (hR : 0 < R) (v : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hv : ‖v‖ ≤ R) : cutoff R ‖v‖ • nonlinC 1 le_rfl v = nonlinC 1 le_rfl v := by
  rw [cutoff_eq_one hR hv, one_smul]

/-- Beyond the radius `2R` the cutoff field vanishes. -/
theorem cutNonlin_eq_zero_of_two_mul_le {R : ℝ} (hR : 0 < R) (v : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hv : 2 * R ≤ ‖v‖) : cutoff R ‖v‖ • nonlinC 1 le_rfl v = 0 := by
  rw [cutoff_eq_zero hR hv, zero_smul]

/-- The origin is a rest point of the cutoff field. -/
theorem Gc_one_zero (R t : ℝ) : Gc 1 le_rfl R t 0 = 0 := by
  rw [Gc_one_eq]
  simp [nonlinC_zero]

end NlsGge.NLS38
