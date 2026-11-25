import Mathlib
import NlsGge.ThirdConsultation.G2.G2037P5A

set_option autoImplicit false

open Set Filter Topology Metric Complex MeasureTheory
open scoped Real

namespace NlsGge.G2037P5
noncomputable section

/-- One factor `(λ - z) / ((τ - z) * sqrt (1 - (g/4)/(τ - z)^2))` equals `q (1/z)` for a function
`q` analytic at zero with `q 0 = 1`. This is the expansion of `stdRoot38` at infinity. -/
theorem factor_expansion (τ g lam : ℂ) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ q 0 = 1 ∧
      ∀ z : ℂ, z ≠ 0 → z ≠ τ →
        (lam - z) / ((τ - z) * Complex.sqrt (1 - (g / 4) / (τ - z) ^ 2)) = q z⁻¹ := by
  refine ⟨fun w => (lam * w - 1) / ((τ * w - 1) *
      Complex.sqrt (1 - (g / 4) * w ^ 2 / (τ * w - 1) ^ 2)), ?_, ?_, ?_⟩
  · have hL : AnalyticAt ℂ (fun w : ℂ => τ * w - 1) 0 :=
      (analyticAt_const.mul analyticAt_id).sub analyticAt_const
    have hτ0 : (τ * (0 : ℂ) - 1) ≠ 0 := by simp
    have hNum : AnalyticAt ℂ (fun w : ℂ => (g / 4) * w ^ 2) 0 :=
      analyticAt_const.mul (analyticAt_id.pow 2)
    have hDen : AnalyticAt ℂ (fun w : ℂ => (τ * w - 1) ^ 2) 0 := hL.pow 2
    have hX : AnalyticAt ℂ (fun w : ℂ => 1 - (g / 4) * w ^ 2 / (τ * w - 1) ^ 2) 0 :=
      analyticAt_const.sub (hNum.div hDen (pow_ne_zero 2 hτ0))
    have h1 : (1 : ℂ) - (g / 4) * (0 : ℂ) ^ 2 / (τ * 0 - 1) ^ 2 ∈ slitPlane := by
      simp [Complex.mem_slitPlane_iff]
    have hS : AnalyticAt ℂ (fun w : ℂ => Complex.sqrt (1 - (g / 4) * w ^ 2 / (τ * w - 1) ^ 2)) 0 :=
      AnalyticAt.cpow hX (analyticAt_const (v := (2⁻¹ : ℂ))) h1
    have hLnum : AnalyticAt ℂ (fun w : ℂ => lam * w - 1) 0 :=
      (analyticAt_const.mul analyticAt_id).sub analyticAt_const
    have hDenom0 : (τ * (0 : ℂ) - 1) *
        Complex.sqrt (1 - (g / 4) * (0 : ℂ) ^ 2 / (τ * 0 - 1) ^ 2) ≠ 0 := by
      simp [Complex.sqrt]
    exact hLnum.div (hL.mul hS) hDenom0
  · simp [Complex.sqrt]
  · intro z hz hzτ
    dsimp only
    have hτz : τ - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzτ)
    have e1 : lam - z = (lam * z⁻¹ - 1) * z := by
      rw [sub_mul, mul_assoc, inv_mul_cancel₀ hz]
      ring
    have e2 : τ - z = (τ * z⁻¹ - 1) * z := by
      rw [sub_mul, mul_assoc, inv_mul_cancel₀ hz]
      ring
    have hτw : τ * z⁻¹ - 1 ≠ 0 := by
      intro h
      apply hτz
      rw [e2, h, zero_mul]
    have e3 : (g / 4) / (τ - z) ^ 2 = (g / 4) * (z⁻¹) ^ 2 / (τ * z⁻¹ - 1) ^ 2 := by
      rw [e2]
      field_simp <;> ring
    rw [e3, e1, e2]
    set S := Complex.sqrt (1 - (g / 4) * z⁻¹ ^ 2 / (τ * z⁻¹ - 1) ^ 2) with hSdef
    rw [show ((τ * z⁻¹ - 1) * z) * S = ((τ * z⁻¹ - 1) * S) * z by ring]
    exact mul_div_mul_right _ _ hz

/-- Finite product of factors: `-I * ∏ (λ n - z)/(...)` equals `-I * Q (1/z)` for large `z`,
with `Q` analytic at zero and `Q 0 = 1`. -/
theorem product_expansion (S : Finset ℤ) (τ g lam : ℤ → ℂ) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ Q 0 = 1 ∧ ∃ R1 : ℝ, 0 < R1 ∧ ∀ z : ℂ, R1 < ‖z‖ →
      -I * ∏ n ∈ S, (lam n - z) / ((τ n - z) * Complex.sqrt (1 - (g n / 4) / (τ n - z) ^ 2))
        = -I * Q z⁻¹ := by
  choose q hqa hq0 hqid using fun n : ℤ => factor_expansion (τ n) (g n) (lam n)
  have hA : AnalyticAt ℂ (∏ n ∈ S, q n) 0 := Finset.analyticAt_prod S (fun n _ => hqa n)
  have hfun : (fun w : ℂ => ∏ n ∈ S, q n w) = ∏ n ∈ S, q n := by
    funext w
    simp [Finset.prod_apply]
  refine ⟨fun w => ∏ n ∈ S, q n w, ?_, ?_, 1 + ∑ n ∈ S, ‖τ n‖, by positivity, ?_⟩
  · rw [hfun]
    exact hA
  · simp [hq0]
  · intro z hz
    have hsum0 : 0 ≤ ∑ n ∈ S, ‖τ n‖ := Finset.sum_nonneg (fun n _ => norm_nonneg _)
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      linarith
    have hzτ : ∀ n ∈ S, z ≠ τ n := by
      intro n hn h
      have hle : ‖τ n‖ ≤ ∑ m ∈ S, ‖τ m‖ :=
        Finset.single_le_sum (fun m _ => norm_nonneg _) hn
      rw [← h] at hle
      linarith
    show -I * ∏ n ∈ S, (lam n - z) / ((τ n - z) * Complex.sqrt (1 - (g n / 4) / (τ n - z) ^ 2))
      = -I * ∏ n ∈ S, q n z⁻¹
    rw [Finset.prod_congr rfl (fun n hn => hqid n z hz0 (hzτ n hn))]

/-- **Conditional conjunct (5) of G2-037.** Given the finite-product differential `fgd`, a
primitive `F` of `fgd` on the complement of a closed bounded set `Cuts`, and the large-`z`
factorization `fgd z = -I * Q (1/z)` with `Q` analytic at zero and `Q 0 = 1`, the Laurent form
`f z = -I*z + g(1/z)` holds for `f = F`. No primitive is assumed beyond `hF`. -/
theorem conjunct5_of_primitive (fgd F : ℂ → ℂ) (Cuts : Set ℂ) {R0 : ℝ} (hR0 : 0 < R0)
    (hcut : Cuts ⊆ closedBall (0 : ℂ) R0) (hclosed : IsClosed Cuts)
    (hQ : ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ Q 0 = 1 ∧ ∃ R1 : ℝ, 0 < R1 ∧
      ∀ z : ℂ, R1 < ‖z‖ → fgd z = -I * Q z⁻¹)
    (hF : ∀ z : ℂ, z ∉ Cuts → HasDerivAt F (fgd z) z) :
    ∃ R : ℝ, 0 < R ∧ Cuts ⊆ closedBall (0 : ℂ) R ∧ ∃ f g : ℂ → ℂ,
      AnalyticOnNhd ℂ f Cutsᶜ ∧
      (∀ z : ℂ, z ∉ Cuts → HasDerivAt f (fgd z) z) ∧
      AnalyticAt ℂ g 0 ∧
      (∀ z : ℂ, R < ‖z‖ → f z = -I * z + g z⁻¹) := by
  obtain ⟨Q, hQa, hQ0, R1, hR1, hQid⟩ := hQ
  obtain ⟨r0, hr0, hanal⟩ := hQa.exists_ball_analyticOnNhd
  have hQd : DifferentiableOn ℂ Q (ball (0 : ℂ) r0) := hanal.differentiableOn
  have hRc : 0 < max R0 R1 := lt_of_lt_of_le hR0 (le_max_left _ _)
  have hFc : ∀ z : ℂ, max R0 R1 < ‖z‖ → HasDerivAt F (-I * Q z⁻¹) z := by
    intro z hz
    have hzc : z ∉ Cuts := fun h => by
      have h' := hcut h
      rw [mem_closedBall_zero_iff] at h'
      linarith [le_max_left R0 R1]
    have h2 := hF z hzc
    rw [hQid z (lt_of_le_of_lt (le_max_right R0 R1) hz)] at h2
    exact h2
  obtain ⟨g, hga, hgid⟩ := primitive_expansion_core F Q hRc hr0 hQd hQ0 hFc
  refine ⟨max R0 (1 / min r0 (1 / max R0 R1)), lt_of_lt_of_le hR0 (le_max_left _ _),
    hcut.trans (closedBall_subset_closedBall (le_max_left _ _)), F, g, ?_,
    fun z hz => hF z hz, hga,
    fun z hz => hgid z (lt_of_le_of_lt (le_max_right _ _) hz)⟩
  exact DifferentiableOn.analyticOnNhd
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt) hclosed.isOpen_compl

end

end NlsGge.G2037P5
