import NlsGge.GK38.XiSqConvolutionUniform

set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

theorem a5QCorrectionProduct_linear_bound38 (n : ℤ) (p : PotPair × ℂ)
    (hW : p.1 ∈ gkW) (c : ℝ) (hc : 0 < c)
    (hsep : ∀ j : ℤ, j ≠ n → c⁻¹ * |(j : ℝ) - n| ≤ ‖tauN p.1 j - p.2‖)
    (B : ℝ) (hconv : a5GammaConvolution38 p.1 n ≤ B) :
    ‖a5QCorrectionProduct38 n p - 1‖ ≤
      ((c^2/4) * Real.exp ((c^2/4) * B)) * a5GammaConvolution38 p.1 n := by
  have hC : 0 ≤ c^2/4 := by positivity
  have hd : 0 ≤ a5GammaConvolution38 p.1 n := Lib.c3B_nonneg _ _ _ _
  have h := (a5QCorrectionProduct_converges_bound38 n p hW c hc hsep).2
  calc
    _ ≤ Real.exp ((c^2/4) * a5GammaConvolution38 p.1 n) - 1 := h
    _ ≤ ((c^2/4) * a5GammaConvolution38 p.1 n) *
        Real.exp ((c^2/4) * a5GammaConvolution38 p.1 n) := Lib.exp_sub_one_le_mul_exp _
    _ ≤ ((c^2/4) * a5GammaConvolution38 p.1 n) * Real.exp ((c^2/4) * B) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hconv hC))
        (mul_nonneg hC hd)
    _ = _ := by ring

/-- Scalar quotient bound after a genuine positive denominator estimate. -/
theorem a5RatioDiv_error_le38 (R P : ℂ) (b e : ℝ)
    (hR : ‖R-1‖ ≤ b) (hP : ‖P-1‖ ≤ e) (hden : (1/2:ℝ) ≤ ‖P‖) :
    ‖R/P-1‖ ≤ 2*b + 2*e := by
  have hPne : P ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hden)
  have heq : R/P-1 = ((R-1)-(P-1))/P := by field_simp; ring
  rw [heq, Complex.norm_div]
  have hnum : ‖(R-1)-(P-1)‖ ≤ b+e :=
    (norm_sub_le _ _).trans (add_le_add hR hP)
  have hbe : 0 ≤ b+e := add_nonneg ((norm_nonneg _).trans hR) ((norm_nonneg _).trans hP)
  calc
    _ ≤ (b+e)/‖P‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (b+e)/(1/2:ℝ) := div_le_div_of_nonneg_left hbe (by norm_num) hden
    _ = _ := by ring

/-- ACTUAL chi has a genuine full square-summable tail-disc majorant on one complex neighbourhood. -/
theorem a5Chi_Dn_l2_majorant38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∃ b : ℤ → ℝ, (∀ n, 0 ≤ b n) ∧
        Summable (fun n : ℤ => b n^2) ∧ (∑' n : ℤ, b n^2) ≤ B ∧
        ∀ n : ℤ, (N : ℤ) < |n| → ∀ z ∈ Lib.Dn n, ‖a5Chi38 n (φ,z)-1‖ ≤ b n := by
  obtain ⟨Uc, hUc, hUcW, c, hc, Nc, Bc, hBc, hC3⟩ :=
    a5ActualCriticalTau_C3_bound38 φ₀ hφ₀
  obtain ⟨Ud, hUd, hUdW, Nd, hDomain⟩ := a5TailDn_omitted_domain38 φ₀ hφ₀
  obtain ⟨Ug, hUg, _hUgW, Bg, hBg, hGap⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  let C : ℝ := c^2/4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let L : ℝ := C * Real.exp (C*Bg)
  have hL : 0 ≤ L := mul_nonneg hC (Real.exp_pos _).le
  have he : ContinuousAt (fun d : ℝ => Real.exp (C*d)-1) 0 := by fun_prop
  have hnear : {d : ℝ | Real.exp (C*d)-1 < (1/2:ℝ)} ∈ 𝓝 0 := by
    apply Filter.eventually_iff.mp
    exact he.eventually_lt_const (by norm_num)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨Ut, hUt, _hUtW, Nt, hTail⟩ := a5GammaConvolution_uniform_tail38 φ₀ hφ₀ δ hδ
  let U := Uc ∩ (Ud ∩ (Ug ∩ Ut))
  let N := max Nc (max Nd Nt)
  have hN (n : ℤ) (hn : (N : ℤ) < |n|) :
      (Nc : ℤ) < |n| ∧ (Nd : ℤ) < |n| ∧ (Nt : ℤ) < |n| := by
    have hcN : Nc ≤ N := le_max_left _ _
    have hdN : Nd ≤ N := (le_max_left Nd Nt).trans (le_max_right _ _)
    have htN : Nt ≤ N := (le_max_right Nd Nt).trans (le_max_right _ _)
    omega
  refine ⟨U, inter_mem hUc (inter_mem hUd (inter_mem hUg hUt)),
    fun φ hφ => hUcW hφ.1, N, 8*Bc+8*L^2*(Bg^2*Lib.invSqSum), ?_, ?_⟩
  · positivity [Lib.invSqSum_nonneg]
  · intro φ hφ
    have hφW := hUcW hφ.1
    obtain ⟨b, hb0, hbs, hbB, hb⟩ := hC3 φ hφ.1
    have hsγ : Summable (fun m : ℤ => ‖gamma2 φ m‖) := (hGap φ hφ.2.2.1).2.2.1
    have hγB : (∑' m : ℤ, ‖gamma2 φ m‖) ≤ Bg := (hGap φ hφ.2.2.1).2.2.2.2.2
    have hconv := a5GammaConvolution_bounds38 φ Bg hsγ hγB
    let a : ℤ → ℝ := fun n => 2*b n + 2*L*a5GammaConvolution38 φ n
    have ha0 (n : ℤ) : 0 ≤ a n := by
      exact add_nonneg (mul_nonneg (by norm_num) (hb0 n))
        (mul_nonneg (mul_nonneg (by norm_num) hL) (hconv.1 n).1)
    have hsD := hconv.2.2.2.1
    have hDB := hconv.2.2.2.2
    have hdom := (hbs.mul_left 8).add (hsD.mul_left (8*L^2))
    have hsq (n : ℤ) : a n^2 ≤ 8*b n^2 + (8*L^2)*a5GammaConvolution38 φ n^2 := by
      dsimp [a]
      nlinarith [sq_nonneg (b n - L*a5GammaConvolution38 φ n)]
    have has := hdom.of_nonneg_of_le (fun n => sq_nonneg _) hsq
    refine ⟨a, ha0, has, ?_, ?_⟩
    · apply (has.tsum_le_tsum hsq hdom).trans
      rw [(hbs.mul_left 8).tsum_add (hsD.mul_left (8*L^2)), tsum_mul_left, tsum_mul_left]
      exact add_le_add (mul_le_mul_of_nonneg_left hbB (by norm_num))
        (mul_le_mul_of_nonneg_left hDB (by positivity))
    · intro n hn z hz
      obtain ⟨hnc, hnd, hnt⟩ := hN n hn
      obtain ⟨hsep, hprod, hratio⟩ := hb n hnc z hz
      have hp := hDomain φ hφ.2.1 n hnd z hz
      have hP := a5QCorrectionProduct_linear_bound38 n (φ,z) hφW c hc hsep Bg (hconv.1 n).2
      have hPsmall : ‖a5QCorrectionProduct38 n (φ,z)-1‖ < (1/2:ℝ) := by
        have hdsmall := hTail φ hφ.2.2.2 n hnt
        have hmem : a5GammaConvolution38 φ n ∈ ball (0:ℝ) δ := by
          rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_nonneg (hconv.1 n).1]
          exact hdsmall
        exact (a5QCorrectionProduct_converges_bound38 n (φ,z) hφW c hc hsep).2.trans_lt (hδball hmem)
      have hden : (1/2:ℝ) ≤ ‖a5QCorrectionProduct38 n (φ,z)‖ := by
        have htri := norm_le_norm_sub_add (1:ℂ) (a5QCorrectionProduct38 n (φ,z))
        rw [norm_one, norm_sub_rev] at htri
        linarith
      rw [a5Chi_ratioQ38 n (φ,z) hp c hc hsep hprod]
      simpa only [a, mul_assoc] using
        a5RatioDiv_error_le38 _ _ (b n) (L*a5GammaConvolution38 φ n) hratio hP hden

theorem a5Chi_tail_circle_l2_majorant38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∃ b : ℤ → ℝ, (∀ n, 0 ≤ b n) ∧
        Summable (fun n : ℤ => b n^2) ∧ (∑' n : ℤ, b n^2) ≤ B ∧
        ∀ n : ℤ, N < n.natAbs → ∀ z ∈ sphere ((n:ℂ)*(Real.pi:ℂ)) (Real.pi/8),
          ‖a5Chi38 n (φ,z)-1‖ ≤ b n := by
  obtain ⟨U, hU, hUW, N, B, hB, h⟩ := a5Chi_Dn_l2_majorant38 φ₀ hφ₀
  refine ⟨U, hU, hUW, N, B, hB, ?_⟩
  intro φ hφ
  obtain ⟨b, hb0, hbs, hbB, hb⟩ := h φ hφ
  refine ⟨b, hb0, hbs, hbB, ?_⟩
  intro n hn z hz
  have hn' : (N:ℤ) < |n| := by
    have hcast : (N:ℤ) < (n.natAbs:ℤ) := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs] using hcast
  have hz' : z ∈ Lib.Dn n := by
    apply mem_ball_iff_norm.mpr
    rw [mem_sphere_iff_norm.mp hz]
    linarith [Real.pi_pos]
  exact hb n hn' z hz'

end
end NlsGge.GK38
