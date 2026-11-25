import NlsGge.GK38.AbelianActualC3
import NlsGge.GK38.AbelianRatioCorrection
import NlsGge.GK38.XiSqChiMajorant

/-! Actual arbitrary-sequence omitted-ratio majorant. UNCOMPILED prospective source.
The accepted A5 root-correction and gamma-convolution arguments are reused literally;
the numerator is now the ACTUAL arbitrary sigma from P2's input Hilbert space.
This is an intermediate ratio bound, NOT the actual Fn uniform bound. -/
set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

theorem p2OmittedRatio_Dn_l2_majorant38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∃ b : ℤ → ℝ, (∀ n, 0 ≤ b n) ∧
        Summable (fun n : ℤ => b n^2) ∧ (∑' n : ℤ, b n^2) ≤ B ∧
        ∀ n : ℤ, (N : ℤ) < |n| → ∀ z ∈ Lib.Dn n, ‖p2OmittedRatio38 n ((φ,s),z)-1‖ ≤ b n := by
  obtain ⟨Uc, hUc, hUcW, V, hV, c, hc, Nc, Bc, hBc, hC3⟩ :=
    p2ArbitraryTau_C3_bound38 φ₀ hφ₀ s₀
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
    fun φ hφ => hUcW hφ.1, V, hV, N, 8*Bc+8*L^2*(Bg^2*Lib.invSqSum), ?_, ?_⟩
  · positivity [Lib.invSqSum_nonneg]
  · intro φ hφ s hsV
    have hφW := hUcW hφ.1
    obtain ⟨b, hb0, hbs, hbB, hb⟩ := hC3 φ hφ.1 s hsV
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
      rw [p2OmittedRatio_ratioQ38 n φ s z hp c hc hsep hprod]
      simpa only [a, mul_assoc] using
        a5RatioDiv_error_le38 _ _ (b n) (L*a5GammaConvolution38 φ n) hratio hP hden

#print axioms p2OmittedRatio_Dn_l2_majorant38
end
end NlsGge.GK38
