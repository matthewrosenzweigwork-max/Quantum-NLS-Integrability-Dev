import NlsGge.GK38.XiSqActualC3

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

def a5GammaHilbert38 : PotPair → Lib.L2Z := Classical.choose a5Gamma2_l2_realization38

theorem a5GammaHilbert_value38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    a5GammaHilbert38 φ m = gamma2 φ m :=
  (Classical.choose_spec a5Gamma2_l2_realization38).1 φ hφ m

theorem a5GammaHilbert_analytic38 : AnalyticOnNhd ℂ a5GammaHilbert38 gkW :=
  (Classical.choose_spec a5Gamma2_l2_realization38).2

theorem a5GammaWeighted_summable38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    Summable (fun m : ℤ => ‖gamma2 φ m‖ * Lib.c3w n m^2) := by
  apply (a5GammaNorm_summable38 φ hφ).of_nonneg_of_le (fun m => by positivity)
  intro m
  have hw : Lib.c3w n m^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (Lib.c3w_nonneg n m) (Lib.c3w_le_one n m) 2
  exact (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans_eq (mul_one _)

/-- An actual Hilbert norm controls the convolution uniformly in the output label. -/
theorem a5GammaConvolution_lipschitz38 (φ ψ : PotPair)
    (hφ : φ ∈ gkW) (hψ : ψ ∈ gkW) (n : ℤ) :
    a5GammaConvolution38 φ n ≤ a5GammaConvolution38 ψ n +
      ‖a5GammaHilbert38 φ - a5GammaHilbert38 ψ‖ * Real.sqrt Lib.invSqSum := by
  let x : Lib.L2Z := a5GammaHilbert38 φ - a5GammaHilbert38 ψ
  have hx (m : ℤ) : x m = gamma2 φ m - gamma2 ψ m := by
    change a5GammaHilbert38 φ m - a5GammaHilbert38 ψ m = _
    rw [a5GammaHilbert_value38 φ hφ, a5GammaHilbert_value38 ψ hψ]
  have hkernel (m : ℤ) : (Lib.c3w n m^2)^2 ≤ Lib.c3w n m^2 := by
    have hw0 := Lib.c3w_nonneg n m
    have hw1 := Lib.c3w_le_one n m
    have hw2 : Lib.c3w n m^2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hw0 hw1 2
    nlinarith [sq_nonneg (Lib.c3w n m)]
  have hks := (Lib.summable_c3w_sq n).of_nonneg_of_le (fun m => sq_nonneg _) hkernel
  have hkbound : (∑' m : ℤ, (Lib.c3w n m^2)^2) ≤ Lib.invSqSum := by
    exact (hks.tsum_le_tsum hkernel (Lib.summable_c3w_sq n)).trans_eq (Lib.tsum_c3w_sq n)
  obtain ⟨hcs, hcsBound⟩ := Lib.cs_tsum (fun m => norm_nonneg (x m)) (fun m => sq_nonneg _)
    (Lib.hasSum_sq_l2 x).summable hks
  have hcsBound' : (∑' m : ℤ, ‖x m‖ * Lib.c3w n m^2) ≤
      ‖x‖ * Real.sqrt Lib.invSqSum := by
    rw [Lib.tsum_sq_l2 x, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)] at hcsBound
    exact hcsBound.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkbound) (norm_nonneg x))
  have hφs := a5GammaWeighted_summable38 φ hφ n
  have hψs := a5GammaWeighted_summable38 ψ hψ n
  have hpoint (m : ℤ) : ‖gamma2 φ m‖ * Lib.c3w n m^2 ≤
      ‖gamma2 ψ m‖ * Lib.c3w n m^2 + ‖x m‖ * Lib.c3w n m^2 := by
    have h := mul_le_mul_of_nonneg_right (norm_le_norm_sub_add (gamma2 φ m) (gamma2 ψ m))
      (sq_nonneg (Lib.c3w n m))
    rw [← hx m, add_mul] at h
    simpa only [add_comm] using h
  rw [a5GammaConvolution_eq38, a5GammaConvolution_eq38]
  calc
    _ ≤ (∑' m : ℤ, ‖gamma2 ψ m‖ * Lib.c3w n m^2) +
        ∑' m : ℤ, ‖x m‖ * Lib.c3w n m^2 := by
      simpa only [hψs.tsum_add hcs] using hφs.tsum_le_tsum hpoint (hψs.add hcs)
    _ ≤ _ := add_le_add le_rfl hcsBound'

/-- Genuine summability at one point gives cofinite tails before any uniform conclusion. -/
theorem a5GammaConvolution_point_tail38 (φ : PotPair) (hφ : φ ∈ gkW)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) < |n| → a5GammaConvolution38 φ n < ε := by
  have hsγ := a5GammaNorm_summable38 φ hφ
  have hsd := (a5GammaConvolution_bounds38 φ (∑' m : ℤ, ‖gamma2 φ m‖) hsγ le_rfl).2.1
  have ht := hsd.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)
  have hf : {n : ℤ | ¬a5GammaConvolution38 φ n < ε}.Finite := eventually_cofinite.mp ht
  obtain ⟨b, hb⟩ := (hf.image (fun n : ℤ => |n|)).bddAbove
  refine ⟨b.natAbs, fun n hn => ?_⟩
  by_contra hnot
  have hnle : |n| ≤ b := hb ⟨n, hnot, rfl⟩
  have hbabs : b ≤ (b.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self b
  omega

/-- Uniform tails are earned from actual analytic-Hilbert NORM continuity, not local mass alone. -/
theorem a5GammaConvolution_uniform_tail38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ U, ∀ n : ℤ, (N : ℤ) < |n| → a5GammaConvolution38 φ n < ε := by
  obtain ⟨N, hN⟩ := a5GammaConvolution_point_tail38 φ₀ hφ₀ (ε/2) (half_pos hε)
  let K := Real.sqrt Lib.invSqSum
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  let δ := ε / (2 * (K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hc := (a5GammaHilbert_analytic38 φ₀ hφ₀).continuousAt
  have hU : {φ : PotPair | ‖a5GammaHilbert38 φ - a5GammaHilbert38 φ₀‖ < δ} ∈ 𝓝 φ₀ := by
    apply Filter.eventually_iff.mp
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hc δ hδ
  refine ⟨_ ∩ gkW, inter_mem hU (isOpen_gkW.mem_nhds hφ₀), inter_subset_right, N, ?_⟩
  intro φ hφ n hn
  have hb := a5GammaConvolution_lipschitz38 φ φ₀ hφ.2 hφ₀ n
  have hsmall : ‖a5GammaHilbert38 φ - a5GammaHilbert38 φ₀‖ * (2 * (K+1)) < ε := by
    exact (lt_div_iff₀ (by positivity)).mp hφ.1
  have hnorm := norm_nonneg (a5GammaHilbert38 φ - a5GammaHilbert38 φ₀)
  have htail := hN n hn
  change a5GammaConvolution38 φ n ≤ a5GammaConvolution38 φ₀ n +
    ‖a5GammaHilbert38 φ - a5GammaHilbert38 φ₀‖ * K at hb
  nlinarith

end
end NlsGge.GK38
