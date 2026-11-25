import NlsGge.GK38.XiSqRootCorrection
import NlsGge.GK38.XiSqLocal

set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

/-- The accepted C.3 theorem is instantiated with ACTUAL critical roots and ACTUAL gap means.
Every returned majorant is nonnegative (absolute value) with genuine full square summability. -/
theorem a5ActualCriticalTau_C3_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ φ ∈ U, ∃ b : ℤ → ℝ,
        (∀ n : ℤ, 0 ≤ b n) ∧ Summable (fun n : ℤ => b n^2) ∧
        (∑' n : ℤ, b n^2) ≤ B ∧
        ∀ n : ℤ, (N : ℤ) < |n| → ∀ z ∈ Lib.Dn n,
          (∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖tauN φ m - z‖) ∧
          Multipliable (Lib.ratioFam (lamDot φ) (tauN φ) n z) (symmetricIcc ℤ) ∧
          ‖Lib.ratioProd (lamDot φ) (tauN φ) n z - 1‖ ≤ b n := by
  obtain ⟨V, hV, hVW, _hVo, _hVc, C, R, c, N, hg, hspec⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hg.2.2.1
  obtain ⟨Ut, hUt, _hUtW, Bt, hBt, ht⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  obtain ⟨Us, hUs, Bs, hBs, hs⟩ := critical_l2 φ₀
  obtain ⟨B0, hC3⟩ := Lib.ratioProd_l2 (Real.sqrt Bt) (2 * (Bs + Bt)) c hc
  let U := V ∩ (Ut ∩ Us)
  refine ⟨U, inter_mem hV (inter_mem hUt hUs), fun φ hφ => hVW hφ.1,
    c, hc, N, max B0 0, le_max_right _ _, ?_⟩
  intro φ hφ
  have hφW := hVW hφ.1
  have hsφ := hs φ hφ.2.2
  have htφ := ht φ hφ.2.1
  have hσ : Summable (fun m : ℤ => ‖Lib.prodDev (lamDot φ) m‖^2) := hsφ.1
  have hρ : Summable (fun m : ℤ => ‖Lib.prodDev (tauN φ) m‖^2) := htφ.1
  have hρmass : (∑' m : ℤ, ‖Lib.prodDev (tauN φ) m‖^2) ≤ Bt := htφ.2.2.2.1
  have hρcoord (m : ℤ) : ‖Lib.prodDev (tauN φ) m‖ ≤ Real.sqrt Bt := by
    have hterm := hρ.sum_le_tsum ({m} : Finset ℤ) (fun _ _ => sq_nonneg _)
    have hbound : ‖Lib.prodDev (tauN φ) m‖^2 ≤ Bt := by
      have hp : ‖Lib.prodDev (tauN φ) m‖^2 ≤
          ∑' j : ℤ, ‖Lib.prodDev (tauN φ) j‖^2 := by
        simpa only [Finset.sum_singleton] using hterm
      exact hp.trans hρmass
    nlinarith [Real.sq_sqrt hBt, Real.sqrt_nonneg Bt, norm_nonneg (Lib.prodDev (tauN φ) m)]
  have hdiff (m : ℤ) : ‖lamDot φ m - tauN φ m‖^2 ≤
      2 * (‖Lib.prodDev (lamDot φ) m‖^2 + ‖Lib.prodDev (tauN φ) m‖^2) := by
    have he : lamDot φ m - tauN φ m =
        Lib.prodDev (lamDot φ) m + -(Lib.prodDev (tauN φ) m) := by
      unfold Lib.prodDev
      ring
    rw [he]
    simpa only [norm_neg] using norm_add_square_le_twice38
      (Lib.prodDev (lamDot φ) m) (-(Lib.prodDev (tauN φ) m))
  have hdom := (hσ.add hρ).mul_left 2
  have hds := hdom.of_nonneg_of_le (fun m => sq_nonneg _) hdiff
  have hdBound : (∑' m : ℤ, ‖lamDot φ m - tauN φ m‖^2) ≤ 2 * (Bs + Bt) := by
    apply (hds.tsum_le_tsum hdiff hdom).trans
    rw [tsum_mul_left, hσ.tsum_add hρ]
    exact mul_le_mul_of_nonneg_left (add_le_add hsφ.2 hρmass) (by norm_num)
  have hsep : ∀ n : ℤ, ((N+1 : ℕ) : ℝ) ≤ |(n : ℝ)| → ∀ m : ℤ, m ≠ n →
      ∀ z ∈ Lib.Dn n, c⁻¹ * |(m : ℝ) - n| ≤ ‖tauN φ m - z‖ := by
    intro n hn m hmn z hz
    have hn' : ((N+1 : ℕ) : ℤ) ≤ |n| := by exact_mod_cast hn
    have hlarge : (N : ℤ) < |n| := by omega
    exact a5Tau_Dn_separation38 φ hφW C R c N hg (hspec φ hφ.1) n hlarge z hz m hmn
  obtain ⟨b, hb, hbs, hbB⟩ := hC3 (lamDot φ) (tauN φ) (N+1) hσ hρ
    (a5Tau_injective38 φ hφW) hρcoord hdBound hsep
  refine ⟨fun n => |b n|, fun n => abs_nonneg _, ?_, ?_, ?_⟩
  · simpa only [sq_abs] using hbs
  · have habs : (∑' n : ℤ, |b n|^2) ≤ B0 := by
      simpa only [sq_abs] using hbB
    exact habs.trans (le_max_left _ _)
  · intro n hn z hz
    have hn' : ((N+1 : ℕ) : ℝ) ≤ |(n : ℝ)| := by
      have hni : ((N+1 : ℕ) : ℤ) ≤ |n| := by omega
      exact_mod_cast hni
    have h := hb n hn' z hz
    exact ⟨fun m hm => hsep n hn' m hm z hz, h.1, h.2.trans (le_abs_self _)⟩

/-- A full actual family certifies the WHOLE tail Dn inside the omitted domain, including its own slit. -/
theorem a5TailDn_omitted_domain38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ U, ∀ n : ℤ, (N : ℤ) < |n| → ∀ z ∈ Lib.Dn n,
        (φ, z) ∈ a5OmittedRootDomain38 n := by
  obtain ⟨V, hV, hVW, _hVo, _hVc, C, R, c, N, hg, hspec⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  refine ⟨V, hV, hVW, N, ?_⟩
  intro φ hφ n hn z hz
  have htail := hg.2.2.2.2 n hn
  have hball : z ∈ ball (C n) (R n) := by
    rw [htail.1, htail.2.1]
    exact hz
  exact a5OwnClosedBall_omittedDomain38 φ (hVW hφ) C R
    ⟨c, N, hg, hspec φ hφ⟩ n z (ball_subset_closedBall hball)

end
end NlsGge.GK38
