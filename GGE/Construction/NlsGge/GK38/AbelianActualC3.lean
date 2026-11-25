import NlsGge.GK38.XiSqActualC3

/-! Actual C3 for ARBITRARY full complex sequence input. UNCOMPILED prospective source.
Proof structure reuses the accepted actual critical/tau C3 instantiation, replacing the
critical-root Hilbert estimate by the genuine arbitrary input Hilbert norm estimate.
All actual tau geometry and the licensed pinned C3 theorem remain unchanged. -/
set_option autoImplicit false
open Set Filter Topology Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

theorem p2ArbitraryTau_C3_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ φ ∈ U, ∀ s ∈ V, ∃ b : ℤ → ℝ,
        (∀ n : ℤ, 0 ≤ b n) ∧ Summable (fun n : ℤ => b n^2) ∧
        (∑' n : ℤ, b n^2) ≤ B ∧
        ∀ n : ℤ, (N : ℤ) < |n| → ∀ z ∈ Lib.Dn n,
          (∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖tauN φ m - z‖) ∧
          Multipliable (Lib.ratioFam (Lib.sigmaOf s) (tauN φ) n z) (symmetricIcc ℤ) ∧
          ‖Lib.ratioProd (Lib.sigmaOf s) (tauN φ) n z - 1‖ ≤ b n := by
  obtain ⟨Ugeom, hV, hVW, _hVo, _hVc, C, R, c, N, hg, hspec⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hg.2.2.1
  obtain ⟨Ut, hUt, _hUtW, Bt, hBt, ht⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  let V : Set Lib.L2Seq := ball s₀ 1
  let Bs : ℝ := (‖s₀‖+1)^2
  have hBs : 0 ≤ Bs := sq_nonneg _
  have hs : ∀ s ∈ V,
      Summable (fun m : ℤ => ‖Lib.prodDev (Lib.sigmaOf s) m‖^2) ∧
      (∑' m : ℤ, ‖Lib.prodDev (Lib.sigmaOf s) m‖^2) ≤ Bs := by
    intro s hs
    have hnorm : ‖s‖ ≤ ‖s₀‖+1 := by
      have he := norm_le_norm_sub_add s s₀
      have hd : ‖s-s₀‖ < 1 := mem_ball_iff_norm.mp hs
      linarith
    refine ⟨Lib.summable_dev_sigmaOf s,?_⟩
    simp only [Lib.dev_sigmaOf]
    rw [Lib.tsum_sq_l2]
    nlinarith [norm_nonneg s,norm_nonneg s₀]
  obtain ⟨B0, hC3⟩ := Lib.ratioProd_l2 (Real.sqrt Bt) (2 * (Bs + Bt)) c hc
  let U := Ugeom ∩ Ut
  refine ⟨U, inter_mem hV hUt, fun φ hφ => hVW hφ.1,
    V, ball_mem_nhds _ (by norm_num), c, hc, N, max B0 0, le_max_right _ _, ?_⟩
  intro φ hφ s hsV
  have hφW := hVW hφ.1
  have hsφ := hs s hsV
  have htφ := ht φ hφ.2
  have hσ : Summable (fun m : ℤ => ‖Lib.prodDev (Lib.sigmaOf s) m‖^2) := hsφ.1
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
  have hdiff (m : ℤ) : ‖Lib.sigmaOf s m - tauN φ m‖^2 ≤
      2 * (‖Lib.prodDev (Lib.sigmaOf s) m‖^2 + ‖Lib.prodDev (tauN φ) m‖^2) := by
    have he : Lib.sigmaOf s m - tauN φ m =
        Lib.prodDev (Lib.sigmaOf s) m + -(Lib.prodDev (tauN φ) m) := by
      unfold Lib.prodDev
      ring
    rw [he]
    simpa only [norm_neg] using norm_add_square_le_twice38
      (Lib.prodDev (Lib.sigmaOf s) m) (-(Lib.prodDev (tauN φ) m))
  have hdom := (hσ.add hρ).mul_left 2
  have hds := hdom.of_nonneg_of_le (fun m => sq_nonneg _) hdiff
  have hdBound : (∑' m : ℤ, ‖Lib.sigmaOf s m - tauN φ m‖^2) ≤ 2 * (Bs + Bt) := by
    apply (hds.tsum_le_tsum hdiff hdom).trans
    rw [tsum_mul_left, hσ.tsum_add hρ]
    exact mul_le_mul_of_nonneg_left (add_le_add hsφ.2 hρmass) (by norm_num)
  have hsep : ∀ n : ℤ, ((N+1 : ℕ) : ℝ) ≤ |(n : ℝ)| → ∀ m : ℤ, m ≠ n →
      ∀ z ∈ Lib.Dn n, c⁻¹ * |(m : ℝ) - n| ≤ ‖tauN φ m - z‖ := by
    intro n hn m hmn z hz
    have hn' : ((N+1 : ℕ) : ℤ) ≤ |n| := by exact_mod_cast hn
    have hlarge : (N : ℤ) < |n| := by omega
    exact a5Tau_Dn_separation38 φ hφW C R c N hg (hspec φ hφ.1) n hlarge z hz m hmn
  obtain ⟨b, hb, hbs, hbB⟩ := hC3 (Lib.sigmaOf s) (tauN φ) (N+1) hσ hρ
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

#print axioms p2ArbitraryTau_C3_bound38
end
end NlsGge.GK38
