import NlsGge.GK38.StdRootBranchesFactors

/-! Openness of the complete joint cut complement: compactness is used only
for the scalar interval, and the fixed D3 family excludes every far cut. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem rootDomain_head_eventually38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38) (n : ℤ) :
    ∀ᶠ q in 𝓝 p, q.1 ∈ gkW →
      q.2 ∉ segment ℝ (lamMinus q.1 n) (lamPlus q.1 n) := by
  have hn := rootDomain_avoids38 hp n
  have hne (t : ℝ) (ht : t ∈ Icc 0 1) :
      (p.2 - tauN p.1 n)^2 - (t : ℂ)^2 * gamma2 p.1 n / 4 ≠ 0 := by
    intro he
    exact hn ((segment_spectral_iff38 p.1 hp.1 n p.2).mpr ⟨t, ht, sub_eq_zero.mp he⟩)
  have he : ∀ᶠ q in 𝓝 p, ∀ t ∈ Icc (0 : ℝ) 1,
      (q.2 - tauN q.1 n)^2 - (t : ℂ)^2 * gamma2 q.1 n / 4 ≠ 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hprojection : Continuous (fun q : (PotPair × ℂ) × ℝ => q.1.1) :=
      (continuous_fst : Continuous (fun r : PotPair × ℂ => r.1)).comp
        (continuous_fst : Continuous (fun q : (PotPair × ℂ) × ℝ => q.1))
    have hτouter : ContinuousAt (fun φ : PotPair => tauN φ n) p.1 :=
      (tauN_analytic n p.1 hp.1).continuousAt
    have hgouter : ContinuousAt (fun φ : PotPair => gamma2 φ n) p.1 :=
      (gamma2_analytic n p.1 hp.1).continuousAt
    have hτ : ContinuousAt (fun q : (PotPair × ℂ) × ℝ => tauN q.1.1 n) (p,t) :=
      ContinuousAt.comp' (f := fun q : (PotPair × ℂ) × ℝ => q.1.1)
        (g := fun φ : PotPair => tauN φ n) (x := (p,t)) hτouter hprojection.continuousAt
    have hg : ContinuousAt (fun q : (PotPair × ℂ) × ℝ => gamma2 q.1.1 n) (p,t) :=
      ContinuousAt.comp' (f := fun q : (PotPair × ℂ) × ℝ => q.1.1)
        (g := fun φ : PotPair => gamma2 φ n) (x := (p,t)) hgouter hprojection.continuousAt
    have hz : ContinuousAt (fun q : (PotPair × ℂ) × ℝ => q.1.2) (p,t) :=
      continuous_fst.snd.continuousAt
    have hc : ContinuousAt (fun q : (PotPair × ℂ) × ℝ => (q.2 : ℂ)) (p,t) :=
      Complex.continuous_ofReal.continuousAt.comp continuous_snd.continuousAt
    exact (((hz.sub hτ).pow 2).sub (((hc.pow 2).mul hg).div_const 4)).eventually_ne
      (hne t ht)
  filter_upwards [he] with q hq hW hseg
  obtain ⟨t, ht, heq⟩ := (segment_spectral_iff38 q.1 hW n q.2).mp hseg
  exact hq t ht (sub_eq_zero.mpr heq)

theorem rootDomain_far_exclusion38 (R : ℝ) : ∃ M : ℕ, ∀ n : ℤ,
    (M : ℤ) < |n| → ∀ z : ℂ, ‖z‖ < R →
      z ∉ ball (countingCenter38 n) (Real.pi / 4) := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((R + Real.pi / 4) / Real.pi)
  refine ⟨M, fun n hn z hz hb => ?_⟩
  have hbig := (div_lt_iff₀ Real.pi_pos).mp hM
  have hfar := countingCenter_far_norm38 hn
  have hsmall := mem_ball_iff_norm.mp hb
  have htri : ‖countingCenter38 n‖ ≤ ‖z - countingCenter38 n‖ + ‖z‖ := by
    simpa only [sub_add_cancel, norm_neg, norm_sub_rev] using
      norm_add_le (countingCenter38 n - z) z
  nlinarith [Real.pi_pos]

theorem isOpen_rootDomain38 : IsOpen rootDomain38 := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨V, hV, hVW, _hVo, _hVc, C, R, c, N, hgeom, hspec⟩ :=
    local_isolatingFamily_common38 p.1 hp.1
  obtain ⟨J, hJ⟩ := rootDomain_far_exclusion38 (‖p.2‖ + 1)
  let M : ℕ := max N J
  have hhead : ∀ᶠ q in 𝓝 p, ∀ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      q.1 ∈ gkW → q.2 ∉ segment ℝ (lamMinus q.1 n) (lamPlus q.1 n) :=
    (Finset.Icc (-(M : ℤ)) (M : ℤ)).eventually_all.mpr
      (fun n _ => rootDomain_head_eventually38 p hp n)
  have hpot : ∀ᶠ q in 𝓝 p, q.1 ∈ V := continuous_fst.continuousAt.preimage_mem_nhds hV
  have hz : ∀ᶠ q in 𝓝 p, ‖q.2‖ < ‖p.2‖ + 1 :=
    (continuous_snd.norm.continuousAt).eventually_lt_const (by linarith)
  filter_upwards [hhead, hpot, hz] with q hq hqV hqz
  refine ⟨hVW hqV, ?_⟩
  intro hgap
  obtain ⟨n, hn⟩ := mem_iUnion.mp hgap
  by_cases hsmall : |n| ≤ (M : ℤ)
  · exact hq n (Finset.mem_Icc.mpr (abs_le.mp hsmall)) (hVW hqV) hn
  · have hM : (M : ℤ) < |n| := lt_of_not_ge hsmall
    have hN : (N : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast le_max_left N J) hM
    have hJ' : (J : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast le_max_right N J) hM
    have hcut := (hspec q.1 hqV).1 n |>.1 hn
    obtain ⟨hc, hr, _⟩ := hgeom.2.2.2.2 n hN
    rw [hc, hr] at hcut
    exact hJ n hJ' q.2 hqz hcut

end
end NlsGge.GK38
