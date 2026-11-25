import Mathlib
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2023
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.GradEigenDefs
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualGapsActionsE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def localLogDiscriminant (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  Complex.log (parity n * (discrim φ z + canonRoot38 φ z))

namespace G2028Aux

theorem slit_of_re_gt {s t : ℂ} (h : t ^ 2 = s ^ 2 - 4) (hs : -2 < s.re) :
    s + t ∈ Complex.slitPlane := by
  by_contra hn
  rw [Complex.mem_slitPlane_iff] at hn
  push_neg at hn
  obtain ⟨hre, him⟩ := hn
  have hprod : (s + t) * (s - t) = 4 := by linear_combination -h
  have hne : s + t ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hprod; norm_num at hprod
  set x : ℝ := (s + t).re with hx
  have hxc : s + t = (x : ℂ) := Complex.ext (by simp [hx]) (by simpa using him)
  have hx0 : x ≠ 0 := by
    intro h0; apply hne; rw [hxc, h0]; simp
  have hxneg : x < 0 := lt_of_le_of_ne hre hx0
  have hst : s - t = ((4 / x : ℝ) : ℂ) := by
    have : (s - t) = 4 / (s + t) := by field_simp; linear_combination hprod
    rw [this, hxc]; push_cast; rfl
  have h2s : 2 * s = ((x + 4 / x : ℝ) : ℂ) := by
    have : 2 * s = (s + t) + (s - t) := by ring
    rw [this, hxc, hst]; push_cast; ring
  have hre2 : 2 * s.re = x + 4 / x := by
    have := congrArg Complex.re h2s
    simpa using this
  have hle : x + 4 / x ≤ -4 := by
    have : x + 4 / x + 4 = (x + 2) ^ 2 / x := by field_simp; ring
    have h3 : (x + 2) ^ 2 / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hxneg.le
    linarith
  linarith

theorem parity_eq_cos (n : ℤ) : parity n = ((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) := by
  have hc : Real.cos ((n : ℝ) * Real.pi) = (-1 : ℝ) ^ n := by
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · have : ((2 * k : ℤ) : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) := by push_cast; ring
      rw [this, Real.cos_int_mul_two_pi]
      exact ((Even.neg_one_zpow ⟨k, by ring⟩)).symm
    · have : ((2 * k + 1 : ℤ) : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) + Real.pi := by push_cast; ring
      rw [this, Real.cos_add_pi, Real.cos_int_mul_two_pi]
      have : Odd (2 * k + 1) := ⟨k, rfl⟩
      rw [this.neg_one_zpow]
  rw [hc]; unfold parity; push_cast; rfl

theorem parity_sq (n : ℤ) : parity n * parity n = 1 := by
  rcases Int.even_or_odd n with h | h
  · unfold parity; rw [h.neg_one_zpow]; norm_num
  · unfold parity; rw [h.neg_one_zpow]; norm_num

theorem parity_ne_zero (n : ℤ) : parity n ≠ 0 := by
  intro h; have := parity_sq n; rw [h] at this; norm_num at this

/-- Real boundary fact: on the closed gap, `parity n * Δ ≥ 2`. -/
theorem two_le_re_parity_discrim (u : PhysicalL2) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :
    2 ≤ (parity n * discrim (realSlice u) (x : ℂ)).re := by
  have hlev : x ∈ actualGapLevelSetE02_38 u n := by
    rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2]; exact hx
  have hre : actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := hlev
  set L := actualQuasimomentumBoundaryE02_38 u x with hL
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hlim1 : Tendsto (fun z : ℂ => Complex.cos (actualQuasimomentumE02_38 u z))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (Complex.cos L)) :=
    ((Complex.continuous_cos.tendsto L).comp (tendsto_actualQuasimomentumBoundaryE02_38 u x))
  have hD : Continuous (actualPhysicalUnitHalfTrace32 u) :=
    (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      continuous_id (fun _ => Set.mem_univ _)
  have hlim2 : Tendsto (fun z : ℂ => Complex.cos (actualQuasimomentumE02_38 u z))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (actualPhysicalUnitHalfTrace32 u (x : ℂ))) := by
    have : Tendsto (actualPhysicalUnitHalfTrace32 u) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
        (𝓝 (actualPhysicalUnitHalfTrace32 u (x : ℂ))) :=
      (hD.tendsto _).mono_left nhdsWithin_le_nhds
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hk.2.1 z hz).symm
  haveI : (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    exact mem_closure_upperHalfPlane_E02_38 (by simp)
  have hHT : actualPhysicalUnitHalfTrace32 u (x : ℂ) = Complex.cos L :=
    tendsto_nhds_unique hlim2 hlim1
  have hLre : L.re = (n : ℝ) * Real.pi := hre
  have hw : L = (((n : ℝ) * Real.pi : ℝ) : ℂ) + ((L.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hLre]
  have hcos : (actualPhysicalUnitHalfTrace32 u (x : ℂ)).re =
      Real.cos ((n : ℝ) * Real.pi) * Real.cosh L.im := by
    rw [hHT]
    conv_lhs => rw [hw]
    rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Real.sin_int_mul_pi]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero]
  rw [discrim_realSlice, parity_eq_cos]
  have h1 := real_cos_int_mul_pi_sq_E02_38 n
  have h2 := Real.one_le_cosh L.im
  have : (((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) * (2 * actualPhysicalUnitHalfTrace32 u (x : ℂ))).re =
      2 * (Real.cos ((n : ℝ) * Real.pi) * (actualPhysicalUnitHalfTrace32 u (x : ℂ)).re) := by
    rw [Complex.re_ofReal_mul]
    have h2 : (2 * actualPhysicalUnitHalfTrace32 u (x : ℂ)).re =
        2 * (actualPhysicalUnitHalfTrace32 u (x : ℂ)).re := by simp [Complex.mul_re]
    rw [h2]; ring
  rw [this, hcos]
  nlinarith


theorem isCompact_gapSegment (φ : PotPair) (n : ℤ) : IsCompact (gapSegment φ n) := by
  unfold gapSegment
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

theorem endpoints_near (u : PhysicalL2) (n : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set PotPair, IsOpen W ∧ realSlice u ∈ W ∧ ∀ φ ∈ W,
      lamMinus φ n ∈ thickening ε (gapSegment (realSlice u) n) ∧
      lamPlus φ n ∈ thickening ε (gapSegment (realSlice u) n) := by
  have hφ0 : realSlice u ∈ gkW := realSlice_mem_gkW u
  set φ0 : PotPair := realSlice u with hφ0d
  set τ0 : ℂ := tauN φ0 n with hτ0
  set G0 : ℂ := gamma2 φ0 n with hG0
  set δ : ℝ := ε / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hτc : ContinuousOn (fun φ => tauN φ n) gkW := (tauN_analytic n).continuousOn
  have hGc : ContinuousOn (fun φ => gamma2 φ n) gkW := (gamma2_analytic n).continuousOn
  let t1 : Set ℂ := Metric.ball τ0 (δ / 2)
  let t2 : Set ℂ := Metric.ball G0 (δ ^ 2)
  have ho1 : IsOpen (gkW ∩ (fun φ => tauN φ n) ⁻¹' t1) :=
    hτc.isOpen_inter_preimage isOpen_gkW Metric.isOpen_ball
  have ho2 : IsOpen (gkW ∩ (fun φ => gamma2 φ n) ⁻¹' t2) :=
    hGc.isOpen_inter_preimage isOpen_gkW Metric.isOpen_ball
  refine ⟨(gkW ∩ (fun φ => tauN φ n) ⁻¹' t1) ∩ (gkW ∩ (fun φ => gamma2 φ n) ⁻¹' t2),
    ho1.inter ho2, ⟨⟨hφ0, ?_⟩, ⟨hφ0, ?_⟩⟩, ?_⟩
  · simp [t1, hτ0, hδpos]
  · simp [t2, hG0, hδpos]
  rintro φ ⟨⟨hφ, h1⟩, ⟨_, h2⟩⟩
  have h1' : ‖tauN φ n - τ0‖ < δ / 2 := by
    simpa [t1, Metric.mem_ball, dist_eq_norm] using h1
  have h2' : ‖gamma2 φ n - G0‖ < δ ^ 2 := by
    simpa [t2, Metric.mem_ball, dist_eq_norm] using h2
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hφ n
  have hG : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hφ n
  have hτ' : τ0 = (lamPlus φ0 n + lamMinus φ0 n) / 2 := tauN_value38 φ0 hφ0 n
  have hG' : G0 = (lamPlus φ0 n - lamMinus φ0 n) ^ 2 := gamma2_value38 φ0 hφ0 n
  set d : ℂ := (lamPlus φ n - lamMinus φ n) / 2 with hd
  set d0 : ℂ := (lamPlus φ0 n - lamMinus φ0 n) / 2 with hd0
  have hlp : lamPlus φ n = tauN φ n + d := by rw [hτ, hd]; ring
  have hlm : lamMinus φ n = tauN φ n - d := by rw [hτ, hd]; ring
  have hlp0 : lamPlus φ0 n = τ0 + d0 := by rw [hτ', hd0]; ring
  have hlm0 : lamMinus φ0 n = τ0 - d0 := by rw [hτ', hd0]; ring
  have hdd : d ^ 2 - d0 ^ 2 = (gamma2 φ n - G0) / 4 := by
    rw [hG, hG', hd, hd0]; ring
  have hcase : ‖d - d0‖ < δ / 2 ∨ ‖d + d0‖ < δ / 2 := by
    by_contra hcon
    push_neg at hcon
    have hmul : ‖d ^ 2 - d0 ^ 2‖ = ‖d - d0‖ * ‖d + d0‖ := by
      rw [← norm_mul]; congr 1; ring
    have hge : (δ / 2) * (δ / 2) ≤ ‖d - d0‖ * ‖d + d0‖ :=
      mul_le_mul hcon.1 hcon.2 (by positivity) (norm_nonneg _)
    have hlt : ‖d ^ 2 - d0 ^ 2‖ < δ ^ 2 / 4 := by
      rw [hdd, norm_div]
      have : ‖(4 : ℂ)‖ = 4 := by simp
      rw [this, div_lt_iff₀ (by norm_num)]
      linarith
    nlinarith
  have memK : ∀ a : ℂ, (a = lamMinus φ0 n ∨ a = lamPlus φ0 n) → a ∈ gapSegment φ0 n := by
    rintro a (rfl | rfl)
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have key : ∀ (e : ℂ) (a : ℂ), (a = lamMinus φ0 n ∨ a = lamPlus φ0 n) →
      dist e a < ε → e ∈ thickening ε (gapSegment φ0 n) :=
    fun e a ha hd' => Metric.mem_thickening_iff.2 ⟨a, memK a ha, hd'⟩
  have hε2 : δ / 2 + δ / 2 < ε := by rw [hδ]; linarith
  rcases hcase with hc | hc
  · refine ⟨key _ (lamMinus φ0 n) (Or.inl rfl) ?_, key _ (lamPlus φ0 n) (Or.inr rfl) ?_⟩
    · rw [dist_eq_norm, hlm, hlm0]
      calc ‖tauN φ n - d - (τ0 - d0)‖ = ‖(tauN φ n - τ0) - (d - d0)‖ := by congr 1; ring
        _ ≤ ‖tauN φ n - τ0‖ + ‖d - d0‖ := norm_sub_le _ _
        _ < ε := by linarith
    · rw [dist_eq_norm, hlp, hlp0]
      calc ‖tauN φ n + d - (τ0 + d0)‖ = ‖(tauN φ n - τ0) + (d - d0)‖ := by congr 1; ring
        _ ≤ ‖tauN φ n - τ0‖ + ‖d - d0‖ := norm_add_le _ _
        _ < ε := by linarith
  · refine ⟨key _ (lamPlus φ0 n) (Or.inr rfl) ?_, key _ (lamMinus φ0 n) (Or.inl rfl) ?_⟩
    · rw [dist_eq_norm, hlm, hlp0]
      calc ‖tauN φ n - d - (τ0 + d0)‖ = ‖(tauN φ n - τ0) - (d + d0)‖ := by congr 1; ring
        _ ≤ ‖tauN φ n - τ0‖ + ‖d + d0‖ := norm_sub_le _ _
        _ < ε := by linarith
    · rw [dist_eq_norm, hlp, hlm0]
      calc ‖tauN φ n + d - (τ0 - d0)‖ = ‖(tauN φ n - τ0) + (d + d0)‖ := by congr 1; ring
        _ ≤ ‖tauN φ n - τ0‖ + ‖d + d0‖ := norm_add_le _ _
        _ < ε := by linarith

end G2028Aux

open G2028Aux

theorem G2_028 (u : PhysicalL2) (n : ℤ) :
    ∃ V : Set PotPair, IsOpen V ∧ realSlice u ∈ V ∧ V ⊆ gkW ∧
      ∃ U : Set ℂ, IsOpen U ∧ gapSegment (realSlice u) n ⊆ U ∧
        (∀ φ ∈ V, gapSegment φ n ⊆ U) ∧
        AnalyticOnNhd ℂ
          (fun p : PotPair × ℂ => localLogDiscriminant n p.1 p.2)
          {p | p.1 ∈ V ∧ p.2 ∈ U ∧ p ∈ rootDomain38} ∧
        ∀ φ ∈ V, ∀ z ∈ U, (φ,z) ∈ rootDomain38 →
          parity n*(discrim φ z+canonRoot38 φ z) ∈ Complex.slitPlane ∧
          HasDerivAt (localLogDiscriminant n φ)
            (deriv (discrim φ) z/canonRoot38 φ z) z := by
  have hφ0 : realSlice u ∈ gkW := realSlice_mem_gkW u
  set K : Set ℂ := gapSegment (realSlice u) n with hK
  have hKc : IsCompact K := isCompact_gapSegment _ _
  have hHc : Continuous (fun p : PotPair × ℂ => parity n * discrim p.1 p.2) :=
    continuous_const.mul (continuousOn_univ.1 analyticOnNhd_discrim.continuousOn)
  set Ω : Set (PotPair × ℂ) := {p | -2 < (parity n * discrim p.1 p.2).re} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt continuous_const (Complex.continuous_re.comp hHc)
  have hsub : ({realSlice u} : Set PotPair) ×ˢ K ⊆ Ω := by
    rintro ⟨φ, z⟩ ⟨hφ, hz⟩
    have hφ' : φ = realSlice u := hφ
    subst hφ'
    simp only [hΩ, Set.mem_setOf_eq]
    obtain ⟨hp, hm⟩ := lamPlus_real u n
    have hz' : z ∈ segment ℝ ((actualGapLowerAllE02_38 u n : ℝ) : ℂ)
        ((actualGapUpperAllE02_38 u n : ℝ) : ℂ) := by
      have := hz; simp only [hK, gapSegment] at this; rwa [hp, hm] at this
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz'
    have hab := (gap_endpoint_levels38 u n).1
    have hx : s * actualGapLowerAllE02_38 u n + t * actualGapUpperAllE02_38 u n ∈
        Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
      have hs' : s = 1 - t := by linarith
      rw [hs']
      constructor <;> nlinarith [mul_nonneg ht (sub_nonneg.2 hab)]
    have h2 := two_le_re_parity_discrim u n _ hx
    have e : s • ((actualGapLowerAllE02_38 u n : ℝ) : ℂ) + t • ((actualGapUpperAllE02_38 u n : ℝ) : ℂ)
        = ((s * actualGapLowerAllE02_38 u n + t * actualGapUpperAllE02_38 u n : ℝ) : ℂ) := by
      simp [Complex.real_smul]
    rw [e]; linarith
  obtain ⟨V0, U0, hV0o, hU0o, hV0, hKU0, hVU⟩ :=
    generalized_tube_lemma isCompact_singleton hKc hΩo hsub
  obtain ⟨ε, hε, hth⟩ := hKc.exists_thickening_subset_open hU0o hKU0
  obtain ⟨W, hWo, hφW, hWend⟩ := endpoints_near u n hε
  have hVo : IsOpen (V0 ∩ W ∩ gkW) := (hV0o.inter hWo).inter isOpen_gkW
  have hconv : Convex ℝ (thickening ε K) := (convex_segment _ _).thickening ε
  have hslit : ∀ φ ∈ V0 ∩ W ∩ gkW, ∀ z ∈ thickening ε K, (φ, z) ∈ rootDomain38 →
      parity n * (discrim φ z + canonRoot38 φ z) ∈ Complex.slitPlane := by
    intro φ hφ z hz hp
    have hΩm : (φ, z) ∈ Ω := hVU (Set.mk_mem_prod hφ.1.1 (hth hz))
    have hsq := ((G2_023.2.1) (φ, z) hp).2
    have hsq' : (parity n * canonRoot38 φ z) ^ 2 = (parity n * discrim φ z) ^ 2 - 4 := by
      have h1 := parity_sq n
      calc (parity n * canonRoot38 φ z) ^ 2 = (parity n * parity n) * canonRoot38 φ z ^ 2 := by ring
        _ = (parity n * parity n) * (discrim φ z ^ 2 - 4) := by rw [hsq]
        _ = (parity n * discrim φ z) ^ 2 - 4 * (parity n * parity n) := by ring
        _ = (parity n * discrim φ z) ^ 2 - 4 := by rw [h1]; ring
    have := slit_of_re_gt hsq' hΩm
    simpa only [mul_add] using this
  refine ⟨V0 ∩ W ∩ gkW, hVo, ⟨⟨hV0 rfl, hφW⟩, hφ0⟩, fun φ hφ => hφ.2, thickening ε K,
    isOpen_thickening, self_subset_thickening hε K, ?_, ?_, ?_⟩
  · intro φ hφ
    exact hconv.segment_subset (hWend φ hφ.1.2).1 (hWend φ hφ.1.2).2
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hs := hslit p.1 h1 p.2 h2 h3
    have hA : AnalyticAt ℂ
        (fun q : PotPair × ℂ => parity n * (discrim q.1 q.2 + canonRoot38 q.1 q.2)) p :=
      analyticAt_const.mul ((analyticOnNhd_discrim p (Set.mem_univ _)).add
        (canonRoot_analytic38 p h3))
    exact hA.clog hs
  · intro φ hφ z hz hp
    have hs := hslit φ hφ z hz hp
    refine ⟨hs, ?_⟩
    have hDa : AnalyticAt ℂ (discrim φ) z :=
      (analyticOnNhd_discrim (φ, z) (Set.mem_univ _)).comp
        (analyticAt_const.prod analyticAt_id)
    have hRa : AnalyticAt ℂ (canonRoot38 φ) z :=
      (canonRoot_analytic38 (φ, z) hp).comp (analyticAt_const.prod analyticAt_id)
    have hΔ : HasDerivAt (discrim φ) (deriv (discrim φ) z) z := hDa.differentiableAt.hasDerivAt
    have hr : HasDerivAt (canonRoot38 φ) (deriv (canonRoot38 φ) z) z :=
      hRa.differentiableAt.hasDerivAt
    have hr0 : canonRoot38 φ z ≠ 0 := (G2_023.2.1 (φ, z) hp).1
    have hnhd : {w : ℂ | (φ, w) ∈ rootDomain38} ∈ 𝓝 z :=
      (isOpen_rootDomain38.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp
    have hev : (fun w => canonRoot38 φ w * canonRoot38 φ w) =ᶠ[𝓝 z]
        fun w => discrim φ w * discrim φ w - 4 := by
      filter_upwards [hnhd] with w hw
      have := ((G2_023.2.1) (φ, w) hw).2
      simp only at this
      rw [← sq, this]; ring
    have h1 := hr.mul hr
    have h2 := ((hΔ.mul hΔ).sub_const 4).congr_of_eventuallyEq hev
    have hu := h1.unique h2
    set r' := deriv (canonRoot38 φ) z with hr'
    set D' := deriv (discrim φ) z with hD'
    have hr'eq : r' = discrim φ z * D' / canonRoot38 φ z := by
      field_simp
      linear_combination hu / 2
    have hne := Complex.slitPlane_ne_zero hs
    have hP := parity_ne_zero n
    have hsum : discrim φ z + canonRoot38 φ z ≠ 0 := by
      intro h0; apply hne; rw [h0, mul_zero]
    have hf : HasDerivAt (fun w => parity n * (discrim φ w + canonRoot38 φ w))
        (parity n * (D' + r')) z := (hΔ.add hr).const_mul (parity n)
    show HasDerivAt (fun w => Complex.log (parity n * (discrim φ w + canonRoot38 φ w))) _ z
    refine (hf.clog hs).congr_deriv ?_
    rw [hr'eq]
    field_simp
    ring


end
end NlsGge.GKDefinitionDesign
