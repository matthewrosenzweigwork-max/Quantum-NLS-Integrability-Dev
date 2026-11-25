import NlsGge.GK38.StdRootBranches

set_option autoImplicit false
open Set Metric Filter Topology SummationFilter
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- All other actual cuts are excluded; the nth actual cut remains in the domain. -/
def a5OmittedRootDomain38 (n : ℤ) : Set (PotPair × ℂ) :=
  {p | p.1 ∈ gkW ∧ ∀ m : ℤ, m ≠ n →
    p.2 ∉ segment ℝ (lamMinus p.1 m) (lamPlus p.1 m)}

def a5OmittedRootFactor38 (n m : ℤ) (p : PotPair × ℂ) : ℂ :=
  if m = n then 1 else rootFactor38 m p

/-- The symmetric product has no added prefactor and exactly omits one normalized factor. -/
def a5OmittedRootProduct38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  ∏'[symmetricIcc ℤ] m : ℤ, a5OmittedRootFactor38 n m p

/-- A single root factor only needs its own cut complement. -/
theorem a5RootFactor_analyticAt38 (m : ℤ) (p : PotPair × ℂ)
    (hW : p.1 ∈ gkW)
    (hm : p.2 ∉ segment ℝ (lamMinus p.1 m) (lamPlus p.1 m)) :
    AnalyticAt ℂ (rootFactor38 m) p := by
  have hs := stdRoot_slit38 (lamMinus p.1 m) (lamPlus p.1 m) p.2 hm
  rw [add_comm (lamMinus p.1 m), ← tauN_value38 p.1 hW m,
    ← gamma2_value38 p.1 hW m] at hs
  exact (stdRoot_analyticAt38 ((tauN_analytic m p.1 hW).comp analyticAt_fst)
    ((gamma2_analytic m p.1 hW).comp analyticAt_fst) analyticAt_snd hs.1 hs.2).div_const

theorem a5RootFactor_ne_zero38 (m : ℤ) (p : PotPair × ℂ)
    (hW : p.1 ∈ gkW)
    (hm : p.2 ∉ segment ℝ (lamMinus p.1 m) (lamPlus p.1 m)) :
    rootFactor38 m p ≠ 0 := by
  rw [rootFactor38, tauN_value38 p.1 hW m, gamma2_value38 p.1 hW m]
  rw [add_comm (lamPlus p.1 m)]
  exact div_ne_zero (stdRoot_ne_zero38 _ _ _ hm)
    (by exact_mod_cast Lib.piN_ne_zero m)

theorem a5CutComplement_eventually38 (p : PotPair × ℂ) (hW : p.1 ∈ gkW) (n : ℤ)
    (hn : p.2 ∉ segment ℝ (lamMinus p.1 n) (lamPlus p.1 n)) :
    ∀ᶠ q in 𝓝 p, q.1 ∈ gkW →
      q.2 ∉ segment ℝ (lamMinus q.1 n) (lamPlus q.1 n) := by
  have hne (t : ℝ) (ht : t ∈ Icc 0 1) :
      (p.2 - tauN p.1 n)^2 - (t : ℂ)^2 * gamma2 p.1 n / 4 ≠ 0 := by
    intro he
    exact hn ((segment_spectral_iff38 p.1 hW n p.2).mpr ⟨t, ht, sub_eq_zero.mp he⟩)
  have he : ∀ᶠ q in 𝓝 p, ∀ t ∈ Icc (0 : ℝ) 1,
      (q.2 - tauN q.1 n)^2 - (t : ℂ)^2 * gamma2 q.1 n / 4 ≠ 0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hprojection : Continuous (fun q : (PotPair × ℂ) × ℝ => q.1.1) :=
      (continuous_fst : Continuous (fun r : PotPair × ℂ => r.1)).comp
        (continuous_fst : Continuous (fun q : (PotPair × ℂ) × ℝ => q.1))
    have hτouter : ContinuousAt (fun φ : PotPair => tauN φ n) p.1 :=
      (tauN_analytic n p.1 hW).continuousAt
    have hgouter : ContinuousAt (fun φ : PotPair => gamma2 φ n) p.1 :=
      (gamma2_analytic n p.1 hW).continuousAt
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

theorem isOpen_a5OmittedRootDomain38 (n : ℤ) : IsOpen (a5OmittedRootDomain38 n) := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨V, hV, hVW, _hVo, _hVc, C, R, c, N, hgeom, hspec⟩ :=
    local_isolatingFamily_common38 p.1 hp.1
  obtain ⟨J, hJ⟩ := rootDomain_far_exclusion38 (‖p.2‖ + 1)
  let M : ℕ := max N J
  have hhead : ∀ᶠ q in 𝓝 p, ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      m ≠ n → q.1 ∈ gkW → q.2 ∉ segment ℝ (lamMinus q.1 m) (lamPlus q.1 m) :=
    (Finset.Icc (-(M : ℤ)) (M : ℤ)).eventually_all.mpr (fun m _ => by
      by_cases hmn : m = n
      · exact Filter.Eventually.of_forall (fun _ hne => False.elim (hne hmn))
      · filter_upwards [a5CutComplement_eventually38 p hp.1 m (hp.2 m hmn)] with q hq _
        exact hq)
  have hpot : ∀ᶠ q : PotPair × ℂ in 𝓝 p, q.1 ∈ V :=
    continuous_fst.continuousAt.preimage_mem_nhds hV
  have hz : ∀ᶠ q : PotPair × ℂ in 𝓝 p, ‖q.2‖ < ‖p.2‖ + 1 :=
    continuous_snd.norm.continuousAt.eventually_lt_const (by linarith)
  filter_upwards [hhead, hpot, hz] with q hq hqV hqz
  refine ⟨hVW hqV, fun m hmn hseg => ?_⟩
  by_cases hsmall : |m| ≤ (M : ℤ)
  · exact hq m (Finset.mem_Icc.mpr (abs_le.mp hsmall)) hmn (hVW hqV) hseg
  · have hM : (M : ℤ) < |m| := lt_of_not_ge hsmall
    have hN : (N : ℤ) < |m| := lt_of_le_of_lt (by exact_mod_cast le_max_left N J) hM
    have hJ' : (J : ℤ) < |m| := lt_of_le_of_lt (by exact_mod_cast le_max_right N J) hM
    have hcut := (hspec q.1 hqV).1 m |>.1 hseg
    obtain ⟨hc, hr, _⟩ := hgeom.2.2.2.2 m hN
    rw [hc, hr] at hcut
    exact hJ m hJ' q.2 hqz hcut

theorem a5OmittedRootFactor_analytic38 (n m : ℤ) :
    AnalyticOnNhd ℂ (a5OmittedRootFactor38 n m) (a5OmittedRootDomain38 n) := by
  intro p hp
  by_cases hmn : m = n
  · have he : a5OmittedRootFactor38 n m = fun _ => (1 : ℂ) := by
      funext q
      simp [a5OmittedRootFactor38, hmn]
    rw [he]
    exact analyticAt_const
  · have he : a5OmittedRootFactor38 n m = rootFactor38 m := by
      funext q
      simp [a5OmittedRootFactor38, hmn]
    rw [he]
    exact a5RootFactor_analyticAt38 m p hp.1 (hp.2 m hmn)

theorem a5OmittedRootFactor_ne_zero38 (n m : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ a5OmittedRootDomain38 n) : a5OmittedRootFactor38 n m p ≠ 0 := by
  by_cases hmn : m = n
  · simp [a5OmittedRootFactor38, hmn]
  · simpa only [a5OmittedRootFactor38, ite_eq_right hmn] using
      a5RootFactor_ne_zero38 m p hp.1 (hp.2 m hmn)

theorem a5RootFactor_global_head_bound38 (p : PotPair × ℂ) 
    {D G R : ℝ} (_hD : 0 ≤ D) (hG : 0 ≤ G) (_hR : 0 ≤ R) (M : ℕ)
    (hδ : ∀ n : ℤ, ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ n : ℤ, ‖gamma2 p.1 n‖ ≤ G) (hz : ‖p.2‖ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (hM : |n| ≤ (M : ℤ)) :
    ‖rootFactor38 n p‖ ≤ ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1 := by
  have hw : ‖tauN p.1 n - p.2‖ ≤ (M : ℝ) * Real.pi + D + R := by
    have hc := countingCenter_low_norm38 hM
    have he : tauN p.1 n - p.2 =
      (tauN p.1 n - countingCenter38 n) + countingCenter38 n - p.2 := by ring
    rw [he]
    calc
      _ ≤ ‖(tauN p.1 n - countingCenter38 n) + countingCenter38 n‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ ‖tauN p.1 n - countingCenter38 n‖ + ‖countingCenter38 n‖ + ‖p.2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (M : ℝ) * Real.pi + D + R := by
        dsimp [countingCenter38] at hc ⊢
        linarith [hδ n]
  have hs : ‖stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2‖ ≤
      ‖tauN p.1 n - p.2‖^2 + ‖gamma2 p.1 n‖ / 4 + 1 := by
    by_cases hm : tauN p.1 n - p.2 = 0
    · simp only [stdRoot38, hm, zero_mul, norm_zero]
      positivity
    · exact stdRoot_norm_le38 hm
  have hs' : ‖stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2‖ ≤
      ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1 := by
    have hw2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    linarith [hg n]
  rw [rootFactor38, norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (root_piN_norm_ge_one38 n hn))).mpr
  have hP : 0 ≤ ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1 := by positivity
  exact hs'.trans (le_mul_of_one_le_right hP (root_piN_norm_ge_one38 n hn))

theorem a5OmittedRootFactor_head_bound38 (n : ℤ) (p : PotPair × ℂ)
    {D G R : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hR : 0 ≤ R) (M : ℕ)
    (hδ : ∀ m : ℤ, ‖tauN p.1 m - (m : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ m : ℤ, ‖gamma2 p.1 m‖ ≤ G) (hz : ‖p.2‖ ≤ R)
    (m : ℤ) (hm : m ≠ 0) (hM : |m| ≤ (M : ℤ)) :
    ‖a5OmittedRootFactor38 n m p‖ ≤ ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1 := by
  by_cases hmn : m = n
  · simp only [a5OmittedRootFactor38, ite_eq_left hmn, norm_one]
    have h0 : 0 ≤ ((M : ℝ) * Real.pi + D + R)^2 + G / 4 := by positivity
    linarith
  · simpa only [a5OmittedRootFactor38, ite_eq_right hmn] using
      a5RootFactor_global_head_bound38 p hD hG hR M hδ hg hz m hm hM

theorem a5Omitted_pair_head_bound38 (n : ℤ) (p : PotPair × ℂ) 
    {D G R : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hR : 0 ≤ R) (M : ℕ)
    (hδ : ∀ n : ℤ, ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ n : ℤ, ‖gamma2 p.1 n‖ ≤ G) (hz : ‖p.2‖ ≤ R)
    (m : ℕ) (hM : m + 1 ≤ M) :
    ‖Lib.pairDev (fun m => a5OmittedRootFactor38 n m p) m‖ ≤
      ((((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1)^2 + 1) *
        (M : ℝ)^2 / ((m : ℝ) + 1)^2 := by
  let A : ℝ := ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpos := a5OmittedRootFactor_head_bound38 n p hD hG hR M hδ hg hz ((m : ℤ) + 1)
    (by omega) (by rw [abs_of_nonneg (by omega)]; exact_mod_cast hM)
  have hneg := a5OmittedRootFactor_head_bound38 n p hD hG hR M hδ hg hz (-((m : ℤ) + 1))
    (by omega) (by rw [abs_neg, abs_of_nonneg (by omega)]; exact_mod_cast hM)
  change ‖a5OmittedRootFactor38 n ((m : ℤ) + 1) p‖ ≤ A at hpos
  change ‖a5OmittedRootFactor38 n (-((m : ℤ) + 1)) p‖ ≤ A at hneg
  have hb : ‖Lib.pairDev (fun m => a5OmittedRootFactor38 n m p) m‖ ≤ A^2 + 1 := by
    unfold Lib.pairDev
    calc
      _ ≤ ‖a5OmittedRootFactor38 n ((m : ℤ) + 1) p * a5OmittedRootFactor38 n (-((m : ℤ) + 1)) p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ A^2 + 1 := by
        rw [norm_mul, norm_one, pow_two]
        exact add_le_add (mul_le_mul hpos hneg (norm_nonneg _) hA) le_rfl
  apply hb.trans
  apply (le_div_iff₀ (by positivity : 0 < ((m : ℝ) + 1)^2)).mpr
  have ht : (m : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hs : ((m : ℝ) + 1)^2 ≤ (M : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem a5Omitted_pair_common_bound38 (n : ℤ) (p : PotPair × ℂ) 
    {D G R : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hR : 0 ≤ R) (M : ℕ)
    (hsep : 2 * (D + R) ≤ (M : ℝ) * Real.pi) (hnM : n.natAbs ≤ M)
    (hδ : ∀ n : ℤ, ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ n : ℤ, ‖gamma2 p.1 n‖ ≤ G) (hz : ‖p.2‖ ≤ R) (m : ℕ) :
    ‖Lib.pairDev (fun m => a5OmittedRootFactor38 n m p) m‖ ≤
      Lib.pairMaj (rootTauQ38 p) (rootPairRadius38 R (rootPairS38 D G R M)) m := by
  rw [root_pairMaj_absorb38 _ _ (rootPairS_nonneg38 hG M)]
  have hmaj : 0 ≤ Lib.pairMaj (rootTauQ38 p) R m := by
    unfold Lib.pairMaj
    exact add_nonneg (mul_nonneg Lib.majC1_nonneg
      (add_nonneg (rootTauQ_nonneg38 _ _) (rootTauQ_nonneg38 _ _)))
      (mul_nonneg (Lib.majC2_nonneg R) (by positivity))
  by_cases hM : m + 1 ≤ M
  · have hb := a5Omitted_pair_head_bound38 n p hD hG hR M hδ hg hz m hM
    have hs : ((((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1)^2 + 1) * (M : ℝ)^2 ≤
        rootPairS38 D G R M := by
      dsimp [rootPairS38]
      linarith [rootGapPairC_nonneg38 hG]
    exact hb.trans ((div_le_div_of_nonneg_right hs (by positivity)).trans (le_add_of_nonneg_left hmaj))
  · have ht : (M : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : M ≤ m + 1)
    have hpos : ((m : ℤ) + 1) ≠ n := by
      intro he
      have hn : n.natAbs = m + 1 := by omega
      omega
    have hneg : (-((m : ℤ) + 1)) ≠ n := by
      intro he
      have hn : n.natAbs = m + 1 := by omega
      omega
    have heq : Lib.pairDev (fun j => a5OmittedRootFactor38 n j p) m =
        Lib.pairDev (fun j => rootFactor38 j p) m := by
      simp only [Lib.pairDev, a5OmittedRootFactor38, ite_eq_right hpos, ite_eq_right hneg]
    rw [heq]
    have hb := root_pair_tail_bound38 p hG hδ hg hz m
      (hsep.trans (mul_le_mul_of_nonneg_right ht Real.pi_pos.le))
    have hs : rootGapPairC38 G ≤ rootPairS38 D G R M := by
      dsimp [rootPairS38]
      have hH : 0 ≤ ((((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1)^2 + 1) * (M : ℝ)^2 := by positivity
      linarith
    exact hb.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hs (by positivity)))

theorem a5Omitted_rootTauQ_line_majorant38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ (a5OmittedRootDomain38 n))
    (h : PotPair × ℂ) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ q : ℤ → ℝ, Summable q ∧
      ∀ ζ : ℂ, ‖ζ‖ < ρ → p + ζ • h ∈ (a5OmittedRootDomain38 n) →
        ∀ n : ℤ, rootTauQ38 (p + ζ • h) n ≤ q n := by
  obtain ⟨A, hAv, hAa⟩ := rootTau_l2_analytic38
  let L : ℂ → PotPair := fun ζ => p.1 + ζ • h.1
  have hL : ∀ ζ, AnalyticAt ℂ L ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hW : IsOpen {ζ : ℂ | L ζ ∈ gkW} :=
    isOpen_gkW.preimage (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW 0 (by simpa [L] using hp.1)
  have ha : AnalyticOnNhd ℂ (fun ζ => A (L ζ)) (ball 0 r) := by
    intro ζ hζ
    exact (hAa (L ζ) (hball hζ)).comp (hL ζ)
  obtain ⟨q, hq, hbound⟩ := Lib.summable_sup_sq_of_analytic (fun ζ => A (L ζ)) r ha
    (ρ' := r / 2) ⟨by linarith, by linarith⟩
  refine ⟨r / 2, by linarith, q, hq, fun ζ hζ hζW n => ?_⟩
  have h := hbound ζ (mem_ball_zero_iff.mpr hζ) n
  rw [hAv (L ζ) (by simpa [L] using hζW.1) n] at h
  exact h

theorem a5Omitted_rootTauQ_local_mass38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ (a5OmittedRootDomain38 n)) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ q ∈ ball p r, q ∈ (a5OmittedRootDomain38 n) →
      Summable (rootTauQ38 q) ∧ (∑' n : ℤ, rootTauQ38 q n) ≤ B := by
  obtain ⟨V, hV, B, hB⟩ := (tauGamma_l2 p.1 hp.1).1
  have hprod : {q : PotPair × ℂ | q.1 ∈ V} ∈ 𝓝 p :=
    continuous_fst.continuousAt.preimage_mem_nhds hV
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hprod
  exact ⟨r, hr, B, fun q hq _ => hB q.1 (hsub hq)⟩

theorem a5Omitted_pair_local_bound38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ (a5OmittedRootDomain38 n)) :
    ∃ r : ℝ, 0 < r ∧ ∃ R' : ℝ, ∀ q ∈ ball p r, q ∈ (a5OmittedRootDomain38 n) → ∀ m : ℕ,
      ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) m‖ ≤ Lib.pairMaj (rootTauQ38 q) R' m := by
  obtain ⟨V, hV, _hVW, D, G, hD, hG, hcoord⟩ := root_common_coordinates38 p.1 hp.1
  let R : ℝ := ‖p.2‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpot : ∀ᶠ q : PotPair × ℂ in 𝓝 p, q.1 ∈ V :=
    continuous_fst.continuousAt.preimage_mem_nhds hV
  have hz : ∀ᶠ q : PotPair × ℂ in 𝓝 p, ‖q.2‖ < R :=
    continuous_snd.norm.continuousAt.eventually_lt_const (by dsimp [R]; linarith)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hpot.and hz)
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * (D + R) / Real.pi)
  let M := max J n.natAbs
  have hsep : 2 * (D + R) ≤ (M : ℝ) * Real.pi := by
    apply (le_of_lt ((div_lt_iff₀ Real.pi_pos).mp hJ)).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left J n.natAbs) Real.pi_pos.le
  refine ⟨r, hr, rootPairRadius38 R (rootPairS38 D G R M), fun q hq hqU m => ?_⟩
  have hqdata := hsub hq
  exact a5Omitted_pair_common_bound38 n q hD hG hR M hsep (le_max_right J n.natAbs)
    (fun n => (hcoord q.1 hqdata.1 n).1) (fun n => (hcoord q.1 hqdata.1 n).2)
    hqdata.2.le m

theorem a5Omitted_pair_summable38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ (a5OmittedRootDomain38 n)) :
    Summable (fun m : ℕ => ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j p) m‖) := by
  obtain ⟨r, hr, R, hb⟩ := a5Omitted_pair_local_bound38 n p hp
  obtain ⟨s, hs, B, hmass⟩ := a5Omitted_rootTauQ_local_mass38 n p hp
  have hQ := (hmass p (mem_ball_self hs) hp).1
  exact (Lib.summable_pairMaj hQ R).of_nonneg_of_le (fun _ => norm_nonneg _)
    (hb p (mem_ball_self hr) hp)

theorem a5OmittedRoot_multipliable38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ (a5OmittedRootDomain38 n)) :
    Multipliable (fun j => a5OmittedRootFactor38 n j p) (symmetricIcc ℤ) :=
  Lib.multipliable_symm_of_summable_pairDev (a5Omitted_pair_summable38 n p hp)

theorem a5Omitted_line_majorant38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ (a5OmittedRootDomain38 n))
    (h : PotPair × ℂ) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ q : ℕ → ℝ, Summable q ∧
      ∀ ζ : ℂ, ‖ζ‖ < ρ → p + ζ • h ∈ (a5OmittedRootDomain38 n) → ∀ m : ℕ,
        ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j (p + ζ • h)) m‖ ≤ q m := by
  obtain ⟨r, hr, R, hb⟩ := a5Omitted_pair_local_bound38 n p hp
  obtain ⟨ρ, hρ, q, hq, hQ⟩ := a5Omitted_rootTauQ_line_majorant38 n p hp h
  refine ⟨min ρ (r / (‖h‖ + 1)), lt_min hρ (by positivity), Lib.pairMaj q R,
    Lib.summable_pairMaj hq R, fun ζ hζ hζU m => ?_⟩
  have hζρ : ‖ζ‖ < ρ := hζ.trans_le (min_le_left _ _)
  have hζr : ‖ζ‖ < r / (‖h‖ + 1) := hζ.trans_le (min_le_right _ _)
  have hball : p + ζ • h ∈ ball p r := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖ζ‖ * (‖h‖ + 1) < r := (lt_div_iff₀ (by positivity)).mp hζr
    nlinarith [norm_nonneg ζ, norm_nonneg h]
  exact (hb _ hball hζU m).trans (Lib.pairMaj_mono (hQ ζ hζρ hζU) R m)

theorem a5Omitted_local_mass38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ (a5OmittedRootDomain38 n)) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ q ∈ ball p r, q ∈ (a5OmittedRootDomain38 n) →
      Summable (fun m : ℕ => ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) m‖) ∧
        (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) m‖) ≤ B := by
  obtain ⟨r, hr, R, hb⟩ := a5Omitted_pair_local_bound38 n p hp
  obtain ⟨s, hs, B, hQ⟩ := a5Omitted_rootTauQ_local_mass38 n p hp
  refine ⟨min r s, lt_min hr hs, 2 * Lib.majC1 * B + Lib.majC2 R * Lib.sumInvSq,
    fun q hq hqU => ?_⟩
  have hqr := ball_subset_ball (min_le_left r s) hq
  have hqs := ball_subset_ball (min_le_right r s) hq
  obtain ⟨hQsum, hQbound⟩ := hQ q hqs hqU
  have hsum := a5Omitted_pair_summable38 n q hqU
  refine ⟨hsum, ?_⟩
  refine (Summable.tsum_le_tsum (hb q hqr hqU) hsum (Lib.summable_pairMaj hQsum R)).trans ?_
  refine (Lib.tsum_pairMaj_le hQsum (rootTauQ_nonneg38 q) R).trans ?_
  have h1 := Lib.majC1_nonneg
  nlinarith

theorem a5OmittedRoot_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (a5OmittedRootProduct38 n) (a5OmittedRootDomain38 n) := by
  exact Lib.analyticOnNhd_symm_tprod (isOpen_a5OmittedRootDomain38 n)
    (a5OmittedRootFactor_analytic38 n) (a5Omitted_line_majorant38 n) (fun p hp => by
      obtain ⟨r, hr, B, hb⟩ := a5Omitted_local_mass38 n p hp
      exact ⟨r, hr, B, fun q hq hqU => (hb q hq hqU).2⟩)

theorem a5OmittedRoot_ne_zero38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ a5OmittedRootDomain38 n) : a5OmittedRootProduct38 n p ≠ 0 := by
  intro he
  obtain ⟨m, hm⟩ := (Lib.tprod_symm_eq_zero_iff (a5Omitted_pair_summable38 n p hp)).mp he
  exact a5OmittedRootFactor_ne_zero38 n m p hp hm

/-- Genuine symmetric convergence precedes deletion of the one normalized factor. -/
theorem a5CanonRoot_omitted_factorization38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ rootDomain38) :
    canonRoot38 p.1 p.2 = 2 * Complex.I * rootFactor38 n p * a5OmittedRootProduct38 n p := by
  classical
  have hp' : p ∈ a5OmittedRootDomain38 n :=
    ⟨hp.1, fun m _ => rootDomain_avoids38 hp m⟩
  have hu : Function.update (fun m => rootFactor38 m p) n 1 =
      fun m => a5OmittedRootFactor38 n m p := by
    funext m
    simp [Function.update, a5OmittedRootFactor38]
  have hmu : Multipliable (Function.update (fun m => rootFactor38 m p) n 1)
      (symmetricIcc ℤ) := by
    rw [hu]
    exact a5OmittedRoot_multipliable38 n p hp'
  have he : (∏'[symmetricIcc ℤ] m : ℤ, rootFactor38 m p) =
      rootFactor38 n p * a5OmittedRootProduct38 n p :=
    Multipliable.tprod_eq_mul_tprod_ite' n hmu
  rw [canonRoot38, he]
  ring

/-- Every free collapsed gap centre lies on the enlarged actual domain. -/
theorem a5OmittedRoot_free_center_mem38 (n : ℤ) :
    ((0 : PotPair), countingCenter38 n) ∈ a5OmittedRootDomain38 n := by
  have hW : (0 : PotPair) ∈ gkW := by
    simpa only [realSlice_zero] using realSlice_mem_gkW (0 : PhysicalL2)
  refine ⟨hW, fun m hmn hseg => ?_⟩
  rw [lamMinus_zero38, lamPlus_zero38, segment_same] at hseg
  have he : countingCenter38 n = countingCenter38 m := Set.mem_singleton_iff.mp hseg
  change (n : ℂ) * (Real.pi : ℂ) = (m : ℂ) * (Real.pi : ℂ) at he
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : n = m := Int.cast_injective (mul_right_cancel₀ hpi he)
  exact hmn hn.symm

/-- This is genuinely through the omitted slit, where the full canonical-root domain fails. -/
theorem a5OmittedRoot_free_center_probe38 (n : ℤ) :
    AnalyticAt ℂ (a5OmittedRootProduct38 n) ((0 : PotPair), countingCenter38 n) ∧
      a5OmittedRootProduct38 n ((0 : PotPair), countingCenter38 n) ≠ 0 ∧
      ((0 : PotPair), countingCenter38 n) ∉ rootDomain38 := by
  have hp := a5OmittedRoot_free_center_mem38 n
  refine ⟨a5OmittedRoot_analytic38 n _ hp, a5OmittedRoot_ne_zero38 n _ hp, ?_⟩
  intro hfull
  apply hfull.2
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  rw [lamMinus_zero38, lamPlus_zero38, segment_same]
  exact Set.mem_singleton _

end
end NlsGge.GK38
