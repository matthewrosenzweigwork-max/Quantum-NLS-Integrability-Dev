import Mathlib
import NlsGge.Atomic.M.M011Support1

                                                                                                                 
                                                                                                                    
                                                                                                                           
                                                                                                                     
                                                                                                          
                                                                                                                
                                                                                                                 
                                                                                                                        
                            
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M011Aux
noncomputable section

open NlsGge.ThirdConsultation.MPrimitive

def halfGap0 (φ : PotPair) : ℂ := (lamPlus φ 0 - lamMinus φ 0) / 2

def gapRatio (φ ψ : PotPair) : ℂ := gamma2 ψ 0 / gamma2 φ 0

/-- Analytic branch of the half gap near `φ`. -/
def halfBranch (φ ψ : PotPair) : ℂ := halfGap0 φ * gapRatio φ ψ ^ (2⁻¹ : ℂ)

/-- Parametric Joukowski map. -/
def JJ (φ : PotPair) (q : PotPair × ℂ) : ℂ := MContour.jouk (tauN q.1 0) (halfBranch φ q.1) q.2

/-- Model integrand: numerator over the omitted root product. -/
def BB (φ : PotPair) (q : PotPair × ℂ) : ℂ :=
  (Lib.piN 0 : ℂ) * deriv (discrim q.1) (JJ φ q) /
    (2 * Complex.I * a5OmittedRootProduct38 0 (q.1, JJ φ q))

theorem halfBranch_sq {φ ψ : PotPair} (hφ : φ ∈ gkW) (hψ : ψ ∈ gkW) (hg : gamma2 φ 0 ≠ 0) :
    (2 * halfBranch φ ψ) ^ 2 = (lamPlus ψ 0 - lamMinus ψ 0) ^ 2 := by
  have h1 : (gapRatio φ ψ ^ (2⁻¹ : ℂ)) ^ 2 = gapRatio φ ψ := Complex.cpow_ofNat_inv_pow _ 2
  have h2 : gamma2 φ 0 = (lamPlus φ 0 - lamMinus φ 0) ^ 2 := gamma2_value38 φ hφ 0
  calc (2 * halfBranch φ ψ) ^ 2
      = (lamPlus φ 0 - lamMinus φ 0) ^ 2 * (gapRatio φ ψ ^ (2⁻¹ : ℂ)) ^ 2 := by
        unfold halfBranch halfGap0; ring
    _ = gamma2 φ 0 * (gamma2 ψ 0 / gamma2 φ 0) := by rw [h1, ← h2, gapRatio]
    _ = gamma2 ψ 0 := by field_simp
    _ = _ := gamma2_value38 ψ hψ 0

theorem halfBranch_ends {φ ψ : PotPair} (hφ : φ ∈ gkW) (hψ : ψ ∈ gkW) (hg : gamma2 φ 0 ≠ 0) :
    (tauN ψ 0 - halfBranch φ ψ = lamMinus ψ 0 ∧ tauN ψ 0 + halfBranch φ ψ = lamPlus ψ 0) ∨
    (tauN ψ 0 - halfBranch φ ψ = lamPlus ψ 0 ∧ tauN ψ 0 + halfBranch φ ψ = lamMinus ψ 0) := by
  have hτ := tauN_value38 ψ hψ 0
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (halfBranch_sq hφ hψ hg) with h | h
  · exact Or.inl ⟨by linear_combination hτ - h / 2, by linear_combination hτ + h / 2⟩
  · exact Or.inr ⟨by linear_combination hτ - h / 2, by linear_combination hτ + h / 2⟩

theorem segment_eq_ends {φ ψ : PotPair} (hφ : φ ∈ gkW) (hψ : ψ ∈ gkW) (hg : gamma2 φ 0 ≠ 0) :
    segment ℝ (lamMinus ψ 0) (lamPlus ψ 0) =
      segment ℝ (tauN ψ 0 - halfBranch φ ψ) (tauN ψ 0 + halfBranch φ ψ) := by
  rcases halfBranch_ends hφ hψ hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, segment_symm]

theorem halfBranch_ne {φ ψ : PotPair} (hgap : lamPlus φ 0 - lamMinus φ 0 ≠ 0)
    (hslit : gapRatio φ ψ ∈ Complex.slitPlane) : halfBranch φ ψ ≠ 0 := by
  refine mul_ne_zero (div_ne_zero hgap two_ne_zero) ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => Complex.slitPlane_ne_zero hslit h.1

theorem halfBranch_analyticAt {φ ψ : PotPair} (hψ : ψ ∈ gkW)
    (hslit : gapRatio φ ψ ∈ Complex.slitPlane) : AnalyticAt ℂ (halfBranch φ) ψ := by
  have hr : AnalyticAt ℂ (gapRatio φ) ψ := (gamma2_analytic 0 ψ hψ).div analyticAt_const
    (fun h => by
      have : gapRatio φ ψ = 0 := by rw [gapRatio, h, div_zero]
      exact Complex.slitPlane_ne_zero hslit this)
  exact analyticAt_const.mul (hr.cpow analyticAt_const hslit)

theorem JJ_analyticAt {φ : PotPair} {q : PotPair × ℂ} (hq : q.1 ∈ gkW)
    (hslit : gapRatio φ q.1 ∈ Complex.slitPlane) : AnalyticAt ℂ (JJ φ) q := by
  have h1 : AnalyticAt ℂ (fun p : PotPair × ℂ => tauN p.1 0) q :=
    (tauN_analytic 0 q.1 hq).comp analyticAt_fst
  have h2 : AnalyticAt ℂ (fun p : PotPair × ℂ => halfBranch φ p.1) q :=
    (halfBranch_analyticAt hq hslit).comp analyticAt_fst
  have h3 : AnalyticAt ℂ (fun p : PotPair × ℂ => Complex.cosh p.2) q :=
    Complex.analyticAt_cosh.comp analyticAt_snd
  have e : JJ φ = fun p : PotPair × ℂ => tauN p.1 0 - halfBranch φ p.1 * Complex.cosh p.2 := rfl
  rw [e]
  exact h1.sub (h2.mul h3)

theorem sinh_ne_zero_of_re_pos {v : ℂ} (hv : 0 < v.re) : Complex.sinh v ≠ 0 := by
  intro hs
  have h1 : (Complex.cosh v - 1) * (Complex.cosh v + 1) = 0 := by
    have := Complex.cosh_sq v
    rw [hs] at this
    linear_combination this
  rcases mul_eq_zero.1 h1 with h | h
  · exact MContour.cosh_not_unit_real hv 1 (by simp) (by simpa [sub_eq_zero] using h)
  · exact MContour.cosh_not_unit_real hv (-1) (by simp) (by
      have : Complex.cosh v = -1 := by linear_combination h
      simpa using this)

/-- One common isolating family and one product ball around `(φ, 0)`. -/
theorem local_setup (φ : PotPair) (hφ : φ ∈ gkW) (hg : gamma2 φ 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∀ ψ ∈ ball φ ε, ψ ∈ gkW ∧ IsolatingFamily38 ψ C R ∧ gapRatio φ ψ ∈ Complex.slitPlane ∧
        ∀ v ∈ ball (0 : ℂ) ε, JJ φ (ψ, v) ∈ ball (C 0) (R 0) := by
  obtain ⟨V0, hV0, hV0W, -, -, C, R, hfam⟩ := local_isolatingFamily φ hφ
  have hr1 : gapRatio φ φ = 1 := div_self hg
  have hslit1 : gapRatio φ φ ∈ Complex.slitPlane := by rw [hr1]; exact Complex.one_mem_slitPlane
  have hrc : ContinuousAt (gapRatio φ) φ :=
    ((gamma2_analytic 0 φ hφ).div analyticAt_const hg).continuousAt
  have hJc : ContinuousAt (JJ φ) (φ, 0) := (JJ_analyticAt (q := (φ, 0)) hφ hslit1).continuousAt
  have hJ0 : JJ φ (φ, 0) = lamMinus φ 0 := by
    have hτ := tauN_value38 φ hφ 0
    show tauN φ 0 - halfGap0 φ * gapRatio φ φ ^ (2⁻¹ : ℂ) * Complex.cosh 0 = lamMinus φ 0
    rw [hr1, Complex.one_cpow, Complex.cosh_zero, hτ, halfGap0]
    ring
  have hmem : JJ φ (φ, 0) ∈ ball (C 0) (R 0) := by
    rw [hJ0]
    exact Support3Aux.cut_sub_ball (hfam φ (mem_of_mem_nhds hV0)) 0 (left_mem_segment ℝ _ _)
  have e1 : ∀ᶠ q : PotPair × ℂ in 𝓝 (φ, 0), q.1 ∈ V0 :=
    continuousAt_fst.preimage_mem_nhds hV0
  have e2 : ∀ᶠ q : PotPair × ℂ in 𝓝 (φ, 0), gapRatio φ q.1 ∈ Complex.slitPlane :=
    (ContinuousAt.comp (g := gapRatio φ) (f := Prod.fst) (x := ((φ, (0 : ℂ)) : PotPair × ℂ)) hrc
      continuousAt_fst).preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hslit1)
  have e3 : ∀ᶠ q : PotPair × ℂ in 𝓝 (φ, 0), JJ φ q ∈ ball (C 0) (R 0) :=
    hJc.preimage_mem_nhds (isOpen_ball.mem_nhds hmem)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  refine ⟨ε, hε, C, R, fun ψ hψ => ?_⟩
  have hq : ∀ v ∈ ball (0 : ℂ) ε, (ψ, v) ∈ ball (φ, (0 : ℂ)) ε := fun v hv => by
    rw [← ball_prod_same]; exact ⟨hψ, hv⟩
  obtain ⟨h1, h2, -⟩ := hball _ (hq 0 (mem_ball_self hε))
  exact ⟨hV0W h1, hfam ψ h1, h2, fun v hv => (hball _ (hq v hv)).2.2⟩

/-- **Base step.** At a noncollapsed base gap some cut-free point has a local analytic representative. -/
theorem base_good (φ : PotPair) (hφ : φ ∈ gkW) (hgap : lamPlus φ 0 - lamMinus φ 0 ≠ 0) :
    ∃ z1 : ℂ, z1 ∈ cutFreeFiber φ ∧ Good φ z1 := by
  have hg : gamma2 φ 0 ≠ 0 := by rw [gamma2_value38 φ hφ 0]; exact pow_ne_zero 2 hgap
  obtain ⟨ε, hε, C, R, hloc⟩ := local_setup φ hφ hg
  set V : Set PotPair := ball φ ε with hVdef
  set W : Set ℂ := ball (0 : ℂ) ε with hWdef
  have hVW : ∀ q ∈ V ×ˢ W, q.1 ∈ gkW ∧ IsolatingFamily38 q.1 C R ∧
      gapRatio φ q.1 ∈ Complex.slitPlane ∧ JJ φ q ∈ ball (C 0) (R 0) := fun q hq =>
    ⟨(hloc q.1 hq.1).1, (hloc q.1 hq.1).2.1, (hloc q.1 hq.1).2.2.1, (hloc q.1 hq.1).2.2.2 q.2 hq.2⟩
  have hJan : AnalyticOnNhd ℂ (JJ φ) (V ×ˢ W) := fun q hq =>
    JJ_analyticAt (hVW q hq).1 (hVW q hq).2.2.1
  have hbc : ContinuousOn (halfBranch φ) V := fun ψ hψ =>
    (halfBranch_analyticAt (hloc ψ hψ).1 (hloc ψ hψ).2.2.1).continuousAt.continuousWithinAt
  have homit : ∀ q ∈ V ×ˢ W, (q.1, JJ φ q) ∈ a5OmittedRootDomain38 0 := by
    intro q hq
    obtain ⟨hW, hf, -, hJ⟩ := hVW q hq
    exact ⟨hW, fun m hm hseg =>
      Support3Aux.balls_disjoint hf hm (Support3Aux.cut_sub_ball hf m hseg) hJ⟩
  have hBan : AnalyticOnNhd ℂ (BB φ) (V ×ˢ W) := by
    intro q hq
    have hpair : AnalyticAt ℂ (fun p : PotPair × ℂ => (p.1, JJ φ p)) q :=
      analyticAt_fst.prod (hJan q hq)
    have hD : AnalyticAt ℂ (fun p : PotPair × ℂ => deriv (discrim p.1) (JJ φ p)) q :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => deriv (discrim p.1) p.2)
        (f := fun p : PotPair × ℂ => (p.1, JJ φ p))
        (analyticOnNhd_discrimDeriv_joint38 _ (mem_univ _)) hpair
    have hP : AnalyticAt ℂ (fun p : PotPair × ℂ => a5OmittedRootProduct38 0 (p.1, JJ φ p)) q :=
      AnalyticAt.comp (g := a5OmittedRootProduct38 0) (f := fun p : PotPair × ℂ => (p.1, JJ φ p))
        (a5OmittedRoot_analytic38 0 _ (homit q hq)) hpair
    show AnalyticAt ℂ (fun p : PotPair × ℂ => (Lib.piN 0 : ℂ) * deriv (discrim p.1) (JJ φ p) /
      (2 * Complex.I * a5OmittedRootProduct38 0 (p.1, JJ φ p))) q
    exact (analyticAt_const.mul hD).div (analyticAt_const.mul hP)
      (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
        (a5OmittedRoot_ne_zero38 0 _ (homit q hq)))
  have hroot : ∀ q ∈ V ×ˢ W, 0 < q.2.re → (q.1, JJ φ q) ∈ rootDomain38 := by
    intro q hq hre
    obtain ⟨hW, -, hslit, -⟩ := hVW q hq
    refine ⟨hW, fun hmem => ?_⟩
    simp only [gapSegments38, Set.mem_iUnion] at hmem
    obtain ⟨m, hm⟩ := hmem
    by_cases hm0 : m = 0
    · subst hm0
      rw [segment_eq_ends hφ hW hg] at hm
      exact MContour.jouk_notMem_segment (halfBranch_ne hgap hslit) hre hm
    · exact (homit q hq).2 m hm0 hm
  -- the constant root sign on the connected product neighbourhood
  set S : Set (PotPair × ℂ) := V ×ˢ (W ∩ {v : ℂ | 0 < v.re}) with hSdef
  have hSsub : ∀ q ∈ S, q ∈ V ×ˢ W ∧ 0 < q.2.re := fun q hq => ⟨⟨hq.1, hq.2.1⟩, hq.2.2⟩
  have hpi : (Lib.piN 0 : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero 0
  obtain ⟨σ, hσ2, hσ⟩ : ∃ σ : ℂ, σ ^ 2 = 1 ∧ ∀ q ∈ S,
      rootFactor38 0 (q.1, JJ φ q) * (Lib.piN 0 : ℂ) = σ * (halfBranch φ q.1 * Complex.sinh q.2) := by
    have hpre : IsPreconnected S :=
      (convex_ball φ ε).isPreconnected.prod
        ((convex_ball (0 : ℂ) ε).inter (convex_halfSpace_re_gt 0)).isPreconnected
    have hf : ContinuousOn (fun q : PotPair × ℂ => rootFactor38 0 (q.1, JJ φ q) * (Lib.piN 0 : ℂ)) S := by
      refine ContinuousOn.mul ?_ continuousOn_const
      exact (rootFactor_analytic38 0).continuousOn.comp
        (continuousOn_fst.prodMk (hJan.continuousOn.mono (fun q hq => (hSsub q hq).1)))
        (fun q hq => hroot q (hSsub q hq).1 (hSsub q hq).2)
    have hgc : ContinuousOn (fun q : PotPair × ℂ => halfBranch φ q.1 * Complex.sinh q.2) S :=
      (hbc.comp continuousOn_fst (fun q hq => hq.1)).mul
        (Complex.continuous_sinh.comp continuous_snd).continuousOn
    have hsq : EqOn ((fun q : PotPair × ℂ => rootFactor38 0 (q.1, JJ φ q) * (Lib.piN 0 : ℂ)) ^ 2)
        ((fun q : PotPair × ℂ => halfBranch φ q.1 * Complex.sinh q.2) ^ 2) S := by
      intro q hq
      obtain ⟨hqVW, hre⟩ := hSsub q hq
      have hp := hroot q hqVW hre
      have h := rootFactor_sq38 0 (q.1, JJ φ q) hp
      simp only at h
      have key : (rootFactor38 0 (q.1, JJ φ q) * (Lib.piN 0 : ℂ)) ^ 2 =
          (lamMinus q.1 0 - JJ φ q) * (lamPlus q.1 0 - JJ φ q) := by
        rw [mul_pow, h, div_mul_cancel₀ _ (pow_ne_zero 2 hpi)]
      simp only [Pi.pow_apply]
      rw [key]
      have hc := Complex.cosh_sq q.2
      have e : JJ φ q = tauN q.1 0 - halfBranch φ q.1 * Complex.cosh q.2 := rfl
      rw [e]
      rcases halfBranch_ends hφ (hVW q hqVW).1 hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; linear_combination (halfBranch φ q.1) ^ 2 * hc
      · rw [← h1, ← h2]; linear_combination (halfBranch φ q.1) ^ 2 * hc
    have hne : ∀ {q : PotPair × ℂ}, q ∈ S → halfBranch φ q.1 * Complex.sinh q.2 ≠ 0 := by
      intro q hq
      exact mul_ne_zero (halfBranch_ne hgap (hVW q (hSsub q hq).1).2.2.1)
        (sinh_ne_zero_of_re_pos (hSsub q hq).2)
    rcases hpre.eq_or_eq_neg_of_sq_eq hf hgc hsq hne with h | h
    · exact ⟨1, by norm_num, fun q hq => by simpa using h hq⟩
    · exact ⟨-1, by norm_num, fun q hq => by simpa using h hq⟩
  -- pointwise reduction `omega dz = -σ BB dv`
  have hred : ∀ q ∈ S, MContour.omega q.1 (JJ φ q) * (-(halfBranch φ q.1 * Complex.sinh q.2)) =
      -σ * BB φ q := by
    intro q hq
    obtain ⟨hqVW, hre⟩ := hSsub q hq
    have hp := hroot q hqVW hre
    have hfac := a5CanonRoot_omitted_factorization38 0 (q.1, JJ φ q) hp
    simp only at hfac
    have hrf0 : rootFactor38 0 (q.1, JJ φ q) ≠ 0 := rootFactor_ne_zero38 0 _ hp
    have hP0 : a5OmittedRootProduct38 0 (q.1, JJ φ q) ≠ 0 := a5OmittedRoot_ne_zero38 0 _ (homit q hqVW)
    have h := hσ q hq
    unfold MContour.omega BB
    rw [hfac]
    set rf := rootFactor38 0 (q.1, JJ φ q)
    set P := a5OmittedRootProduct38 0 (q.1, JJ φ q)
    set D' := deriv (discrim q.1) (JJ φ q)
    set s := Complex.sinh q.2
    set d := halfBranch φ q.1
    set pn : ℂ := (Lib.piN 0 : ℂ)
    have h2 : (2 * Complex.I * rf * P) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hrf0) hP0
    rw [div_mul_eq_mul_div, div_eq_iff h2]
    have e1 : pn * D' / (2 * Complex.I * P) * (2 * Complex.I * rf * P) = pn * D' * rf := by
      field_simp
    have e2 : -σ * (pn * D' / (2 * Complex.I * P)) * (2 * Complex.I * rf * P) =
        -σ * (pn * D' / (2 * Complex.I * P) * (2 * Complex.I * rf * P)) := by ring
    rw [e2, e1]
    linear_combination (σ * D') * h + (D' * d * s) * hσ2
  -- the endpoint path and its integral
  set δ' : ℝ := ε / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hmemVW : ∀ ψ ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, (ψ, (t : ℂ) * (δ' : ℂ)) ∈ V ×ˢ W := by
    intro ψ hψ t ht
    refine ⟨hψ, ?_⟩
    rw [hWdef, mem_ball_zero_iff, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ht.1, abs_of_pos hδ'0]
    nlinarith [ht.2]
  have hmemS : ∀ ψ ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1, (ψ, (t : ℂ) * (δ' : ℂ)) ∈ S := by
    intro ψ hψ t ht
    have h := hmemVW ψ hψ t (Ioc_subset_Icc_self ht)
    refine ⟨h.1, h.2, ?_⟩
    show 0 < ((t : ℂ) * (δ' : ℂ)).re
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_pos ht.1 hδ'0
  set kf : PotPair → ℝ → ℂ := fun ψ t => -σ * (BB φ (ψ, (t : ℂ) * (δ' : ℂ)) * (δ' : ℂ)) with hkf
  set G : PotPair → ℂ := fun ψ => ∫ t in (0 : ℝ)..1, kf ψ t with hG
  set a : PotPair → ℂ := fun ψ => JJ φ (ψ, (δ' : ℂ)) with ha
  have hGan : AnalyticOnNhd ℂ G V := by
    have hH : AnalyticOnNhd ℂ (fun q : PotPair × ℂ => -σ * (BB φ q * (δ' : ℂ))) (V ×ˢ W) :=
      fun q hq => analyticAt_const.mul ((hBan q hq).mul analyticAt_const)
    have hW' : ∀ u ∈ V, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
        (u, (fun _ : PotPair => (0 : ℂ)) u +
          (s : ℂ) * ((fun _ : PotPair => (δ' : ℂ)) u - (fun _ : PotPair => (0 : ℂ)) u)) ∈ V ×ˢ W := by
      intro u hu s hs
      simpa using hmemVW u hu s hs
    have := NlsGge.G4022Support.segment_integral_analytic isOpen_ball hH analyticOnNhd_const
      analyticOnNhd_const hW'
    simpa [hG, hkf] using this
  have haan : AnalyticOnNhd ℂ a V := by
    intro ψ hψ
    have hm1 : (ψ, (δ' : ℂ)) ∈ V ×ˢ W := by simpa using hmemVW ψ hψ 1 ⟨zero_le_one, le_rfl⟩
    exact AnalyticAt.comp (g := JJ φ) (f := fun ψ : PotPair => (ψ, (δ' : ℂ)))
      (hJan _ hm1) (analyticAt_id.prod analyticAt_const)
  -- identification with the landed primitive
  have hGval : ∀ ψ ∈ V, ∀ hp : ψ ∈ gkW ∧ a ψ ∈ endpointClosureFiber ψ,
      G ψ = M.primitive ⟨(ψ, a ψ), hp⟩ := by
    intro ψ hψ hp
    set c : ℝ → ℂ := fun t => JJ φ (ψ, (t : ℂ) * (δ' : ℂ)) with hc
    have hvd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) * (δ' : ℂ)) (δ' : ℂ) t := fun t => by
      simpa using (hasDerivAt_id t).ofReal_comp.mul_const (δ' : ℂ)
    have hcd : ∀ t : ℝ, HasDerivAt c ((δ' : ℂ) • (-(halfBranch φ ψ * Complex.sinh ((t : ℂ) * (δ' : ℂ))))) t :=
      fun t => by
        have h := (MContour.jouk_hasDerivAt (tauN ψ 0) (halfBranch φ ψ) ((t : ℂ) * (δ' : ℂ))).scomp t (hvd t)
        exact h
    have hvcd : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ) * (δ' : ℂ)) :=
      Complex.ofRealCLM.contDiff.mul contDiff_const
    have hccd : ContDiff ℝ 1 c := by
      have e : c = fun t : ℝ => tauN ψ 0 - halfBranch φ ψ * Complex.cosh ((t : ℂ) * (δ' : ℂ)) := rfl
      rw [e]
      exact contDiff_const.sub (contDiff_const.mul ((Complex.contDiff_cosh.restrict_scalars ℝ).comp hvcd))
    have hkc : ContinuousOn (kf ψ) (Icc (0 : ℝ) 1) := by
      refine continuousOn_const.mul (ContinuousOn.mul ?_ continuousOn_const)
      exact hBan.continuousOn.comp (continuousOn_const.prodMk hvcd.continuous.continuousOn)
        (fun t ht => hmemVW ψ hψ t ht)
    have hE : MContour.HasEndpointIntegral ψ c (∫ t in (0 : ℝ)..1, kf ψ t) := by
      refine hasEndpointIntegral_of_eq ψ c (kf ψ) hkc (fun t ht => ?_)
      rw [(hcd t).deriv, smul_eq_mul]
      have hr := hred (ψ, (t : ℂ) * (δ' : ℂ)) (hmemS ψ hψ t (Ioo_subset_Ioc_self ht))
      simp only at hr
      simp only [hkf, hc]
      linear_combination (δ' : ℂ) * hr
    obtain ⟨upper, hup⟩ : ∃ upper : Bool, baseEndpoint ψ upper = tauN ψ 0 - halfBranch φ ψ := by
      rcases halfBranch_ends hφ hp.1 hg with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨false, by rw [baseEndpoint_false, h1]⟩
      · exact ⟨true, by rw [baseEndpoint_true, h1]⟩
    have hadm : AdmissiblePrimitiveChain ψ (baseEndpoint ψ upper) (a ψ) 0 (fun _ => c) := by
      refine ⟨fun i => i.elim0, fun _ => ⟨hccd.continuous.continuousOn, hccd.contDiffOn⟩, ?_, ?_,
        Or.inl ⟨fun _ t ht => (hroot _ (hmemVW ψ hψ t (Ioo_subset_Icc_self ht))
          (hmemS ψ hψ t (Ioo_subset_Ioc_self ht)).2.2).2, fun i => i.elim0⟩⟩
      · show JJ φ (ψ, ((0 : ℝ) : ℂ) * (δ' : ℂ)) = baseEndpoint ψ upper
        rw [hup]
        show tauN ψ 0 - halfBranch φ ψ * Complex.cosh (((0 : ℝ) : ℂ) * (δ' : ℂ)) = _
        simp
      · show JJ φ (ψ, ((1 : ℝ) : ℂ) * (δ' : ℂ)) = JJ φ (ψ, (δ' : ℂ))
        simp
    obtain ⟨I, hI, hsum⟩ :=
      (symmetric_primitive_characterization ⟨(ψ, a ψ), hp⟩).2.2 upper 0 (fun _ => c) hadm
    rw [Fin.sum_univ_one] at hsum
    have h1 := MContour.HasEndpointIntegral.unique (hI 0) hE
    show G ψ = symmetricPrimitive _
    rw [← hsum, h1]
  -- transport from the moving point `a ψ` to the fixed point `z1 = a φ`
  have hφV : φ ∈ V := mem_ball_self hε
  have hz1 : (φ, a φ) ∈ rootDomain38 := by
    have h := hroot _ (hmemVW φ hφV 1 ⟨zero_le_one, le_rfl⟩)
      (hmemS φ hφV 1 ⟨zero_lt_one, le_rfl⟩).2.2
    show (φ, JJ φ (φ, (δ' : ℂ))) ∈ rootDomain38
    simpa using h
  obtain ⟨ε1, hε1, hball1⟩ := Metric.isOpen_iff.1 isOpen_rootDomain38 _ hz1
  rw [← ball_prod_same] at hball1
  set V' : Set PotPair := (V ∩ ball φ ε1) ∩ a ⁻¹' ball (a φ) ε1 with hV'
  have hV'o : IsOpen V' :=
    (haan.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (isOpen_ball.inter isOpen_ball) isOpen_ball
  have hφV' : φ ∈ V' := ⟨⟨hφV, mem_ball_self hε1⟩, mem_ball_self hε1⟩
  have hdom : ∀ ψ ∈ V', ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      (ψ, a ψ + (s : ℂ) * ((fun _ : PotPair => a φ) ψ - a ψ)) ∈ rootDomain38 := by
    intro ψ hψ s hs
    apply hball1
    refine ⟨hψ.1.2, ?_⟩
    have := (convex_ball (a φ) ε1).add_smul_sub_mem hψ.2 (mem_ball_self hε1) hs
    simpa [Complex.real_smul] using this
  obtain ⟨hAn, hVal⟩ := transport hV'o (a := a) (b := fun _ => a φ) (F := G)
    (haan.mono (fun ψ hψ => hψ.1.1)) analyticOnNhd_const (hGan.mono (fun ψ hψ => hψ.1.1)) hdom
    (fun ψ hψ hp => hGval ψ hψ.1.1 hp)
  refine ⟨a φ, hz1.2, V', hV'o, hφV', _, fun ψ hψ => ⟨hball1 ⟨hψ.1.2, mem_ball_self hε1⟩, hVal ψ hψ⟩, hAn⟩

end
end NlsGge.ThirdConsultation.M011Aux
