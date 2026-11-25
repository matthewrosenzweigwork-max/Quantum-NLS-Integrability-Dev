import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.TauGamma
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036H2
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN003
import NlsGge.Atomic.KSN.KSN004Host

                                                                                                                     
                                                                                                                                   
                                                                                                                                       
                          
                                                                                                            
                                                                                                                                    
                                                                                                                                     
                                                                                                                                    
                                                                                                                                       
set_option autoImplicit false

namespace NlsGge.Atomic.KSN004Support
noncomputable section
open Set Filter Topology MeasureTheory
open NlsGge.Atomic.KSN003Design (PiecewiseC1On)

/-- A continuous nonvanishing square root of a differentiable function is differentiable. -/
theorem root_hasDerivWithinAt {s : Set ℝ} {x : ℝ} {r Q : ℝ → ℂ} {Q' : ℂ}
    (hQ : HasDerivWithinAt Q Q' s x) (hr : ContinuousWithinAt r s x)
    (hsq : ∀ u ∈ s, r u ^ 2 = Q u) (hx : x ∈ s) (hne : r x ≠ 0) :
    HasDerivWithinAt r (Q' / (2 * r x)) s x := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hQ ⊢
  have hsum : Tendsto (fun u => r u + r x) (𝓝[s \ {x}] x) (𝓝 (r x + r x)) :=
    (hr.mono Set.sdiff_subset).tendsto.add tendsto_const_nhds
  have h2 : r x + r x ≠ 0 := by
    rw [← two_mul]; exact mul_ne_zero two_ne_zero hne
  have hq := hQ.div hsum h2
  have h22 : 2 * r x = r x + r x := by ring
  rw [h22]
  refine Tendsto.congr' ?_ hq
  filter_upwards [self_mem_nhdsWithin, hsum.eventually_ne h2] with u hu hne'
  simp only [Pi.div_apply]
  have hu1 : u ∈ s := hu.1
  have hu2 : u ≠ x := hu.2
  have hsub : u - x ≠ 0 := sub_ne_zero.2 hu2
  rw [slope_def_module, slope_def_module, Complex.real_smul, Complex.real_smul]
  have hq1 := hsq u hu1
  have hq2 := hsq x hx
  have hsub' : ((u : ℂ) - (x : ℂ)) ≠ 0 := by exact_mod_cast hsub
  push_cast
  rw [← hq1, ← hq2]
  field_simp
  ring

theorem arc_ftc (A B : ℂ) (oc ζ : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hoc : DifferentiableOn ℂ oc U) (hζ : ContinuousOn ζ U)
    (hode : ∀ z ∈ U, (A - z) * (B - z) * deriv oc z + (z - (A + B) / 2) * oc z = ζ z - 1)
    {c r : ℝ → ℂ} {p q : ℝ} (hpq : p ≤ q) (hc : ContDiffOn ℝ 1 c (Icc p q))
    (hr : ContinuousOn r (Icc p q)) (hU' : ∀ u ∈ Icc p q, c u ∈ U)
    (hsq : ∀ u ∈ Icc p q, r u ^ 2 = (A - c u) * (B - c u))
    (hne : ∀ u ∈ Icc p q, r u ≠ 0) :
    IntervalIntegrable (fun u => deriv c u * (ζ (c u) - 1) / r u) volume p q ∧
      ∫ u in p..q, deriv c u * (ζ (c u) - 1) / r u = r q * oc (c q) - r p * oc (c p) := by
  rcases hpq.eq_or_lt with rfl | hlt
  · exact ⟨IntervalIntegrable.refl, by simp⟩
  · set D : ℝ → ℂ := derivWithin c (Icc p q) with hD
    have hUD : UniqueDiffOn ℝ (Icc p q) := uniqueDiffOn_Icc hlt
    have hDcont : ContinuousOn D (Icc p q) := hc.continuousOn_derivWithin hUD le_rfl
    have hcc : ContinuousOn c (Icc p q) := hc.continuousOn
    have hmaps : MapsTo c (Icc p q) U := hU'
    have hocc : ContinuousOn oc U := hoc.continuousOn
    have hg : ContinuousOn (fun u => D u * (ζ (c u) - 1) / r u) (Icc p q) :=
      (hDcont.mul ((hζ.comp hcc hmaps).sub continuousOn_const)).div hr hne
    have hgint : IntervalIntegrable (fun u => D u * (ζ (c u) - 1) / r u) volume p q :=
      hg.intervalIntegrable_of_Icc hlt.le
    have hEq : ∀ u ∈ Ioo p q, deriv c u = D u := fun u hu =>
      (derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)).symm
    have hfint : IntervalIntegrable (fun u => deriv c u * (ζ (c u) - 1) / r u) volume p q := by
      refine hgint.congr_uIoo ?_
      intro u hu
      rw [Set.uIoo_of_le hlt.le] at hu
      simp only
      rw [hEq u hu]
    have hint_eq : ∫ u in p..q, deriv c u * (ζ (c u) - 1) / r u =
        ∫ u in p..q, D u * (ζ (c u) - 1) / r u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(Set.countable_singleton q).ae_notMem volume] with u hu huI
      rw [Set.uIoc_of_le hlt.le] at huI
      have hne' : u ≠ q := hu
      rw [hEq u ⟨huI.1, lt_of_le_of_ne huI.2 hne'⟩]
    refine ⟨hfint, ?_⟩
    rw [hint_eq]
    have hderiv : ∀ x ∈ Icc p q, HasDerivWithinAt (fun u => r u * oc (c u))
        (D x * (ζ (c x) - 1) / r x) (Icc p q) x := by
      intro x hx
      have hcd : HasDerivWithinAt c (D x) (Icc p q) x :=
        ((hc.differentiableOn one_ne_zero) x hx).hasDerivWithinAt
      have hQ : HasDerivWithinAt (fun u => (A - c u) * (B - c u))
          ((-D x) * (B - c x) + (A - c x) * (-D x)) (Icc p q) x :=
        (hcd.const_sub A).mul (hcd.const_sub B)
      have hR := root_hasDerivWithinAt (Q := fun u => (A - c u) * (B - c u)) hQ (hr x hx)
        hsq hx (hne x hx)
      have hocd : HasDerivAt oc (deriv oc (c x)) (c x) :=
        (hoc.differentiableAt (hU.mem_nhds (hU' x hx))).hasDerivAt
      have hO : HasDerivWithinAt (oc ∘ c) (D x • deriv oc (c x)) (Icc p q) x :=
        hocd.scomp_hasDerivWithinAt x hcd
      have hP := hR.mul hO
      refine hP.congr_deriv ?_
      have hz := hode (c x) (hU' x hx)
      have hsqx := hsq x hx
      have hr0 := hne x hx
      simp only [Function.comp_apply, smul_eq_mul]
      rw [← hz, ← hsqx]
      field_simp
      ring
    have hcontF : ContinuousOn (fun u => r u * oc (c u)) (Icc p q) :=
      hr.mul (hocc.comp hcc hmaps)
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hlt.le hcontF
      (fun x hx => (hderiv x ⟨hx.1.le, hx.2.le⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsGT hx.2)
          (fun y hy => ⟨hx.1.le.trans hy.1.le, hy.2.le⟩))) hgint

theorem pw_ftc (A B : ℂ) (oc ζ : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hoc : DifferentiableOn ℂ oc U) (hζ : ContinuousOn ζ U)
    (hode : ∀ z ∈ U, (A - z) * (B - z) * deriv oc z + (z - (A + B) / 2) * oc z = ζ z - 1)
    {c r : ℝ → ℂ} {p q : ℝ} (h : PiecewiseC1On c p q)
    (hr : ContinuousOn r (Icc p q)) (hU' : ∀ u ∈ Icc p q, c u ∈ U)
    (hsq : ∀ u ∈ Icc p q, r u ^ 2 = (A - c u) * (B - c u))
    (hne : ∀ u ∈ Icc p q, r u ≠ 0) :
    IntervalIntegrable (fun u => deriv c u * (ζ (c u) - 1) / r u) volume p q ∧
      ∫ u in p..q, deriv c u * (ζ (c u) - 1) / r u = r q * oc (c q) - r p * oc (c p) := by
  induction h with
  | arc hpq hc => exact arc_ftc A B oc ζ U hU hoc hζ hode hpq hc hr hU' hsq hne
  | @trans p m q h₁ h₂ _ _ ih1 ih2 =>
    obtain ⟨hi1, he1⟩ := ih1 (hr.mono (Icc_subset_Icc le_rfl h₂))
      (fun u hu => hU' u ⟨hu.1, hu.2.trans h₂⟩) (fun u hu => hsq u ⟨hu.1, hu.2.trans h₂⟩)
      (fun u hu => hne u ⟨hu.1, hu.2.trans h₂⟩)
    obtain ⟨hi2, he2⟩ := ih2 (hr.mono (Icc_subset_Icc h₁ le_rfl))
      (fun u hu => hU' u ⟨h₁.trans hu.1, hu.2⟩) (fun u hu => hsq u ⟨h₁.trans hu.1, hu.2⟩)
      (fun u hu => hne u ⟨h₁.trans hu.1, hu.2⟩)
    refine ⟨hi1.trans hi2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, he1, he2]
    ring

theorem pw_sub {c : ℝ → ℂ} {p q : ℝ} (h : PiecewiseC1On c p q) :
    ∀ a b, p ≤ a → a ≤ b → b ≤ q → PiecewiseC1On c a b := by
  induction h with
  | arc hpq hc =>
    intro a b hpa hab hbq
    exact PiecewiseC1On.arc hab (hc.mono (Icc_subset_Icc hpa hbq))
  | @trans p m q h₁ h₂ _ _ ih1 ih2 =>
    intro a b hpa hab hbq
    by_cases hbm : b ≤ m
    · exact ih1 a b hpa hab hbm
    · by_cases ham : m ≤ a
      · exact ih2 a b ham hab hbq
      · exact PiecewiseC1On.trans (not_le.1 ham).le (not_le.1 hbm).le
          (ih1 a m hpa (not_le.1 ham).le le_rfl) (ih2 m b le_rfl (not_le.1 hbm).le hbq)

theorem pw_continuousOn {c : ℝ → ℂ} {p q : ℝ} (h : PiecewiseC1On c p q) :
    ContinuousOn c (Icc p q) := by
  induction h with
  | arc hpq hc => exact hc.continuousOn
  | @trans p m q h₁ h₂ _ _ ih1 ih2 =>
    rw [← Set.Icc_union_Icc_eq_Icc h₁ h₂]
    exact ih1.union_of_isClosed ih2 isClosed_Icc isClosed_Icc

theorem correction_limit (A B : ℂ) (oc ζ : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hoc : DifferentiableOn ℂ oc U) (hζ : ContinuousOn ζ U)
    (hode : ∀ z ∈ U, (A - z) * (B - z) * deriv oc z + (z - (A + B) / 2) * oc z = ζ z - 1)
    {c r : ℝ → ℂ} (hpw : PiecewiseC1On c 0 1) (hr : ContinuousOn r (Icc 0 1))
    (hU' : ∀ u ∈ Icc (0 : ℝ) 1, c u ∈ U)
    (hsq : ∀ u ∈ Icc (0 : ℝ) 1, r u ^ 2 = (A - c u) * (B - c u))
    (hne : ∀ u ∈ Ioo (0 : ℝ) 1, r u ≠ 0) :
    (∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      IntervalIntegrable (fun t => deriv c t * (ζ (c t) - 1) / r t) volume δ (1 - δ)) ∧
    Tendsto (fun δ : ℝ => ∫ t in δ..(1 - δ), deriv c t * (ζ (c t) - 1) / r t) (𝓝[>] 0)
      (𝓝 (r 1 * oc (c 1) - r 0 * oc (c 0))) := by
  have hmain : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      IntervalIntegrable (fun t => deriv c t * (ζ (c t) - 1) / r t) volume δ (1 - δ) ∧
      ∫ t in δ..(1 - δ), deriv c t * (ζ (c t) - 1) / r t =
        r (1 - δ) * oc (c (1 - δ)) - r δ * oc (c δ) := by
    intro δ h0 h1
    have hsub : PiecewiseC1On c δ (1 - δ) :=
      pw_sub hpw δ (1 - δ) h0.le (by linarith) (by linarith)
    have hI : ∀ u ∈ Icc δ (1 - δ), u ∈ Icc (0 : ℝ) 1 :=
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hI' : ∀ u ∈ Icc δ (1 - δ), u ∈ Ioo (0 : ℝ) 1 :=
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact pw_ftc A B oc ζ U hU hoc hζ hode hsub (hr.mono hI) (fun u hu => hU' u (hI u hu))
      (fun u hu => hsq u (hI u hu)) (fun u hu => hne u (hI' u hu))
  refine ⟨fun δ h0 h1 => (hmain δ h0 h1).1, ?_⟩
  have hF : ContinuousOn (fun u => r u * oc (c u)) (Icc 0 1) :=
    hr.mul (hoc.continuousOn.comp (pw_continuousOn hpw) hU')
  have hl0 : Tendsto (fun δ : ℝ => r δ * oc (c δ)) (𝓝[>] 0) (𝓝 (r 0 * oc (c 0))) := by
    have h := hF 0 ⟨le_rfl, zero_le_one⟩
    exact (h.mono_of_mem_nhdsWithin
      (mem_of_superset (Ioc_mem_nhdsGT zero_lt_one) Ioc_subset_Icc_self)).tendsto
  have hl1 : Tendsto (fun δ : ℝ => r (1 - δ) * oc (c (1 - δ))) (𝓝[>] 0)
      (𝓝 (r 1 * oc (c 1))) := by
    have h := hF 1 ⟨zero_le_one, le_rfl⟩
    have hlim : Tendsto (fun δ : ℝ => 1 - δ) (𝓝[>] 0) (𝓝[Icc 0 1] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h' : Tendsto (fun δ : ℝ => 1 - δ) (𝓝 0) (𝓝 (1 - 0)) :=
          (continuous_const.sub continuous_id).tendsto 0
        rw [sub_zero] at h'
        exact h'.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with δ hδ
        exact ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
    exact h.tendsto.comp hlim
  refine Tendsto.congr' ?_ (hl1.sub hl0)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
  exact ((hmain δ hδ.1 hδ.2).2).symm

end
end NlsGge.Atomic.KSN004Support

namespace NlsGge.ThirdConsultation.KSN
noncomputable section
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign

theorem KSN004_main (φ : PotPair) (hφ : φ ∈ sourceBetaW) (n a : ℤ)
    (ha : a = 1 ∨ a = -1) (hγ : gamma2 φ n ≠ 0)
    (cMinus rMinus cPlus rPlus : ℝ → ℂ)
    (hMinus : CorrectionPath n φ false cMinus rMinus) (hPlus : CorrectionPath n φ true cPlus rPlus) :
  ∃ IMinus IPlus : ℂ,
    HasCorrectionIntegral n φ cMinus rMinus IMinus ∧
    HasCorrectionIntegral n φ cPlus rPlus IPlus ∧
    IMinus = terminalRoot n φ * ownCorrection n φ (muSeq φ n) ∧
    IPlus = terminalRoot n φ * ownCorrection n φ (muSeq φ n) ∧
    Complex.exp (-(a : ℂ) * IMinus) = Complex.exp (-(a : ℂ) * IPlus) ∧
    Complex.exp (-(a : ℂ) * IMinus) = eta n a φ := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφ)
  obtain ⟨hoc, hodeRaw⟩ := ownCorrection_analytic_and_ode n φ hφ
  obtain ⟨c0, N, hg, hs⟩ := isolating_family38 φ hgk
  have hζ : ContinuousOn (normalizedZeta n φ) (Metric.ball (discC φ n) (discR φ n)) :=
    (g4036_K_analytic φ hgk (discC φ) (discR φ) c0 N hg hs n).continuousOn.mono
      Metric.ball_subset_closedBall
  have hode : ∀ z ∈ Metric.ball (discC φ n) (discR φ n),
      (lamPlus φ n - z) * (lamMinus φ n - z) * deriv (ownCorrection n φ) z +
        (z - (lamPlus φ n + lamMinus φ n) / 2) * ownCorrection n φ z =
          normalizedZeta n φ z - 1 := by
    intro z hz
    have h := hodeRaw z hz
    rw [tauN_value38 φ hgk n, gamma2_value38 φ hgk n] at h
    linear_combination h
  have key : ∀ (e : Bool) (c r : ℝ → ℂ), CorrectionPath n φ e c r →
      HasCorrectionIntegral n φ c r (terminalRoot n φ * ownCorrection n φ (muSeq φ n)) := by
    intro e c r h
    obtain ⟨hpw, hrc, hc0, hc1, hr0, hr1, hball, hne⟩ := h
    have hlim := NlsGge.Atomic.KSN004Support.correction_limit (lamPlus φ n) (lamMinus φ n)
      (ownCorrection n φ) (normalizedZeta n φ) (Metric.ball (discC φ n) (discR φ n))
      Metric.isOpen_ball hoc.differentiableOn hζ hode hpw hrc
      (fun u hu => (hball u hu).1) (fun u hu => (hball u hu).2) hne
    have e1 : r 1 * ownCorrection n φ (c 1) - r 0 * ownCorrection n φ (c 0) =
        terminalRoot n φ * ownCorrection n φ (muSeq φ n) := by
      rw [hr1, hr0, hc1]; ring
    rw [e1] at hlim
    exact ⟨hlim.1, hlim.2⟩
  refine ⟨terminalRoot n φ * ownCorrection n φ (muSeq φ n),
    terminalRoot n φ * ownCorrection n φ (muSeq φ n), key false cMinus rMinus hMinus, key true cPlus rPlus hPlus,
    rfl, rfl, rfl, ?_⟩
  unfold eta
  congr 1
  ring

end
end NlsGge.ThirdConsultation.KSN
