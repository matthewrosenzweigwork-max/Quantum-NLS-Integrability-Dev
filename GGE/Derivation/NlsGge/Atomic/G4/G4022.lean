import Mathlib
import NlsGge.Atomic.G4.G4012
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4022Host
import NlsGge.ThirdConsultation.G4.G4018Support9
import NlsGge.GK38.TauGamma
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.IsolatingPersistence

/- G4-022 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4022.lean.
   Head `G4022`: followup9 STATEMENTS/G4.md:259-270 (Pro round 9), verbatim except bound variable lambda -> lam
   (Lean keyword). `chi` is hosted in NlsGge/Atomic/G4/G4022Host.lean. Route: see G4022_MAP01.md / G4022_ROUTE.md
   (genuine; the analytic anchor gkSourceBeta_analytic38 is not used). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.G4022Support
noncomputable section

/-- Clamp of a real parameter to the unit interval. -/
def clampI (t : ℝ) : ℝ := max 0 (min t 1)

theorem clampI_continuous : Continuous clampI := by
  unfold clampI; fun_prop

theorem clampI_mem (t : ℝ) : clampI t ∈ Icc (0 : ℝ) 1 := by
  unfold clampI
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clampI_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampI t = t := by
  unfold clampI
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- Parameter integral along a moving affine segment is analytic. -/
theorem segment_integral_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℂ)} {H : E × ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H W) {τ ℓ : E → ℂ}
    (hτ : AnalyticOnNhd ℂ τ U) (hℓ : AnalyticOnNhd ℂ ℓ U)
    (hW : ∀ u ∈ U, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      (u, τ u + (s : ℂ) * (ℓ u - τ u)) ∈ W) :
    AnalyticOnNhd ℂ
      (fun u => ∫ s in (0 : ℝ)..1, H (u, τ u + (s : ℂ) * (ℓ u - τ u))) U := by
  let a : ℝ → E → ℂ := fun t u => H (u, τ u + (clampI t : ℂ) * (ℓ u - τ u))
  have hmaps : ∀ t : ℝ, ∀ u ∈ U, (u, τ u + (clampI t : ℂ) * (ℓ u - τ u)) ∈ W :=
    fun t u hu => hW u hu (clampI t) (clampI_mem t)
  have heq : ∀ u : E, (∫ s in (0 : ℝ)..1, H (u, τ u + (s : ℂ) * (ℓ u - τ u))) =
      ∫ t, a t u ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro u
    rw [← intervalIntegral.integral_of_le zero_le_one]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    simp only [a, clampI_eq hs]
  have hfun : (fun u => ∫ s in (0 : ℝ)..1, H (u, τ u + (s : ℂ) * (ℓ u - τ u))) =
      fun u => ∫ t, a t u ∂(volume.restrict (Ioc (0 : ℝ) 1)) := funext heq
  rw [hfun]
  -- joint continuity
  have hΨ : ContinuousOn (fun z : E × ℝ => a z.2 z.1) (U ×ˢ (univ : Set ℝ)) := by
    have h1 : ContinuousOn (fun z : E × ℝ => τ z.1) (U ×ˢ (univ : Set ℝ)) :=
      hτ.continuousOn.comp continuousOn_fst (fun z hz => hz.1)
    have h2 : ContinuousOn (fun z : E × ℝ => ℓ z.1) (U ×ˢ (univ : Set ℝ)) :=
      hℓ.continuousOn.comp continuousOn_fst (fun z hz => hz.1)
    have h3 : Continuous (fun z : E × ℝ => (clampI z.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (clampI_continuous.comp continuous_snd)
    have h4 : ContinuousOn (fun z : E × ℝ => (z.1, τ z.1 + (clampI z.2 : ℂ) * (ℓ z.1 - τ z.1)))
        (U ×ˢ (univ : Set ℝ)) :=
      (continuous_fst.continuousOn).prodMk (h1.add (h3.continuousOn.mul (h2.sub h1)))
    exact hH.continuousOn.comp h4 (fun z hz => hmaps z.2 z.1 hz.1)
  have hana : ∀ t : ℝ, AnalyticOnNhd ℂ (a t) U := by
    intro t u hu
    have hm := hmaps t u hu
    have hpair : AnalyticAt ℂ (fun v : E => (v, τ v + (clampI t : ℂ) * (ℓ v - τ v))) u :=
      analyticAt_id.prod ((hτ u hu).add (analyticAt_const.mul ((hℓ u hu).sub (hτ u hu))))
    exact (hH _ hm).comp_of_eq hpair rfl
  apply NlsGge.Atomic.G4.analyticOn_integral_of_locally_dominated hU
  · exact Filter.Eventually.of_forall hana
  · intro u hu
    have hc : Continuous (fun t : ℝ => a t u) := by
      have : ContinuousOn (fun t : ℝ => a t u) univ :=
        hΨ.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t _ => ⟨hu, mem_univ _⟩)
      exact continuousOn_univ.mp this
    exact hc.aestronglyMeasurable
  · intro u₁ hu₁
    -- bound at u₁ on the compact interval
    have hc1 : Continuous (fun t : ℝ => ‖a t u₁‖) := by
      have : ContinuousOn (fun t : ℝ => a t u₁) univ :=
        hΨ.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t _ => ⟨hu₁, mem_univ _⟩)
      exact (continuousOn_univ.mp this).norm
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hc1.continuousOn
    have hev : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ z in 𝓝 (u₁, t), ‖a z.2 z.1‖ < max B 0 + 1 := by
      intro t ht
      have hcz : ContinuousAt (fun z : E × ℝ => a z.2 z.1) (u₁, t) :=
        hΨ.continuousAt (prod_mem_nhds (hU.mem_nhds hu₁) univ_mem)
      have h1 : ContinuousAt (fun z : E × ℝ => ‖a z.2 z.1‖) (u₁, t) := hcz.norm
      have hlt : ‖a t u₁‖ < max B 0 + 1 := by
        have := hB t ht
        simp only [norm_norm] at this
        linarith [le_max_left B 0]
      exact h1.eventually (gt_mem_nhds hlt)
    have htube := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).eventually_forall_of_forall_eventually
      (P := fun u t => ‖a t u‖ < max B 0 + 1) hev
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (htube.and (hU.mem_nhds hu₁))
    refine ⟨r, hr, fun v hv => (hrsub hv).2, fun _ => max B 0 + 1, ?_, ?_⟩
    · exact integrable_const _
    · intro v hv
      refine Filter.Eventually.of_forall (fun t => ?_)
      have h1 := (hrsub hv).1 (clampI t) (clampI_mem t)
      have e : a (clampI t) v = a t v := by simp only [a, clampI_eq (clampI_mem t)]
      rw [e] at h1
      exact h1.le

/-- Convexity of a set of scalars along a segment. -/
theorem seg_mem {B : Set ℂ} (hB : Convex ℝ B) {a b : ℂ} (ha : a ∈ B) (hb : b ∈ B)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : a + (s : ℂ) * (b - a) ∈ B := by
  have h := hB ha hb (sub_nonneg.2 hs.2) hs.1 (by ring)
  have e : a + (s : ℂ) * (b - a) = (1 - s) • a + s • b := by
    simp only [Complex.real_smul]; push_cast; ring
  rw [e]; exact h

/-- The partial derivative in the second slot of a jointly analytic function. -/
theorem slice_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} {p : E × ℂ} (h : AnalyticAt ℂ F p) :
    HasDerivAt (fun z : ℂ => F (p.1, z)) (fderiv ℂ F p ((0 : E), (1 : ℂ))) p.2 := by
  have h1 : HasFDerivAt F (fderiv ℂ F p) p := h.differentiableAt.hasFDerivAt
  have h2 : HasDerivAt (fun z : ℂ => (p.1, z)) ((0 : E), (1 : ℂ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact h1.comp_hasDerivAt p.2 h2

theorem slice_deriv_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {S : Set (E × ℂ)} {F : E × ℂ → ℂ} (hF : AnalyticOnNhd ℂ F S) :
    AnalyticOnNhd ℂ (fun p : E × ℂ => fderiv ℂ F p ((0 : E), (1 : ℂ))) S := by
  intro p hp
  exact ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).analyticAt _).comp (hF.fderiv p hp)

/-- The divided difference equals the segment integral of the derivative. -/
theorem divided_difference_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F : E × ℂ → ℂ} {φ : E} {B : Set ℂ} (hB : Convex ℝ B)
    (hK : ∀ z ∈ B, AnalyticAt ℂ F (φ, z)) {τ lam : ℂ} (hτ : τ ∈ B) (hlam : lam ∈ B) :
    (if lam = τ then fderiv ℂ F (φ, τ) ((0 : E), (1 : ℂ))
      else (F (φ, τ) - F (φ, lam)) / (τ - lam)) =
    ∫ s in (0 : ℝ)..1, fderiv ℂ F (φ, τ + (s : ℂ) * (lam - τ)) ((0 : E), (1 : ℂ)) := by
  classical
  have hderiv : ∀ z ∈ B, HasDerivAt (fun w : ℂ => F (φ, w))
      (fderiv ℂ F (φ, z) ((0 : E), (1 : ℂ))) z :=
    fun z hz => slice_hasDerivAt (p := (φ, z)) (hK z hz)
  by_cases h : lam = τ
  · subst h
    simp
  · rw [if_neg h]
    have hγ : ∀ s ∈ Icc (0 : ℝ) 1, τ + (s : ℂ) * (lam - τ) ∈ B :=
      fun s hs => seg_mem hB hτ hlam hs
    have hpath : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => F (φ, τ + (x : ℂ) * (lam - τ)))
          (fderiv ℂ F (φ, τ + (s : ℂ) * (lam - τ)) ((0 : E), (1 : ℂ)) * (lam - τ)) s := by
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      have hlin : HasDerivAt (fun w : ℂ => τ + w * (lam - τ)) (lam - τ) (s : ℂ) := by
        simpa using ((hasDerivAt_id (s : ℂ)).mul_const (lam - τ)).const_add τ
      have hcomp := (hderiv _ (hγ s hs)).comp (s : ℂ) hlin
      exact hcomp.comp_ofReal
    have hDc : ∀ z ∈ B, ContinuousAt (fun w : ℂ => fderiv ℂ F (φ, w) ((0 : E), (1 : ℂ))) z := by
      intro z hz
      have h1 : ContinuousAt (fun p : E × ℂ => fderiv ℂ F p ((0 : E), (1 : ℂ))) (φ, z) :=
        (((ContinuousLinearMap.apply ℂ ℂ ((0 : E), (1 : ℂ))).analyticAt _).comp
          (hK z hz).fderiv).continuousAt
      exact h1.comp (f := fun w : ℂ => (φ, w)) (x := z) (by fun_prop)
    have hcont : ContinuousOn
        (fun s : ℝ => fderiv ℂ F (φ, τ + (s : ℂ) * (lam - τ)) ((0 : E), (1 : ℂ)))
        (uIcc (0 : ℝ) 1) := by
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      have h2 := hDc _ (hγ s hs)
      have h3 : Continuous (fun x : ℝ => τ + (x : ℂ) * (lam - τ)) := by fun_prop
      exact (h2.comp_of_eq (h3.continuousAt (x := s)) rfl).continuousWithinAt
    have hint : IntervalIntegrable
        (fun s : ℝ => fderiv ℂ F (φ, τ + (s : ℂ) * (lam - τ)) ((0 : E), (1 : ℂ)) * (lam - τ))
        volume 0 1 :=
      (hcont.mul continuousOn_const).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath hint
    rw [intervalIntegral.integral_mul_const] at hftc
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero,
      add_sub_cancel] at hftc
    have hne : τ - lam ≠ 0 := sub_ne_zero.2 (fun e => h e.symm)
    rw [div_eq_iff hne]
    linear_combination hftc

/-- Auxiliary: the partial derivative of the normalized product in the spectral variable. -/
def Kd (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  fderiv ℂ (fun q : PotPair × ℂ => normalizedZeta n q.1 q.2) p ((0 : PotPair), (1 : ℂ))

/-- Auxiliary: the segment integral of `Kd` from `tauN` to the spectral variable. -/
def Dint (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, Kd n (p.1, tauN p.1 n + (s : ℂ) * (p.2 - tauN p.1 n))

theorem local_structure (n : ℤ) (φ₁ : PotPair) (hφ₁ : φ₁ ∈ sourceBetaW) :
    ∃ V₁ : Set PotPair, IsOpen V₁ ∧ φ₁ ∈ V₁ ∧ V₁ ⊆ sourceBetaW ∧
      (∀ φ ∈ V₁, tauN φ n ∈ ball (discC φ₁ n) (discR φ₁ n) ∧
        muSeq φ n ∈ ball (discC φ₁ n) (discR φ₁ n)) ∧
      AnalyticOnNhd ℂ (fun p : PotPair × ℂ => normalizedZeta n p.1 p.2)
        (V₁ ×ˢ ball (discC φ₁ n) (discR φ₁ n)) := by
  have hφW : φ₁ ∈ sourceW := sourceFamily.V_W hφ₁
  have hgk : φ₁ ∈ gkW := sourceFamily.W_gk hφW
  obtain ⟨ρ, hρ, c, N, hgeom, hspecball⟩ :=
    fixed_family_persistence38 φ₁ (discC φ₁) (discR φ₁) (isolating_family38 φ₁ hgk)
  refine ⟨ball φ₁ ρ ∩ sourceBetaW, isOpen_ball.inter sourceFamily.V_open,
    ⟨mem_ball_self hρ, hφ₁⟩, inter_subset_right, ?_, ?_⟩
  · intro φ hφ
    have hs := hspecball φ hφ.1
    have hgkφ : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφ.2)
    refine ⟨?_, (hs.1 n).2.1⟩
    have hmem : tauN φ n ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [tauN_value38 φ hgkφ n]
      simp only [Complex.real_smul]
      push_cast
      ring
    exact (hs.1 n).1 hmem
  · exact NlsGge.G4018Support.normalizedZeta_joint_analytic _
      (fun φ hφ => sourceFamily.V_W hφ.2) (discC φ₁) (discR φ₁)
      (fun φ hφ => ⟨c, N, hgeom, hspecball φ hφ.1⟩) n

theorem Dint_analytic (n : ℤ) {V₁ : Set PotPair} {B : Set ℂ} (hB : Convex ℝ B)
    (hV₁o : IsOpen V₁) (hV₁ : V₁ ⊆ gkW) (htau : ∀ φ ∈ V₁, tauN φ n ∈ B)
    (hF : AnalyticOnNhd ℂ (fun p : PotPair × ℂ => normalizedZeta n p.1 p.2) (V₁ ×ˢ B))
    (hBo : IsOpen B) :
    AnalyticOnNhd ℂ (Dint n) (V₁ ×ˢ B) := by
  have hKd : AnalyticOnNhd ℂ (Kd n) (V₁ ×ˢ B) := slice_deriv_analytic hF
  have hH : AnalyticOnNhd ℂ (fun q : (PotPair × ℂ) × ℂ => Kd n (q.1.1, q.2))
      {q : (PotPair × ℂ) × ℂ | (q.1.1, q.2) ∈ V₁ ×ˢ B} := by
    intro q hq
    have h1 : AnalyticAt ℂ (fun q : (PotPair × ℂ) × ℂ => q.1.1) q :=
      analyticAt_fst.comp_of_eq analyticAt_fst rfl
    have hp : AnalyticAt ℂ (fun q : (PotPair × ℂ) × ℂ => (q.1.1, q.2)) q :=
      h1.prod analyticAt_snd
    exact (hKd (q.1.1, q.2) hq).comp_of_eq hp rfl
  have hτ : AnalyticOnNhd ℂ (fun u : PotPair × ℂ => tauN u.1 n) (V₁ ×ˢ B) := by
    intro u hu
    exact (tauN_analytic n u.1 (hV₁ hu.1)).comp_of_eq analyticAt_fst rfl
  have hℓ : AnalyticOnNhd ℂ (fun u : PotPair × ℂ => u.2) (V₁ ×ˢ B) :=
    fun u _ => analyticAt_snd
  have hU : IsOpen (V₁ ×ˢ B) := hV₁o.prod hBo
  exact segment_integral_analytic hU hH hτ hℓ
    (fun u hu s hs => ⟨hu.1, seg_mem hB (htau _ hu.1) hu.2 hs⟩)

theorem zdd_eq_Dint (n : ℤ) {V₁ : Set PotPair} {B : Set ℂ} (hB : Convex ℝ B)
    (htau : ∀ φ ∈ V₁, tauN φ n ∈ B)
    (hF : AnalyticOnNhd ℂ (fun p : PotPair × ℂ => normalizedZeta n p.1 p.2) (V₁ ×ˢ B))
    {φ : PotPair} (hφ : φ ∈ V₁) {lam : ℂ} (hlam : lam ∈ B) :
    zetaDividedDifference n φ lam = Dint n (φ, lam) := by
  have h := divided_difference_eq_integral (F := fun q : PotPair × ℂ => normalizedZeta n q.1 q.2)
    (φ := φ) hB (fun z hz => hF (φ, z) ⟨hφ, hz⟩) (htau φ hφ) hlam
  have hz : deriv (normalizedZeta n φ) (tauN φ n) = Kd n (φ, tauN φ n) :=
    (slice_hasDerivAt (F := fun q : PotPair × ℂ => normalizedZeta n q.1 q.2)
      (p := (φ, tauN φ n)) (hF (φ, tauN φ n) ⟨hφ, htau φ hφ⟩)).deriv
  unfold zetaDividedDifference
  by_cases hl : lam = tauN φ n
  · rw [if_pos hl, hz]
    rw [if_pos hl] at h
    exact h
  · rw [if_neg hl]
    rw [if_neg hl] at h
    exact h


theorem zdd_analyticAt (n : ℤ) (φ₁ : PotPair) (hφ₁ : φ₁ ∈ sourceBetaW) (lam : ℂ)
    (hlam : lam ∈ ball (discC φ₁ n) (discR φ₁ n)) :
    AnalyticAt ℂ (fun p : PotPair × ℂ => zetaDividedDifference n p.1 p.2) (φ₁, lam) := by
  obtain ⟨V₁, hV₁o, hφV, hV₁s, hball, hF⟩ := local_structure n φ₁ hφ₁
  have hgk : V₁ ⊆ gkW := fun φ hφ => sourceFamily.W_gk (sourceFamily.V_W (hV₁s hφ))
  have hD := Dint_analytic n (convex_ball _ _) hV₁o hgk (fun φ hφ => (hball φ hφ).1) hF
    isOpen_ball
  have hmem : (φ₁, lam) ∈ V₁ ×ˢ ball (discC φ₁ n) (discR φ₁ n) := ⟨hφV, hlam⟩
  have hnh : V₁ ×ˢ ball (discC φ₁ n) (discR φ₁ n) ∈ 𝓝 (φ₁, lam) :=
    (hV₁o.prod isOpen_ball).mem_nhds hmem
  refine (hD _ hmem).congr ?_
  filter_upwards [hnh] with p hp
  exact (zdd_eq_Dint n (convex_ball _ _) (fun φ hφ => (hball φ hφ).1) hF hp.1 hp.2).symm

theorem seg_intervalIntegrable (n : ℤ) (φ₁ : PotPair) (hφ₁ : φ₁ ∈ sourceBetaW) :
    IntervalIntegrable (fun t : ℝ => zetaDividedDifference n φ₁
      (tauN φ₁ n + (t : ℂ) * (muSeq φ₁ n - tauN φ₁ n))) volume 0 1 := by
  obtain ⟨V₁, hV₁o, hφV, hV₁s, hball, hF⟩ := local_structure n φ₁ hφ₁
  have hgk : V₁ ⊆ gkW := fun φ hφ => sourceFamily.W_gk (sourceFamily.V_W (hV₁s hφ))
  have hD := Dint_analytic n (convex_ball _ _) hV₁o hgk (fun φ hφ => (hball φ hφ).1) hF
    isOpen_ball
  have hpath : Continuous (fun t : ℝ => (φ₁, tauN φ₁ n + (t : ℂ) * (muSeq φ₁ n - tauN φ₁ n))) := by
    fun_prop
  have hseg : ∀ t ∈ uIcc (0 : ℝ) 1,
      tauN φ₁ n + (t : ℂ) * (muSeq φ₁ n - tauN φ₁ n) ∈ ball (discC φ₁ n) (discR φ₁ n) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact seg_mem (convex_ball _ _) (hball φ₁ hφV).1 (hball φ₁ hφV).2 ht
  refine ContinuousOn.intervalIntegrable ?_
  have hc : ContinuousOn
      (fun t : ℝ => Dint n (φ₁, tauN φ₁ n + (t : ℂ) * (muSeq φ₁ n - tauN φ₁ n)))
      (uIcc (0 : ℝ) 1) :=
    hD.continuousOn.comp hpath.continuousOn (fun t ht => ⟨hφV, hseg t ht⟩)
  exact hc.congr (fun t ht =>
    zdd_eq_Dint n (convex_ball _ _) (fun φ hφ => (hball φ hφ).1) hF hφV (hseg t ht))

theorem chi_analyticAt (n : ℤ) (φ₁ : PotPair) (hφ₁ : φ₁ ∈ sourceBetaW) :
    AnalyticAt ℂ (chi n) φ₁ := by
  obtain ⟨V₁, hV₁o, hφV, hV₁s, hball, hF⟩ := local_structure n φ₁ hφ₁
  have hgk : V₁ ⊆ gkW := fun φ hφ => sourceFamily.W_gk (sourceFamily.V_W (hV₁s hφ))
  have hD := Dint_analytic n (convex_ball _ _) hV₁o hgk (fun φ hφ => (hball φ hφ).1) hF
    isOpen_ball
  have hτ : AnalyticOnNhd ℂ (fun φ : PotPair => tauN φ n) V₁ :=
    fun φ hφ => tauN_analytic n φ (hgk hφ)
  have hμ : AnalyticOnNhd ℂ (fun φ : PotPair => muSeq φ n) V₁ :=
    fun φ hφ => analyticOnNhd_muSeq_complex38 n φ (hgk hφ)
  have hI := segment_integral_analytic hV₁o hD hτ hμ
    (fun φ hφ s hs => ⟨hφ, seg_mem (convex_ball _ _) (hball φ hφ).1 (hball φ hφ).2 hs⟩)
  have hprod := ((hμ φ₁ hφV).sub (hτ φ₁ hφV)).mul (hI φ₁ hφV)
  refine hprod.congr ?_
  filter_upwards [hV₁o.mem_nhds hφV] with φ hφ
  simp only [Pi.mul_apply, Pi.sub_apply]
  unfold chi
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact (zdd_eq_Dint n (convex_ball _ _) (fun φ hφ => (hball φ hφ).1) hF hφ
    (seg_mem (convex_ball _ _) (hball φ hφ).1 (hball φ hφ).2 ht)).symm

end
end NlsGge.G4022Support

namespace NlsGge.GKDefinitionDesign
noncomputable section

open NlsGge.G4022Support in
theorem G4022 (n : ℤ) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ sourceBetaW ∧
    AnalyticOnNhd ℂ (chi n) V ∧
    ∀ φ ∈ V,
      IntervalIntegrable (fun t : ℝ =>
        zetaDividedDifference n φ (tauN φ n + (t : ℂ) * (muSeq φ n - tauN φ n)))
        volume 0 1 ∧
      (∀ lam ∈ Metric.ball (discC φ n) (discR φ n),
        AnalyticAt ℂ (fun p : PotPair × ℂ => zetaDividedDifference n p.1 p.2) (φ, lam)) ∧
      zetaDividedDifference n φ (tauN φ n) = deriv (normalizedZeta n φ) (tauN φ n) := by
  refine ⟨sourceBetaW, sourceFamily.V_open.mem_nhds hφ₀, subset_rfl,
    fun φ hφ => chi_analyticAt n φ hφ, fun φ hφ => ⟨seg_intervalIntegrable n φ hφ,
      fun lam hlam => zdd_analyticAt n φ hφ lam hlam, ?_⟩⟩
  unfold zetaDividedDifference
  rw [if_pos rfl]

end
end NlsGge.GKDefinitionDesign
