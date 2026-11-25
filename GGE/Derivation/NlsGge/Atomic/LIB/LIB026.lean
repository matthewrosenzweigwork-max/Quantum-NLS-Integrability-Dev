import Mathlib
import NlsGge.Atomic.IntervalH1
import NlsGge.Spectral.ComplexACPointwiseTestIntegrationByPartsV2

/-!
# LIB-026: arbitrary interval H1 representatives, traces, and Green pairing

The shared carrier is the graph of the distributional derivative on the open unit
interval, with no endpoint condition. The proof first establishes the L1 core:
a function with zero weak derivative is constant almost everywhere, using a local
mean-zero test antiderivative and the fundamental lemma of the calculus of variations.
Subtracting the derivative primitive then constructs an AC representative.

Its restriction to `[0,1]` is the unique continuous representative, so the public
representative and its endpoint traces are independent of all choices. Every point
evaluation is bounded by the sum of the two L2 norms. The conjugate product rule
and AC fundamental theorem give integration by parts on the full H1 carrier.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace NlsGge.Atomic.LIB026

lemma integral_eq_interval_of_tsupport_subset {f : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo (0 : ℝ) 1) :
    (∫ x, f x) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (0 : ℝ) 1) fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(hf h).1, (hf h).2.le⟩)).symm

lemma exists_local_antideriv {ψ : ℝ → ℝ} (hs : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hU : tsupport ψ ⊆ Ioo (0 : ℝ) 1)
    (h0 : ∫ x, ψ x = 0) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo (0 : ℝ) 1 ∧ ∀ x, deriv χ x = ψ x := by
  by_cases hne : (tsupport ψ).Nonempty
  · let A : ℝ := sInf (tsupport ψ)
    let B : ℝ := sSup (tsupport ψ)
    have hA : 0 < A := (hU (hc.sInf_mem hne)).1
    have hB : B < 1 := (hU (hc.sSup_mem hne)).2
    let a := A / 2
    let b := (B + 1) / 2
    have ha : 0 < a := half_pos hA
    have hb : b < 1 := by dsimp [b]; linarith
    have hψa : ∀ x, x ≤ a → ψ x = 0 := by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hxs
      have := csInf_le hc.bddBelow hxs
      change A ≤ x at this
      dsimp [a] at hx
      linarith
    have hψb : ∀ x, b ≤ x → ψ x = 0 := by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hxs
      have := le_csSup hc.bddAbove hxs
      change x ≤ B at this
      dsimp [b] at hx
      linarith
    let χ : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, ψ s
    have hd (x : ℝ) : HasDerivAt χ (ψ x) x :=
      (hs.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
    have hder : deriv χ = ψ := funext fun x => (hd x).deriv
    have hχ0 : ∫ s in (0 : ℝ)..1, ψ s = 0 := by
      rw [← integral_eq_interval_of_tsupport_subset hU, h0]
    have hχa : ∀ x, x ≤ a → χ x = 0 := by
      intro x hx
      change (∫ s in (0 : ℝ)..x, ψ s) = 0
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro s hs'
        apply hψa
        rw [uIcc] at hs'
        exact hs'.2.trans (max_le ha.le hx)
    have hχb : ∀ x, b ≤ x → χ x = 0 := by
      intro x hx
      change (∫ s in (0 : ℝ)..x, ψ s) = 0
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (b := 1) (hs.continuous.intervalIntegrable _ _)
        (hs.continuous.intervalIntegrable _ _), hχ0]
      have hz : (∫ s in (1 : ℝ)..x, ψ s) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
        · simp
        · intro s hs'
          apply hψb
          rw [uIcc] at hs'
          exact (le_min hb.le hx).trans hs'.1
      simp [hz]
    have hts : tsupport χ ⊆ Icc a b := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      constructor
      · by_contra hn
        exact hx (hχa x (not_le.mp hn).le)
      · by_contra hn
        exact hx (hχb x (not_le.mp hn).le)
    refine ⟨χ, ?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) hts,
      fun x hx => ⟨ha.trans_le (hts hx).1, (hts hx).2.trans_lt hb⟩, fun x => congrFun hder x⟩
    rw [contDiff_infty_iff_deriv, hder]
    exact ⟨fun x => (hd x).differentiableAt, hs⟩
  · have hψ : ψ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun hx => hne ⟨x, hx⟩)
    refine ⟨0, contDiff_const, ?_, ?_, ?_⟩
    · simp [HasCompactSupport]
    · simp
    · intro x
      simp [hψ]

lemma exists_local_bump : ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
    tsupport ρ ⊆ Ioo (0 : ℝ) 1 ∧ ∫ x, ρ x = 1 := by
  let f : ContDiffBump (1 / 2 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_, f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  change |x - 1/2| ≤ 1/4 at hx
  constructor <;> linarith [abs_le.mp hx]


lemma interval_integral_mul_test_eq_integral (f : ℝ → ℂ) {ψ : ℝ → ℝ}
    (hψ : tsupport ψ ⊆ Ioo (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, f x * (ψ x : ℂ)) = ∫ x, f x * (ψ x : ℂ) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hx ⟨(hψ h).1, (hψ h).2.le⟩)
  simp [hz]

lemma ae_const_of_weak_zero {H : ℝ → ℂ} (hH : IntervalIntegrable H volume 0 1)
    (h : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo (0 : ℝ) 1 →
        (∫ x in (0 : ℝ)..1, H x * ((deriv χ x : ℝ) : ℂ)) = 0) :
    ∃ c : ℂ, ∀ᵐ x ∂volume, x ∈ Ioo (0 : ℝ) 1 → H x = c := by
  obtain ⟨ρ, hρs, hρc, hρU, hρ1⟩ := exists_local_bump
  let c : ℂ := ∫ x in (0 : ℝ)..1, H x * (ρ x : ℂ)
  have hint (η : ℝ → ℝ) (hη : Continuous η) :
      IntervalIntegrable (fun x => H x * (η x : ℂ)) volume 0 1 :=
    hH.mul_continuousOn (Complex.continuous_ofReal.comp hη).continuousOn
  have key : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo (0 : ℝ) 1 →
        (∫ x, η x • (H x - c)) = 0 := by
    intro η hηs hηc hηU
    let m : ℝ := ∫ x, η x
    let ψ : ℝ → ℝ := fun x => η x - m * ρ x
    have hψs : ContDiff ℝ ∞ ψ := hηs.sub (contDiff_const.mul hρs)
    have hψc : HasCompactSupport ψ := hηc.sub hρc.mul_left
    have hψU : tsupport ψ ⊆ Ioo (0 : ℝ) 1 :=
      (tsupport_sub η (fun x => m * ρ x)).trans
        (union_subset hηU (tsupport_mul_subset_right.trans hρU))
    have hψ0 : ∫ x, ψ x = 0 := by
      dsimp [ψ]
      rw [integral_sub (hηs.continuous.integrable_of_hasCompactSupport hηc)
        ((hρs.continuous.integrable_of_hasCompactSupport hρc).const_mul m),
        integral_const_mul, hρ1]
      simp [m]
    obtain ⟨χ, hχs, hχc, hχU, hχd⟩ := exists_local_antideriv hψs hψc hψU hψ0
    have hzero := h χ hχs hχc hχU
    simp only [hχd] at hzero
    have e1 : (∫ x in (0 : ℝ)..1, H x * (ψ x : ℂ)) =
        (∫ x in (0 : ℝ)..1, H x * (η x : ℂ)) - (m : ℂ) * c := by
      have hpoint (x : ℝ) : H x * (ψ x : ℂ) =
          H x * (η x : ℂ) - (m : ℂ) * (H x * (ρ x : ℂ)) := by
        dsimp [ψ]
        push_cast
        ring
      simp_rw [hpoint]
      rw [intervalIntegral.integral_sub (hint η hηs.continuous)
        ((hint ρ hρs.continuous).const_mul _), intervalIntegral.integral_const_mul]
    have e2 : (∫ x, η x • (H x - c)) =
        (∫ x in (0 : ℝ)..1, H x * (η x : ℂ)) - c * (m : ℂ) := by
      have hpoint (x : ℝ) : η x • (H x - c) = (H x - c) * (η x : ℂ) := by
        rw [Complex.real_smul]
        ring
      have hηi : IntervalIntegrable (fun x => (η x : ℂ)) volume 0 1 :=
        (Complex.continuous_ofReal.comp hηs.continuous).intervalIntegrable _ _
      simp_rw [hpoint]
      rw [← interval_integral_mul_test_eq_integral _ hηU]
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (hint η hηs.continuous)
        (hηi.const_mul c),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
        ← integral_eq_interval_of_tsupport_subset hηU]
    rw [e2]
    rw [e1] at hzero
    linear_combination hzero
  have hi : IntegrableOn (fun x => H x - c) (Ioo (0 : ℝ) 1) volume := by
    exact (hH.def'.mono_set (by
      rw [uIoc_of_le zero_le_one]
      exact Ioo_subset_Ioc_self)).sub (integrableOn_const (by simp) (by simp))
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hi.locallyIntegrableOn key
  exact ⟨c, hae.mono (fun x hx hmem => sub_eq_zero.mp (hx hmem))⟩


/-- The L1 weak-derivative core, without any boundary relation. -/
theorem exists_ac_rep_of_weakDerivative {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hweak : Interval.HasWeakDerivative f g) :
    ∃ F : ℝ → ℂ, AbsolutelyContinuousOnInterval F 0 1 ∧
      f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] F ∧
      ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (g x) x := by
  let P : ℝ → ℂ := fun x => ∫ s in (0 : ℝ)..x, g s
  have hP : AbsolutelyContinuousOnInterval P 0 1 :=
    NlsGge.SpectralFoundations.complex_intervalIntegral_primitive_absolutelyContinuousV2
      hg left_mem_uIcc
  have hdP : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt P (g x) x := by
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hmem
    exact hx hmem 0 left_mem_uIcc
  have hzero : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo (0 : ℝ) 1 →
        (∫ x in (0 : ℝ)..1, (f x - P x) * ((deriv χ x : ℝ) : ℂ)) = 0 := by
    intro χ hχs hχc hχU
    have hχd (x : ℝ) : HasDerivAt (fun x => (χ x : ℂ)) ((deriv χ x : ℝ) : ℂ) x :=
      ((hχs.differentiable (by simp)) x).hasDerivAt.ofReal_comp
    have hχdi : IntervalIntegrable (fun x => ((deriv χ x : ℝ) : ℂ)) volume 0 1 :=
      (Complex.continuous_ofReal.comp (hχs.continuous_deriv (by simp))).intervalIntegrable _ _
    have hparts := NlsGge.SpectralFoundations.complex_ac_pointwise_test_integration_by_parts
      hP hg hdP (fun x _ => hχd x) hχdi
    have hχ0 : χ 0 = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (hχU h).1.false)
    have hχ1 : χ 1 = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl (1 : ℝ)) (hχU h).2)
    simp only [hχ0, hχ1, Complex.ofReal_zero, mul_zero, sub_self, zero_sub] at hparts
    have hχdc : Continuous (fun x => ((deriv χ x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hχs.continuous_deriv (by simp))
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub
      (hf.mul_continuousOn hχdc.continuousOn)
      (hχdi.continuousOn_mul hP.continuousOn), hweak χ hχs hχc hχU, hparts]
    exact sub_self _
  obtain ⟨c, hc⟩ := ae_const_of_weak_zero
    (hf.sub (hP.continuousOn.intervalIntegrable)) hzero
  let F : ℝ → ℂ := fun x => c + P x
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨F, hconst.add hP, ?_, ?_⟩
  · have h1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by simp [ae_iff]
    change ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), f x = F x
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hc, h1] with x hx hx1 hmem
    have := hx ⟨hmem.1, lt_of_le_of_ne hmem.2 hx1⟩
    dsimp [F]
    linear_combination this
  · filter_upwards [hdP] with x hx hmem
    exact (hx hmem).const_add c


lemma continuousRepresentative_unique {f : ℝ → ℂ}
    {F G : C(Icc (0 : ℝ) 1, ℂ)}
    (hF : IccExtend zero_le_one F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f)
    (hG : IccExtend zero_le_one G =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f) : F = G := by
  have hae : IccExtend zero_le_one F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      IccExtend zero_le_one G := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact hF.trans hG.symm
  have heq := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae
    F.continuous.Icc_extend'.continuousOn G.continuous.Icc_extend'.continuousOn
  ext x
  simpa only [IccExtend_val] using heq x.property

/-- An interval weak derivative determines a unique continuous representative on
the closed source interval. The representative is not chosen on a larger domain. -/
theorem existsUnique_continuousRepresentative_of_weakDerivative {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hweak : Interval.HasWeakDerivative f g) :
    ∃! F : C(Icc (0 : ℝ) 1, ℂ),
      IccExtend zero_le_one F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f := by
  obtain ⟨F, hFac, hFae, hFd⟩ := exists_ac_rep_of_weakDerivative hf hg hweak
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hFac.continuousOn
  let Fc : C(Icc (0 : ℝ) 1, ℂ) := ⟨_, hFc.domRestrict⟩
  have hrep : IccExtend zero_le_one Fc =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f := by
    filter_upwards [hFae, ae_restrict_mem measurableSet_Ioc] with x hx hmem
    rw [IccExtend_of_mem zero_le_one Fc ⟨hmem.1.le, hmem.2⟩]
    exact hx.symm
  exact ⟨Fc, hrep, fun G hG => continuousRepresentative_unique hG hrep⟩

lemma intervalIntegrable_L2 (f : NlsGge.Schur.SourceIntervalL2) :
    IntervalIntegrable (fun x => f x) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    ((Lp.memLp f).integrable (by norm_num))

/-- Existence and uniqueness of the actual interval H1 continuous representative. -/
theorem interval_h1_existsUnique_continuousRepresentative (f : Interval.H1) :
    ∃! F : C(Icc (0 : ℝ) 1, ℂ),
      IccExtend zero_le_one F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f.value :=
  existsUnique_continuousRepresentative_of_weakDerivative
    (intervalIntegrable_L2 f.value) (intervalIntegrable_L2 f.derivative) f.weak

/-- The unique continuous representative, on precisely the closed source interval. -/
def representative (f : Interval.H1) : C(Icc (0 : ℝ) 1, ℂ) :=
  Classical.choose (interval_h1_existsUnique_continuousRepresentative f).exists

theorem representative_ae (f : Interval.H1) :
    IccExtend zero_le_one (representative f) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f.value :=
  Classical.choose_spec (interval_h1_existsUnique_continuousRepresentative f).exists

theorem representative_eq_of_ae (f : Interval.H1) (F : C(Icc (0 : ℝ) 1, ℂ))
    (hF : IccExtend zero_le_one F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f.value) :
    F = representative f :=
  continuousRepresentative_unique hF (representative_ae f)

/-- The continuous representative is AC and has the given L2 weak derivative a.e. -/
theorem representative_spec (f : Interval.H1) :
    AbsolutelyContinuousOnInterval (IccExtend zero_le_one (representative f)) 0 1 ∧
      ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 →
        HasDerivAt (IccExtend zero_le_one (representative f)) (f.derivative x) x := by
  obtain ⟨F, hFac, hFae, hFd⟩ := exists_ac_rep_of_weakDerivative
    (intervalIntegrable_L2 f.value) (intervalIntegrable_L2 f.derivative) f.weak
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hFac.continuousOn
  have hae : F =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      IccExtend zero_le_one (representative f) := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact hFae.symm.trans (representative_ae f).symm
  have heq := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae hFc
    (representative f).continuous.Icc_extend'.continuousOn
  constructor
  · exact hFac.congr (by simpa only [uIcc_of_le zero_le_one] using heq)
  · have h0 : ∀ᵐ x ∂volume, x ≠ (0 : ℝ) := by simp [ae_iff]
    have h1 : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := by simp [ae_iff]
    filter_upwards [hFd, h0, h1] with x hd hx0 hx1 hmem
    have hmem' : x ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using hmem
    apply (hd hmem).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne hmem'.1 hx0.symm)
      (lt_of_le_of_ne hmem'.2 hx1)] with s hs
    exact (heq ⟨hs.1.le, hs.2.le⟩).symm


/-- A quantitative trace estimate already at W1,1 regularity. -/
theorem ac_norm_le_integral_norm_add_derivative {F g : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (g x) x)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖F x‖ ≤ (∫ s in (0 : ℝ)..1, ‖F s‖) + ∫ s in (0 : ℝ)..1, ‖g s‖ := by
  obtain ⟨s, hs, havg⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := (volume : Measure ℝ))
    hF.continuousOn.norm (intervalIntegrable_const (c := (1 : ℝ)))
    (fun _ _ => zero_le_one)
  have hmean : (∫ s in (0 : ℝ)..1, ‖F s‖) = ‖F s‖ := by simpa using havg
  have hx' : x ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hx
  have hsub : uIcc s x ⊆ uIcc (0 : ℝ) 1 := uIcc_subset_uIcc hs hx'
  have hid := NlsGge.SpectralFoundations.complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    (hF.mono hsub) (hg.mono_set hsub)
    (hd.mono (fun y hy hmem => hy (hsub hmem))) x right_mem_uIcc
  have hnorm : ‖∫ t in s..x, g t‖ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ := by
    have hmono := setIntegral_mono_set hg.norm.def'
      (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun t ht => uIoc_subset_uIoc_of_uIcc_subset_uIcc hsub ht))
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (hmono.trans_eq (by rw [uIoc_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]))
  rw [hid, hmean]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hnorm)

lemma integral_norm_L2_le (f : NlsGge.Schur.SourceIntervalL2) :
    (∫ x in (0 : ℝ)..1, ‖f x‖) ≤ ‖f‖ := by
  let : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [intervalIntegral.integral_of_le zero_le_one,
    integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def,
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- Every point evaluation, including both endpoint traces, has the same H1 bound. -/
theorem representative_norm_le (f : Interval.H1) (x : Icc (0 : ℝ) 1) :
    ‖representative f x‖ ≤ ‖f.value‖ + ‖f.derivative‖ := by
  have hb := ac_norm_le_integral_norm_add_derivative (representative_spec f).1
    (intervalIntegrable_L2 f.derivative) (representative_spec f).2 x.property
  have hi : (∫ s in (0 : ℝ)..1, ‖IccExtend zero_le_one (representative f) s‖) =
      ∫ s in (0 : ℝ)..1, ‖f.value s‖ := by
    apply intervalIntegral.integral_congr_ae_restrict
    simpa only [uIoc_of_le zero_le_one, Function.comp_def] using (representative_ae f).fun_comp norm
  rw [IccExtend_val, hi] at hb
  exact hb.trans (add_le_add (integral_norm_L2_le f.value) (integral_norm_L2_le f.derivative))

/-- Left endpoint trace of the unique continuous representative. -/
def traceLeft (f : Interval.H1) : ℂ := representative f ⟨0, by norm_num⟩

/-- Right endpoint trace of the unique continuous representative. -/
def traceRight (f : Interval.H1) : ℂ := representative f ⟨1, by norm_num⟩

theorem traceLeft_norm_le (f : Interval.H1) :
    ‖traceLeft f‖ ≤ ‖f.value‖ + ‖f.derivative‖ :=
  representative_norm_le f ⟨0, by norm_num⟩

theorem traceRight_norm_le (f : Interval.H1) :
    ‖traceRight f‖ ≤ ‖f.value‖ + ‖f.derivative‖ :=
  representative_norm_le f ⟨1, by norm_num⟩


set_option backward.isDefEq.respectTransparency false in
/-- Conjugate integration by parts for complex AC functions with integrable
almost-everywhere derivatives. -/
theorem ac_conjugate_integrationByParts {F G F' G' : ℝ → ℂ}
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hG : AbsolutelyContinuousOnInterval G 0 1)
    (hF' : IntervalIntegrable F' volume 0 1)
    (hG' : IntervalIntegrable G' volume 0 1)
    (hdF : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt F (F' x) x)
    (hdG : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt G (G' x) x) :
    (∫ x in (0 : ℝ)..1, star (F' x) * G x + star (F x) * G' x) =
      star (F 1) * G 1 - star (F 0) * G 0 := by
  have hstar : AbsolutelyContinuousOnInterval (fun x => star (F x)) 0 1 := by
    simpa only [Function.comp_def] using!
      Complex.conjLIE.lipschitz.comp_absolutelyContinuousOnInterval hF
  have hprod : AbsolutelyContinuousOnInterval (fun x => star (F x) * G x) 0 1 := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hstar.smul hG
  have hi1 : IntervalIntegrable (fun x => star (F' x) * G x) volume 0 1 :=
    (intervalIntegrable_iff.mpr
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp hF'.def')).mul_continuousOn
        hG.continuousOn
  have hi2 : IntervalIntegrable (fun x => star (F x) * G' x) volume 0 1 :=
    hG'.continuousOn_mul hstar.continuousOn
  have hdprod : ∀ᵐ x ∂volume, x ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun x => star (F x) * G x) (star (F' x) * G x + star (F x) * G' x) x := by
    filter_upwards [hdF, hdG] with x hx hy hmem
    exact (hx hmem).star.mul (hy hmem)
  have heq := NlsGge.SpectralFoundations.complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    hprod (hi1.add hi2) hdprod 1 right_mem_uIcc
  linear_combination -heq

/-- Both derivative-product terms in the H1 Green pairing are genuinely integrable. -/
theorem interval_h1_pairing_integrable (f g : Interval.H1) :
    IntervalIntegrable (fun x => star (f.derivative x) * g.value x +
      star (f.value x) * g.derivative x) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  exact ((Lp.memLp f.derivative).star.integrable_mul (Lp.memLp g.value)).add
    ((Lp.memLp f.value).star.integrable_mul (Lp.memLp g.derivative))

/-- The source conjugate integration-by-parts identity for arbitrary interval H1
functions. No relation between either pair of endpoint traces is imposed. -/
theorem interval_h1_integrationByParts (f g : Interval.H1) :
    (∫ x in (0 : ℝ)..1, star (f.derivative x) * g.value x +
      star (f.value x) * g.derivative x) =
        star (traceRight f) * traceRight g - star (traceLeft f) * traceLeft g := by
  have hi := interval_h1_pairing_integrable f g
  have hparts := ac_conjugate_integrationByParts (representative_spec f).1
    (representative_spec g).1 (intervalIntegrable_L2 f.derivative)
    (intervalIntegrable_L2 g.derivative) (representative_spec f).2 (representative_spec g).2
  have heq : (∫ x in (0 : ℝ)..1, star (f.derivative x) * g.value x +
      star (f.value x) * g.derivative x) =
      ∫ x in (0 : ℝ)..1, star (f.derivative x) * IccExtend zero_le_one (representative g) x +
        star (IccExtend zero_le_one (representative f) x) * g.derivative x := by
    apply intervalIntegral.integral_congr_ae_restrict
    have hf : (fun x => IccExtend zero_le_one (representative f) x) =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
        (fun x => f.value x) := by
      simpa only [uIoc_of_le zero_le_one] using representative_ae f
    have hg : (fun x => IccExtend zero_le_one (representative g) x) =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
        (fun x => g.value x) := by
      simpa only [uIoc_of_le zero_le_one] using representative_ae g
    filter_upwards [hf, hg] with x hx hy
    rw [hx, hy]
  rw [heq, hparts]
  simp only [IccExtend_right, IccExtend_left, traceRight, traceLeft]

end NlsGge.Atomic.LIB026
