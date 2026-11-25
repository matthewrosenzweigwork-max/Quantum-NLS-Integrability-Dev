import QuantumNLS.Prop010SingleContourR17

/-!
# R-52CF5DA1 stage 12a: the frozen denominator `D_v` on the fixed rectangles near a rough center

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraphs "By continuity of the transfer and
its spectral derivatives, a fixed open neighborhood of `u_*` gives a common positive probe margin, fixed cutoff
neighborhoods, and a positive contour lower bound on `|D_v|` for every unit `v` in that neighborhood" and, from
`lem:audit-scalar-period`, "The identity `a² - wa + e^{izL} = 0` gives `∂_w log a = 1/D`".

* `hasDerivAt_localLog_gen`: the local logarithm of the background `g` (eq:B4-local-functions) has, at the transfer
  value of a nearby background `g'` (on the same root branch), the complex derivative `1/D(g')`
  (quadratic relation `a² - wa + e = 0` differentiated, no new hypothesis on the branch beyond the branch conditions);
* `eventually_hasDerivAt`: these branch conditions hold for all backgrounds near a regular one;
* `Df_eq`, `continuousAt_Df`, `continuousOn_Dinv`: `D_v = A_v - e^{izL}/A_v` is continuous and nonvanishing at the
  regular points of `v`;
* **`local_label`** / **`local_denominators`**: for a unit rough center `u` and the accepted PROP-010 extensions
  `F_n` of `u` (tube agreement with `λ(z,·)` of `u` of radius `r_n` on `Γ_n`), there are constants `m_n > 0`, `S_n` and
  ONE neighborhood of `u` on which, for every `n ∈ F` and `z ∈ Γ_n`: `(v,z)` is regular, `m_n ≤ |D_v(z)|`,
  `|s(z;v)| ≤ S_n`, and `w ↦ F_n(z,w)` has complex derivative `D_v(z)⁻¹` at `w = s(z;v)`.
No hypothesis is added; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology Complex

namespace QuantumNLS.R52CFDenom

section Generic
open ScalarLogBranchR10

/-- The derivative of the local logarithm of `g` at the transfer value of a nearby background `g'`. -/
theorem hasDerivAt_localLog_gen (e g g' : ℂ) (hD : difference e g ≠ 0) (hD' : difference e g' ≠ 0)
    (hroot : root e g (transfer e g') = exp g')
    (hq : 1 + ((transfer e g') ^ 2 - (transfer e g) ^ 2) / (difference e g) ^ 2 ∈ slitPlane)
    (hl : exp g' / exp g ∈ slitPlane) :
    HasDerivAt (localLog e g) (difference e g')⁻¹ (transfer e g') := by
  have hw : HasDerivAt (fun w : ℂ => 1 + (w ^ 2 - (transfer e g) ^ 2) / (difference e g) ^ 2)
      ((2 * transfer e g') / (difference e g) ^ 2) (transfer e g') := by
    simpa using (((hasDerivAt_id (transfer e g')).pow 2).sub_const ((transfer e g) ^ 2)
      |>.div_const ((difference e g) ^ 2)).const_add 1
  have hp := hw.cpow_const (c := (2:ℂ)⁻¹) hq
  have hr0 := ((hasDerivAt_id (transfer e g')).add (hp.const_mul (difference e g))).div_const 2
  obtain ⟨r', hr⟩ : ∃ r', HasDerivAt (root e g) r' (transfer e g') := ⟨_, hr0⟩
  have hc : HasDerivAt (fun w => root e g w ^ 2 - w * root e g w + e) 0 (transfer e g') := by
    have hfun : (fun w => root e g w ^ 2 - w * root e g w + e) = fun _ => (0 : ℂ) :=
      funext fun w => root_quadratic e g w hD
    rw [hfun]
    exact hasDerivAt_const _ _
  have hd2 := ((hr.pow 2).sub ((hasDerivAt_id (transfer e g')).mul hr)).add_const e
  have hrel := hd2.unique hc
  rw [hroot] at hrel
  have hrel' : 2 * exp g' * r' - (exp g' + transfer e g' * r') = 0 := by
    simpa using hrel
  have hrd : r' * difference e g' = exp g' := by
    have hw0 : transfer e g' = exp g' + e / exp g' := rfl
    rw [hw0] at hrel'
    unfold difference
    linear_combination hrel'
  have hsl : root e g (transfer e g') / exp g ∈ slitPlane := by rw [hroot]; exact hl
  have hlog := ((hr.div_const (exp g)).clog hsl).const_add g
  refine hlog.congr_deriv ?_
  rw [hroot, div_div_div_cancel_right₀ (exp_ne_zero g)]
  calc r' / exp g' = r' * difference e g' / (exp g' * difference e g') := by
        rw [mul_div_mul_right _ _ hD']
    _ = (difference e g')⁻¹ := by
        rw [hrd, div_mul_eq_div_div, div_self (exp_ne_zero g'), one_div]

/-- The branch conditions of `hasDerivAt_localLog_gen` hold near a regular background. -/
theorem eventually_hasDerivAt {X : Type*} [TopologicalSpace X] {e g v : X → ℂ} {x : X}
    (he : ContinuousAt e x) (hg : ContinuousAt g x) (hv : ContinuousAt v x)
    (hbase : v x = g x) (hD : difference (e x) (g x) ≠ 0) :
    ∀ᶠ y in 𝓝 x, HasDerivAt (localLog (e y) (g y)) (difference (e y) (v y))⁻¹
      (transfer (e y) (v y)) := by
  have ht : ContinuousAt (fun y => transfer (e y) (v y)) x :=
    hv.cexp.add (he.div hv.cexp (exp_ne_zero _))
  have htg : ContinuousAt (fun y => transfer (e y) (g y)) x :=
    hg.cexp.add (he.div hg.cexp (exp_ne_zero _))
  have hr := continuousAt_root he hg ht hD (by rw [hbase])
  have hd : ContinuousAt (fun y => difference (e y) (g y)) x :=
    hg.cexp.sub (he.div hg.cexp (exp_ne_zero _))
  have hdv : ContinuousAt (fun y => difference (e y) (v y)) x :=
    hv.cexp.sub (he.div hv.cexp (exp_ne_zero _))
  have hne : root (e x) (g x) (transfer (e x) (v x)) ≠ e x / exp (v x) := by
    rw [hbase, root_at]
    exact sub_ne_zero.mp hD
  have hn := (hr.sub (he.div hv.cexp (exp_ne_zero _))).eventually_ne (sub_ne_zero.mpr hne)
  have hdne := hd.eventually_ne hD
  have hdvne := hdv.eventually_ne (by rw [hbase]; exact hD)
  have hq : ∀ᶠ y in 𝓝 x, 1 + ((transfer (e y) (v y)) ^ 2 - (transfer (e y) (g y)) ^ 2) /
      (difference (e y) (g y)) ^ 2 ∈ slitPlane := by
    have hc : ContinuousAt (fun y => 1 + ((transfer (e y) (v y)) ^ 2 - (transfer (e y) (g y)) ^ 2) /
        (difference (e y) (g y)) ^ 2) x :=
      continuousAt_const.add (((ht.pow 2).sub (htg.pow 2)).div (hd.pow 2) (pow_ne_zero 2 hD))
    apply hc.eventually_mem (isOpen_slitPlane.mem_nhds _)
    simp [hbase, Complex.slitPlane]
  have hl : ∀ᶠ y in 𝓝 x, exp (v y) / exp (g y) ∈ slitPlane := by
    have hc : ContinuousAt (fun y => exp (v y) / exp (g y)) x := hv.cexp.div hg.cexp (exp_ne_zero _)
    apply hc.eventually_mem (isOpen_slitPlane.mem_nhds _)
    show exp (v x) / exp (g x) ∈ slitPlane
    rw [hbase, div_self (exp_ne_zero _)]
    exact one_mem_slitPlane
  filter_upwards [hn, hdne, hdvne, hq, hl] with y hy hdy hdvy hqy hly
  have hq2 := root_quadratic (e y) (g y) (transfer (e y) (v y)) hdy
  have hf : (root (e y) (g y) (transfer (e y) (v y)) - exp (v y)) *
      (root (e y) (g y) (transfer (e y) (v y)) - e y / exp (v y)) = 0 := by
    rw [← hq2]
    unfold transfer
    field_simp
    ring
  have ha : root (e y) (g y) (transfer (e y) (v y)) = exp (v y) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hy)
  exact hasDerivAt_localLog_gen (e y) (g y) (v y) hdy hdvy ha hqy hly

/-- A positive continuous function on a compact set has a positive lower bound. -/
theorem exists_pos_lower {K : Set ℂ} (hK : IsCompact K) {f : ℂ → ℝ} (hf : ContinuousOn f K)
    (hpos : ∀ z ∈ K, 0 < f z) : ∃ m > 0, ∀ z ∈ K, m ≤ f z := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun z hz => by simp [he] at hz⟩
  · obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f z0, hpos z0 hz0, fun z hz => isMinOn_iff.mp hmin z hz⟩

end Generic

section Physical
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootScalarPeriodR8 (cut)
open PeriodReconstruction (Gam isCompact_Gam)
open PeriodReconstructionCore (Df sf)

variable {L κ : ℝ} [Fact (0 < L)]

theorem Df_eq (hκ : 0 < κ) (v : L2T L) (z : ℂ) :
    Df L κ (fun z => G hκ z v) z =
      ScalarLogBranchR10.difference (RootScalarPeriodR10.exponential L z)
        (RootScalarPeriodR10.exponent hκ v z) := by
  simp only [Df, PeriodReconstructionCore.Af, ScalarLogBranchR10.difference, RootScalarPeriodR10.exponent,
    ← Prop010CutoffExistenceR11.ef_exp]

theorem continuousAt_G (hκ : 0 < κ) (v : L2T L) {z : ℂ} (hz : Regular κ (v, z)) :
    ContinuousAt (fun z => G hκ z v) z :=
  (RootCauchyJointR9.continuousAt_joint_regular hκ (v, z) hz).comp (f := fun z : ℂ => (v, z))
    (continuous_const.prodMk continuous_id).continuousAt

theorem continuousAt_Df (hκ : 0 < κ) (v : L2T L) {z : ℂ} (hz : Regular κ (v, z)) :
    ContinuousAt (fun z => Df L κ (fun z => G hκ z v) z) z := by
  have hG := continuousAt_G hκ v hz
  have hA : ContinuousAt (fun z => exp (I * κ * G hκ z v)) z := (hG.const_mul (I * (κ : ℂ))).cexp
  have he : ContinuousAt (fun z : ℂ => exp (I * L * z)) z :=
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt
  exact hA.sub (he.div hA (exp_ne_zero _))

theorem Df_ne (hκ : 0 < κ) (v : L2T L) {z : ℂ} (hz : Regular κ (v, z)) :
    Df L κ (fun z => G hκ z v) z ≠ 0 := by
  rw [Df_eq]
  exact RootScalarPeriodR10.difference_ne hκ v z hz

/-- `z ↦ D_v(z)⁻¹` is continuous on every set of regular points of `v`. -/
theorem continuousOn_Dinv (hκ : 0 < κ) (v : L2T L) {K : Set ℂ} (hK : ∀ z ∈ K, Regular κ (v, z)) :
    ContinuousOn (fun z => (Df L κ (fun z => G hκ z v) z)⁻¹) K := fun z hz =>
  ((continuousAt_Df hκ v (hK z hz)).inv₀ (Df_ne hκ v (hK z hz))).continuousWithinAt

/-- **One label.** -/
theorem local_label (hκ : 0 < κ) (u : L2T L) (n : ℤ) {h r : ℝ} (hh : 0 < h) (hr : 0 < r)
    (Fe : ℂ × ℂ → ℂ)
    (hf : ∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h, ∀ w,
      ‖w - sf L κ (fun z => G hκ z u) z‖ < r →
        Fe (z, w) = Prop010ContourBindingR11.localLog L κ (fun z => G hκ z u) z w) :
    ∃ m S : ℝ, 0 < m ∧ ∀ᶠ v in 𝓝 u, ∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,
      Regular κ (v, z) ∧ m ≤ ‖Df L κ (fun z => G hκ z v) z‖ ∧
      ‖NormalizedTransfer.productSymbol L κ v z‖ ≤ S ∧
      HasDerivAt (fun w => Fe (z, w)) (Df L κ (fun z => G hκ z v) z)⁻¹
        (NormalizedTransfer.productSymbol L κ v z) := by
  set Γ := Gam (cut hκ u (n-1)) (cut hκ u n) h with hΓ
  have hK : IsCompact Γ := isCompact_Gam _ _ _
  have hreg : ∀ z ∈ Γ, Regular κ (u, z) := fun z hz =>
    Prop010CutoffExistenceR11.rectangle_regular L hκ u n hh hz
  have hc0 : Continuous (fun p : L2T L × ℂ => RootScalarPeriodR10.symbol κ p.1 p.2) := by
    simp_rw [Prop010ClassicalR10.symbol_eq_trace hκ]
    have hd : Continuous (fun p : L2T L × ℂ => L2SpatialTransfer.discriminant κ p.1 p.2) :=
      continuous_iff_continuousAt.mpr fun p =>
        (DEF014DiscriminantAnalytic.analyticAt_discriminant_joint κ p).continuousAt
    exact (by fun_prop : Continuous (fun p : L2T L × ℂ => exp (I*p.2*L/2))).mul hd
  have hc : Continuous (fun p : L2T L × ℂ => NormalizedTransfer.productSymbol L κ p.1 p.2) := hc0
  have hDu : ContinuousOn (fun z => ‖Df L κ (fun z => G hκ z u) z‖) Γ := fun z hz =>
    (continuousAt_Df hκ u (hreg z hz)).norm.continuousWithinAt
  have hDpos : ∀ z ∈ Γ, 0 < ‖Df L κ (fun z => G hκ z u) z‖ := fun z hz =>
    norm_pos_iff.mpr (Df_ne hκ u (hreg z hz))
  obtain ⟨m0, hm0, hm0le⟩ := exists_pos_lower hK hDu hDpos
  have hcu : Continuous (fun z : ℂ => NormalizedTransfer.productSymbol L κ u z) :=
    hc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨S0, hS0⟩ := hK.exists_bound_of_continuousOn hcu.continuousOn
  refine ⟨m0 / 2, S0 + r, half_pos hm0, ?_⟩
  have key : ∀ᶠ v in 𝓝 u, ∀ z ∈ Γ, z ∈ Γ →
      (Regular κ (v, z) ∧ m0 / 2 ≤ ‖Df L κ (fun z => G hκ z v) z‖ ∧
        ‖NormalizedTransfer.productSymbol L κ v z‖ ≤ S0 + r ∧
        HasDerivAt (fun w => Fe (z, w)) (Df L κ (fun z => G hκ z v) z)⁻¹
          (NormalizedTransfer.productSymbol L κ v z)) := by
    apply hK.eventually_forall_of_forall_eventually
    intro z0 hz0
    have hr0 := hreg z0 hz0
    have e1 : ∀ᶠ p : L2T L × ℂ in 𝓝 (u, z0), Regular κ p :=
      (RootCauchyJointR9.isOpen_regular κ).mem_nhds hr0
    have hcs : Continuous (fun p : L2T L × ℂ => NormalizedTransfer.productSymbol L κ u p.2) :=
      hc.comp (continuous_const.prodMk continuous_snd)
    have e2 : ∀ᶠ p : L2T L × ℂ in 𝓝 (u, z0),
        ‖NormalizedTransfer.productSymbol L κ p.1 p.2 - NormalizedTransfer.productSymbol L κ u p.2‖ < r :=
      (hc.sub hcs).norm.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
    have hg : ContinuousAt (fun p : L2T L × ℂ => RootScalarPeriodR10.exponent hκ u p.2) (u, z0) := by
      have hj : ContinuousAt (fun p : L2T L × ℂ => (u, p.2)) (u, z0) :=
        (continuous_const.prodMk continuous_snd).continuousAt
      exact ((RootCauchyJointR9.continuousAt_joint_regular hκ (u, z0) hr0).comp
        (f := fun p : L2T L × ℂ => (u, p.2)) hj).const_mul (I * (κ : ℂ))
    have hv : ContinuousAt (fun p : L2T L × ℂ => RootScalarPeriodR10.exponent hκ p.1 p.2) (u, z0) :=
      (RootCauchyJointR9.continuousAt_joint_regular hκ (u, z0) hr0).const_mul (I * (κ : ℂ))
    have he : ContinuousAt (fun p : L2T L × ℂ => RootScalarPeriodR10.exponential L p.2) (u, z0) := by
      unfold RootScalarPeriodR10.exponential
      exact (by fun_prop : Continuous (fun p : L2T L × ℂ => exp (I * p.2 * (L : ℂ)))).continuousAt
    have e3 := eventually_hasDerivAt he hg hv rfl (RootScalarPeriodR10.difference_ne hκ u z0 hr0)
    have hDv : ContinuousAt (fun p : L2T L × ℂ => ScalarLogBranchR10.difference
        (RootScalarPeriodR10.exponential L p.2) (RootScalarPeriodR10.exponent hκ p.1 p.2)) (u, z0) :=
      hv.cexp.sub (he.div hv.cexp (exp_ne_zero _))
    have e4 : ∀ᶠ p : L2T L × ℂ in 𝓝 (u, z0), m0 / 2 < ‖ScalarLogBranchR10.difference
        (RootScalarPeriodR10.exponential L p.2) (RootScalarPeriodR10.exponent hκ p.1 p.2)‖ := by
      apply hDv.norm.eventually (lt_mem_nhds _)
      have h1 := hm0le z0 hz0
      rw [Df_eq] at h1
      show m0 / 2 < ‖ScalarLogBranchR10.difference (RootScalarPeriodR10.exponential L z0)
        (RootScalarPeriodR10.exponent hκ u z0)‖
      linarith
    filter_upwards [e1, e2, e3, e4] with p hp1 hp2 hp3 hp4
    intro hpz
    have hsym : NormalizedTransfer.productSymbol L κ p.1 p.2 =
        ScalarLogBranchR10.transfer (RootScalarPeriodR10.exponential L p.2)
          (RootScalarPeriodR10.exponent hκ p.1 p.2) :=
      RootScalarPeriodR10.transfer_identity hκ p.1 p.2 hp1
    have hsu : sf L κ (fun z => G hκ z u) p.2 = NormalizedTransfer.productSymbol L κ u p.2 :=
      Prop010SingleContourR17.background_eq_symbol hκ u p.2 (hreg p.2 hpz)
    have hd : HasDerivAt (ScalarLogBranchR10.localLog (RootScalarPeriodR10.exponential L p.2)
        (RootScalarPeriodR10.exponent hκ u p.2)) (Df L κ (fun z => G hκ z p.1) p.2)⁻¹
        (NormalizedTransfer.productSymbol L κ p.1 p.2) := by
      rw [Df_eq, hsym]
      exact hp3
    have htube : ‖NormalizedTransfer.productSymbol L κ p.1 p.2 - sf L κ (fun z => G hκ z u) p.2‖ < r := by
      rw [hsu]; exact hp2
    have hev : (fun w => Fe (p.2, w)) =ᶠ[𝓝 (NormalizedTransfer.productSymbol L κ p.1 p.2)]
        ScalarLogBranchR10.localLog (RootScalarPeriodR10.exponential L p.2)
          (RootScalarPeriodR10.exponent hκ u p.2) := by
      have hmem : Metric.ball (sf L κ (fun z => G hκ z u) p.2) r ∈
          𝓝 (NormalizedTransfer.productSymbol L κ p.1 p.2) :=
        Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm]; exact htube)
      filter_upwards [hmem] with w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact (hf p.2 hpz w hw).trans (Prop010SingleContourR17.log_eq_lambda hκ u p.2 w)
    refine ⟨hp1, ?_, ?_, hd.congr_of_eventuallyEq hev⟩
    · rw [Df_eq]
      exact hp4.le
    · have hb := hS0 p.2 hpz
      have hb' : ‖NormalizedTransfer.productSymbol L κ u p.2‖ ≤ S0 := hb
      have ht := norm_sub_norm_le (NormalizedTransfer.productSymbol L κ p.1 p.2)
        (NormalizedTransfer.productSymbol L κ u p.2)
      linarith
  filter_upwards [key] with v hv z hz
  exact hv z hz hz

/-- **All labels of a finite set, on one neighborhood.** -/
theorem local_denominators (hκ : 0 < κ) (u : L2T L) (Fs : Finset ℤ) {h : ℝ} (hh : 0 < h)
    (r : ℤ → ℝ) (hr : ∀ n, 0 < r n) (Fe : ℤ → ℂ × ℂ → ℂ)
    (hf : ∀ n, ∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h, ∀ w,
      ‖w - sf L κ (fun z => G hκ z u) z‖ < r n →
        Fe n (z, w) = Prop010ContourBindingR11.localLog L κ (fun z => G hκ z u) z w) :
    ∃ m S : ℤ → ℝ, (∀ n, 0 < m n) ∧ ∀ᶠ v in 𝓝 u, ∀ n ∈ Fs,
      ∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,
      Regular κ (v, z) ∧ m n ≤ ‖Df L κ (fun z => G hκ z v) z‖ ∧
      ‖NormalizedTransfer.productSymbol L κ v z‖ ≤ S n ∧
      HasDerivAt (fun w => Fe n (z, w)) (Df L κ (fun z => G hκ z v) z)⁻¹
        (NormalizedTransfer.productSymbol L κ v z) := by
  have hloc := fun n => local_label hκ u n hh (hr n) (Fe n) (hf n)
  choose m S hmS using hloc
  exact ⟨m, S, fun n => (hmS n).1, (Filter.eventually_all_finset Fs).mpr fun n _ => (hmS n).2⟩

end Physical

end QuantumNLS.R52CFDenom

#print axioms QuantumNLS.R52CFDenom.hasDerivAt_localLog_gen
#print axioms QuantumNLS.R52CFDenom.local_label
#print axioms QuantumNLS.R52CFDenom.local_denominators
