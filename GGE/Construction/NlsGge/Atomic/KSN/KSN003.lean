import Mathlib

   
                                                                                                                                                                     
                                                 
                                                                                      
                                    
                                                                                                          
                                                                     
                                                                                                        
                                                                                               
                                                                                         
                                                                                    
  
set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace NlsGge.Atomic.KSN003Design

/-- The cut `G = [a,b]`: the closed complex segment between the two endpoints. -/
def gapCut (a b : ℂ) : Set ℂ := segment ℝ a b

/-- The cut domain `C \ [a,b]`. -/
def cutDomain (a b : ℂ) : Set ℂ := (gapCut a b)ᶜ

/-- A square-root sheet for the pair `(a,b)`: an analytic function on the cut domain whose
square is `(b - z) * (a - z)` (exactly two exist; the source's starred root is a chosen sign). -/
structure IsSquareRootSheet (a b : ℂ) (s : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ s (cutDomain a b)
  sq : ∀ z ∈ cutDomain a b, s z ^ 2 = (b - z) * (a - z)

/-- `c` is a finite concatenation of `C^1` arcs on the parameter interval `[p,q]`
(each arc is `C^1` on a closed subinterval, with one-sided derivatives at its ends). -/
inductive PiecewiseC1On (c : ℝ → ℂ) : ℝ → ℝ → Prop
  | arc {p q : ℝ} (hpq : p ≤ q) (hc : ContDiffOn ℝ 1 c (Icc p q)) : PiecewiseC1On c p q
  | trans {p m q : ℝ} (h₁ : p ≤ m) (h₂ : m ≤ q) :
      PiecewiseC1On c p m → PiecewiseC1On c m q → PiecewiseC1On c p q

/-- A piecewise `C^1` path from the endpoint `a` to `mu` that leaves the cut at once: it starts at
`a`, ends at `mu`, and lies in the cut domain for every positive time. -/
def IsGapPath (a b mu : ℂ) (c : ℝ → ℂ) : Prop :=
  c 0 = a ∧ c 1 = mu ∧ PiecewiseC1On c 0 1 ∧ ∀ t ∈ Ioc (0 : ℝ) 1, c t ∈ cutDomain a b

/-- The improper path integral `int_a^mu dlambda / s(lambda)` along `c` converges to `I`: the
integrals over `[delta,1]` (continuous integrands off the finitely many corners, no junk branch)
tend to `I` as `delta -> 0+`. -/
def HasGapIntegral (s : ℂ → ℂ) (c : ℝ → ℂ) (I : ℂ) : Prop :=
  Tendsto (fun δ : ℝ => ∫ t in δ..1, deriv c t / s (c t)) (𝓝[>] 0) (𝓝 I)


private lemma isOpen_cutDomain (a b : ℂ) : IsOpen (cutDomain a b) := by
  have hc : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  exact hc.isClosed.isOpen_compl

private lemma ne_of_mem_cutDomain {a b z : ℂ} (hz : z ∈ cutDomain a b) : z ≠ a ∧ z ≠ b := by
  constructor
  · rintro rfl
    exact hz (left_mem_segment ℝ _ _)
  · rintro rfl
    exact hz (right_mem_segment ℝ _ _)

private lemma sheet_ne_zero {a b : ℂ} {S : ℂ → ℂ} (hS : IsSquareRootSheet a b S) {z : ℂ}
    (hz : z ∈ cutDomain a b) : S z ≠ 0 := by
  intro h
  have h2 := hS.sq z hz
  rw [h] at h2
  have h4 := ne_of_mem_cutDomain hz
  have h3 : (b - z) * (a - z) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 h4.2.symm) (sub_ne_zero.2 h4.1.symm)
  apply h3
  rw [← h2]
  simp

private def gapF (a b : ℂ) (S : ℂ → ℂ) (ε : ℂ) (z : ℂ) : ℂ := ((a + b) / 2 - z) - ε * S z

private lemma sheet_hasDerivAt {a b : ℂ} {S : ℂ → ℂ} (hS : IsSquareRootSheet a b S) {z : ℂ}
    (hz : z ∈ cutDomain a b) :
    HasDerivAt S (deriv S z) z ∧ S z * deriv S z = -((a + b) / 2 - z) := by
  have hd : DifferentiableAt ℂ S z := (hS.analytic z hz).differentiableAt
  have hSd : HasDerivAt S (deriv S z) z := hd.hasDerivAt
  refine ⟨hSd, ?_⟩
  have h1 : HasDerivAt (fun w => S w * S w) (deriv S z * S z + S z * deriv S z) z := hSd.mul hSd
  have h3 := ((hasDerivAt_id' z).const_sub b).mul ((hasDerivAt_id' z).const_sub a)
  have heq : (fun w : ℂ => (b - w) * (a - w)) =ᶠ[𝓝 z] (fun w => S w * S w) := by
    filter_upwards [(isOpen_cutDomain a b).mem_nhds hz] with w hw
    rw [← pow_two]
    exact (hS.sq w hw).symm
  have h4 := h1.congr_of_eventuallyEq heq
  have h5 := h4.unique h3
  linear_combination (1 / 2 : ℂ) * h5

private lemma gapF_hasDerivAt {a b : ℂ} {S : ℂ → ℂ} (hS : IsSquareRootSheet a b S) {ε : ℂ}
    (hεε : ε * ε = 1) {z : ℂ} (hz : z ∈ cutDomain a b) :
    HasDerivAt (gapF a b S ε) (ε * gapF a b S ε z / S z) z := by
  obtain ⟨hSd, hd⟩ := sheet_hasDerivAt hS hz
  have hS0 := sheet_ne_zero hS hz
  have h1 : HasDerivAt (gapF a b S ε) (-1 - ε * deriv S z) z :=
    ((hasDerivAt_id' z).const_sub ((a + b) / 2)).sub (hSd.const_mul ε)
  have hk : -1 - ε * deriv S z = ε * gapF a b S ε z / S z := by
    rw [eq_div_iff hS0]
    unfold gapF
    linear_combination (-ε) * hd + (S z) * hεε
  rw [← hk]
  exact h1

private lemma arc_ftc {a b : ℂ} {S : ℂ → ℂ} (hS : IsSquareRootSheet a b S) {ε : ℂ}
    (hεε : ε * ε = 1) {c : ℝ → ℂ} {p q : ℝ} (hpq : p ≤ q)
    (hc : ContDiffOn ℝ 1 c (Icc p q)) (hΩ : ∀ u ∈ Icc p q, c u ∈ cutDomain a b) :
    IntervalIntegrable (fun u => deriv c u / S (c u)) MeasureTheory.volume p q ∧
      gapF a b S ε (c q) = gapF a b S ε (c p) *
        Complex.exp (ε * ∫ u in p..q, deriv c u / S (c u)) := by
  rcases hpq.eq_or_lt with rfl | hlt
  · refine ⟨IntervalIntegrable.refl, ?_⟩
    simp
  · set D : ℝ → ℂ := derivWithin c (Icc p q) with hD
    have hUD : UniqueDiffOn ℝ (Icc p q) := uniqueDiffOn_Icc hlt
    have hDcont : ContinuousOn D (Icc p q) := hc.continuousOn_derivWithin hUD le_rfl
    have hcc : ContinuousOn c (Icc p q) := hc.continuousOn
    have hmaps : MapsTo c (Icc p q) (cutDomain a b) := hΩ
    have hScont : ContinuousOn (fun u => S (c u)) (Icc p q) :=
      hS.analytic.continuousOn.comp hcc hmaps
    have hS0 : ∀ u ∈ Icc p q, S (c u) ≠ 0 := fun u hu => sheet_ne_zero hS (hΩ u hu)
    have hg : ContinuousOn (fun u => D u / S (c u)) (Icc p q) := hDcont.div hScont hS0
    have hgint : IntervalIntegrable (fun u => D u / S (c u)) MeasureTheory.volume p q :=
      hg.intervalIntegrable_of_Icc hlt.le
    have hEq : ∀ u ∈ Ioo p q, deriv c u = D u := fun u hu =>
      (derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)).symm
    have hfint : IntervalIntegrable (fun u => deriv c u / S (c u)) MeasureTheory.volume p q := by
      refine hgint.congr_uIoo ?_
      intro u hu
      rw [Set.uIoo_of_le hlt.le] at hu
      simp only
      rw [hEq u hu]
    have hint_eq : ∫ u in p..q, deriv c u / S (c u) = ∫ u in p..q, D u / S (c u) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(Set.countable_singleton q).ae_notMem MeasureTheory.volume] with u hu huI
      rw [Set.uIoc_of_le hlt.le] at huI
      have hne : u ≠ q := hu
      rw [hEq u ⟨huI.1, lt_of_le_of_ne huI.2 hne⟩]
    refine ⟨hfint, ?_⟩
    rw [hint_eq]
    set J : ℝ → ℂ := fun u => ∫ y in p..u, D y / S (c y) with hJ
    set Ψ : ℝ → ℂ := fun u => gapF a b S ε (c u) * Complex.exp (-ε * J u) with hΨ
    have hFcont : ContinuousOn (fun u => gapF a b S ε (c u)) (Icc p q) := by
      show ContinuousOn (fun u => ((a + b) / 2 - c u) - ε * S (c u)) (Icc p q)
      exact (continuousOn_const.sub hcc).sub (continuousOn_const.mul hScont)
    have hprim : ContinuousOn J (Icc p q) := by
      have := intervalIntegral.continuousOn_primitive_interval' hgint
        (left_mem_uIcc : p ∈ Set.uIcc p q)
      rwa [Set.uIcc_of_le hlt.le] at this
    have hcont : ContinuousOn Ψ (Icc p q) :=
      hFcont.mul ((continuousOn_const.mul hprim).cexp)
    have hderiv : ∀ x ∈ Ico p q, HasDerivWithinAt Ψ 0 (Ici x) x := by
      intro x hx
      have hxI : x ∈ Icc p q := ⟨hx.1, hx.2.le⟩
      have hxΩ := hΩ x hxI
      have hnh : Icc p q ∈ 𝓝[Ici x] x :=
        mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc hx.1 le_rfl)
      have hcd : HasDerivWithinAt c (D x) (Ici x) x :=
        (((hc.differentiableOn one_ne_zero) x hxI).hasDerivWithinAt).mono_of_mem_nhdsWithin hnh
      have hFd := gapF_hasDerivAt hS hεε hxΩ
      have hFc : HasDerivWithinAt (fun u => gapF a b S ε (c u))
          (D x • (ε * gapF a b S ε (c x) / S (c x))) (Ici x) x :=
        hFd.scomp_hasDerivWithinAt x hcd
      have hmem : Icc p q ∈ 𝓝[Ioi x] x :=
        mem_of_superset (Ioc_mem_nhdsGT hx.2) (fun y hy => ⟨hx.1.trans hy.1.le, hy.2⟩)
      have hmeas : StronglyMeasurableAtFilter (fun u => D u / S (c u)) (𝓝[Ioi x] x) :=
        (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
          (nhdsWithin_le_of_mem hmem)
      have hcw : ContinuousWithinAt (fun u => D u / S (c u)) (Ioi x) x :=
        (hg x hxI).mono_of_mem_nhdsWithin hmem
      have hgx : IntervalIntegrable (fun u => D u / S (c u)) MeasureTheory.volume p x :=
        ((hg.mono (Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1)
      have hI : HasDerivWithinAt J (D x / S (c x)) (Ici x) x :=
        intervalIntegral.integral_hasDerivWithinAt_right (s := Ici x) (t := Ioi x)
          hgx hmeas hcw
      have hE : HasDerivWithinAt (fun u => Complex.exp (-ε * J u))
          (Complex.exp (-ε * J x) * (-ε * (D x / S (c x)))) (Ici x) x :=
        (hI.const_mul (-ε)).cexp
      have hP := hFc.mul hE
      convert hP using 1
      simp only [smul_eq_mul]
      ring
    have hconst := constant_of_has_deriv_right_zero hcont hderiv q ⟨hlt.le, le_rfl⟩
    have hJp : J p = 0 := by simp [hJ]
    have hΨp : Ψ p = gapF a b S ε (c p) := by simp [hΨ, hJp]
    have h1 : gapF a b S ε (c q) * Complex.exp (-ε * J q) = gapF a b S ε (c p) := by
      rw [← hΨp]
      exact hconst
    have h2 : Complex.exp (-ε * J q) * Complex.exp (ε * J q) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc gapF a b S ε (c q)
        = gapF a b S ε (c q) * (Complex.exp (-ε * J q) * Complex.exp (ε * J q)) := by
          rw [h2, mul_one]
      _ = (gapF a b S ε (c q) * Complex.exp (-ε * J q)) * Complex.exp (ε * J q) := by ring
      _ = gapF a b S ε (c p) * Complex.exp (ε * J q) := by rw [h1]

private lemma pw_ftc {a b : ℂ} {S : ℂ → ℂ} (hS : IsSquareRootSheet a b S) {ε : ℂ}
    (hεε : ε * ε = 1) {c : ℝ → ℂ} {p q : ℝ} (h : PiecewiseC1On c p q)
    (hΩ : ∀ u ∈ Icc p q, c u ∈ cutDomain a b) :
    IntervalIntegrable (fun u => deriv c u / S (c u)) MeasureTheory.volume p q ∧
      gapF a b S ε (c q) = gapF a b S ε (c p) *
        Complex.exp (ε * ∫ u in p..q, deriv c u / S (c u)) := by
  induction h with
  | arc hpq hc => exact arc_ftc hS hεε hpq hc hΩ
  | @trans p m q h₁ h₂ _ _ ih1 ih2 =>
    obtain ⟨hi1, he1⟩ := ih1 (fun u hu => hΩ u ⟨hu.1, hu.2.trans h₂⟩)
    obtain ⟨hi2, he2⟩ := ih2 (fun u hu => hΩ u ⟨h₁.trans hu.1, hu.2⟩)
    refine ⟨hi1.trans hi2, ?_⟩
    rw [he2, he1, mul_assoc, ← Complex.exp_add, ← mul_add,
      intervalIntegral.integral_add_adjacent_intervals hi1 hi2]

private lemma pw_restrict {c : ℝ → ℂ} {p q : ℝ} (h : PiecewiseC1On c p q) :
    ∀ δ, p ≤ δ → δ ≤ q → PiecewiseC1On c δ q := by
  induction h with
  | arc hpq hc =>
    intro δ hpδ hδq
    exact PiecewiseC1On.arc hδq (hc.mono (Icc_subset_Icc hpδ le_rfl))
  | @trans p m q h₁ h₂ _ _ ih1 ih2 =>
    intro δ hpδ hδq
    by_cases hδm : δ ≤ m
    · exact PiecewiseC1On.trans hδm h₂ (ih1 δ hpδ hδm) (by assumption)
    · exact ih2 δ (le_of_lt (not_le.1 hδm)) hδq

private lemma pw_continuousOn {c : ℝ → ℂ} {p q : ℝ} (h : PiecewiseC1On c p q) :
    ContinuousOn c (Icc p q) := by
  induction h with
  | arc hpq hc => exact hc.continuousOn
  | @trans p m q h₁ h₂ _ _ ih1 ih2 =>
    rw [← Set.Icc_union_Icc_eq_Icc h₁ h₂]
    exact ih1.union_of_isClosed ih2 isClosed_Icc isClosed_Icc

/-- KSN-003 (whole proposition): the elementary Abelian integral exponential. -/
theorem elementary_gap_exponential (a b : ℂ) (hab : a ≠ b) (S : ℂ → ℂ)
    (hS : IsSquareRootSheet a b S) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (mu : ℂ) (c : ℝ → ℂ)
    (hc : IsGapPath a b mu c) (I : ℂ) (hI : HasGapIntegral S c I) :
    ((b - a) / 2) * Complex.exp (ε * I) = ((a + b) / 2 - mu) - ε * S mu := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨hc0, hc1, hpw, hΩ⟩ := hc
  have hident : ∀ δ ∈ Ioc (0 : ℝ) 1, gapF a b S ε mu =
      gapF a b S ε (c δ) * Complex.exp (ε * ∫ t in δ..1, deriv c t / S (c t)) := by
    intro δ hδ
    have hpw' := pw_restrict hpw δ hδ.1.le hδ.2
    have := (pw_ftc hS hεε hpw'
      (fun u hu => hΩ u ⟨lt_of_lt_of_le hδ.1 hu.1, hu.2⟩)).2
    rw [hc1] at this
    exact this
  have hcont : ContinuousOn c (Icc 0 1) := pw_continuousOn hpw
  have hlim_c : Tendsto c (𝓝[>] 0) (𝓝 a) := by
    have h0 : ContinuousWithinAt c (Ioi 0) 0 :=
      (hcont 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioc_mem_nhdsGT zero_lt_one) Ioc_subset_Icc_self)
    rw [← hc0]
    exact h0
  have hlim_S : Tendsto (fun δ => S (c δ)) (𝓝[>] 0) (𝓝 0) := by
    have hpoly : Tendsto (fun δ => (b - c δ) * (a - c δ)) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_const_nhds (x := b)).sub hlim_c).mul
        ((tendsto_const_nhds (x := a)).sub hlim_c)
      simpa using this
    have hnorm2 : Tendsto (fun δ => ‖S (c δ)‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun δ => ‖(b - c δ) * (a - c δ)‖) (𝓝[>] 0) (𝓝 0) := by
        simpa using hpoly.norm
      refine h1.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with δ hδ
      rw [← hS.sq (c δ) (hΩ δ hδ), norm_pow]
    have hnorm : Tendsto (fun δ => ‖S (c δ)‖) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hnorm2
      simp only [Real.sqrt_zero] at this
      refine this.congr (fun δ => ?_)
      simp [Real.sqrt_sq (norm_nonneg _)]
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm
  have h1 : Tendsto (fun δ => gapF a b S ε (c δ)) (𝓝[>] 0) (𝓝 ((b - a) / 2)) := by
    have := (((tendsto_const_nhds (x := (a + b) / 2)).sub hlim_c)).sub
      ((tendsto_const_nhds (x := ε)).mul hlim_S)
    have e : (a + b) / 2 - a = (b - a) / 2 := by ring
    rw [mul_zero, sub_zero] at this
    rw [e] at this
    exact this
  have h2 : Tendsto (fun δ => Complex.exp (ε * ∫ t in δ..1, deriv c t / S (c t)))
      (𝓝[>] 0) (𝓝 (Complex.exp (ε * I))) :=
    (Complex.continuous_exp.tendsto _).comp (hI.const_mul ε)
  have h4 : Tendsto (fun _ : ℝ => gapF a b S ε mu) (𝓝[>] 0)
      (𝓝 (((b - a) / 2) * Complex.exp (ε * I))) := by
    refine (h1.mul h2).congr' ?_
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with δ hδ
    exact (hident δ hδ).symm
  have h5 := tendsto_nhds_unique h4 tendsto_const_nhds
  rw [h5]
  rfl


open MeasureTheory

/-! ### Reachability: a polygonal path from `a` to every point of the cut domain -/

/-- A point is away from the real unit interval `[0,1]` (normalised cut). -/
private def GoodPt (x : ℂ) : Prop := 1 < x.re ∨ x.re < 0 ∨ x.im ≠ 0

private lemma mem_cutDomain_of_good {a b : ℂ} (hab : a ≠ b) {x : ℂ} (hx : GoodPt x) :
    a + (b - a) * x ∈ cutDomain a b := by
  intro hseg
  obtain ⟨s, t, hs, ht, hst, h⟩ := hseg
  simp only [Complex.real_smul] at h
  have hs' : (s : ℂ) = 1 - t := by
    have : s = 1 - t := by linarith
    rw [this]; push_cast; ring
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have h1 : (b - a) * (x - t) = 0 := by linear_combination (-1 : ℂ) * h + a * hs'
  have h2 : x = (t : ℂ) := by
    rcases mul_eq_zero.1 h1 with h3 | h3
    · exact absurd h3 hd
    · exact sub_eq_zero.1 h3
  have ht1 : t ≤ 1 := by linarith
  rcases hx with h4 | h4 | h4
  · rw [h2] at h4; simp at h4; linarith
  · rw [h2] at h4; simp at h4; linarith
  · apply h4; rw [h2]; simp

/-- Four-leg polygonal parametrisation on `[0,1/4],[1/4,1/2],[1/2,3/4],[3/4,1]`. -/
private def poly4 (P0 P1 P2 P3 P4 : ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 / 4 then P0 + ((4 * t : ℝ) : ℂ) * (P1 - P0)
  else if t ≤ 1 / 2 then P1 + ((4 * t - 1 : ℝ) : ℂ) * (P2 - P1)
  else if t ≤ 3 / 4 then P2 + ((4 * t - 2 : ℝ) : ℂ) * (P3 - P2)
  else P3 + ((4 * t - 3 : ℝ) : ℂ) * (P4 - P3)

private lemma poly4_eq1 (P0 P1 P2 P3 P4 : ℂ) {t : ℝ} (h : t ≤ 1 / 4) :
    poly4 P0 P1 P2 P3 P4 t = P0 + ((4 * t : ℝ) : ℂ) * (P1 - P0) := by
  unfold poly4
  rw [if_pos h]

private lemma poly4_eq2 (P0 P1 P2 P3 P4 : ℂ) {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1 / 2) :
    poly4 P0 P1 P2 P3 P4 t = P1 + ((4 * t - 1 : ℝ) : ℂ) * (P2 - P1) := by
  by_cases h : t ≤ 1 / 4
  · have : t = 1 / 4 := le_antisymm h h1
    subst this
    simp only [poly4, if_pos h]
    push_cast
    ring
  · unfold poly4
    rw [if_neg h, if_pos h2]

private lemma poly4_eq3 (P0 P1 P2 P3 P4 : ℂ) {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 3 / 4) :
    poly4 P0 P1 P2 P3 P4 t = P2 + ((4 * t - 2 : ℝ) : ℂ) * (P3 - P2) := by
  by_cases h : t ≤ 1 / 2
  · have : t = 1 / 2 := le_antisymm h h1
    subst this
    simp only [poly4, if_neg (by norm_num : ¬ ((1 : ℝ) / 2 ≤ 1 / 4)), if_pos h]
    push_cast
    ring
  · have h' : ¬ t ≤ 1 / 4 := by intro h''; apply h; linarith
    unfold poly4
    rw [if_neg h', if_neg h, if_pos h2]

private lemma poly4_eq4 (P0 P1 P2 P3 P4 : ℂ) {t : ℝ} (h1 : 3 / 4 ≤ t) :
    poly4 P0 P1 P2 P3 P4 t = P3 + ((4 * t - 3 : ℝ) : ℂ) * (P4 - P3) := by
  by_cases h : t ≤ 3 / 4
  · have : t = 3 / 4 := le_antisymm h h1
    subst this
    simp only [poly4, if_neg (by norm_num : ¬ ((3 : ℝ) / 4 ≤ 1 / 4)),
      if_neg (by norm_num : ¬ ((3 : ℝ) / 4 ≤ 1 / 2)), if_pos h]
    push_cast
    ring
  · have h' : ¬ t ≤ 1 / 4 := by intro h''; apply h; linarith
    have h'' : ¬ t ≤ 1 / 2 := by intro h3; apply h; linarith
    unfold poly4
    rw [if_neg h', if_neg h'', if_neg h]

private lemma contDiff_leg (a d A B : ℂ) (k : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => a + d * (A + ((4 * t - k : ℝ) : ℂ) * (B - A))) := by
  have h0 : ContDiff ℝ 1 (fun t : ℝ => 4 * t - k) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have h1 : ContDiff ℝ 1 (fun t : ℝ => ((4 * t - k : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h0
  exact contDiff_const.add (contDiff_const.mul (contDiff_const.add (h1.mul contDiff_const)))

private lemma leg_pos (α β γ : ℝ) {A B : ℂ} {s : ℝ}
    (hA : 0 < α * A.re + β * A.im + γ) (hB : 0 < α * B.re + β * B.im + γ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < α * (A + (s : ℂ) * (B - A)).re + β * (A + (s : ℂ) * (B - A)).im + γ := by
  have key : α * (A + (s : ℂ) * (B - A)).re + β * (A + (s : ℂ) * (B - A)).im + γ =
      (1 - s) * (α * A.re + β * A.im + γ) + s * (α * B.re + β * B.im + γ) := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.add_im, Complex.mul_im, Complex.sub_im, zero_mul, sub_zero,
      add_zero]
    ring
  rw [key]
  by_cases h1 : s = 1
  · subst h1; simpa using hB
  · have hlt : s < 1 := lt_of_le_of_ne hs1 h1
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hA) (mul_nonneg hs0 hB.le)

private lemma poly4_cases (P0 P1 P2 P3 P4 : ℂ) {t : ℝ} (ht1 : t ≤ 1) :
    (t ≤ 1 / 4 ∧ poly4 P0 P1 P2 P3 P4 t = P0 + ((4 * t : ℝ) : ℂ) * (P1 - P0)) ∨
    (1 / 4 ≤ t ∧ t ≤ 1 / 2 ∧
      poly4 P0 P1 P2 P3 P4 t = P1 + ((4 * t - 1 : ℝ) : ℂ) * (P2 - P1)) ∨
    (1 / 2 ≤ t ∧ t ≤ 3 / 4 ∧
      poly4 P0 P1 P2 P3 P4 t = P2 + ((4 * t - 2 : ℝ) : ℂ) * (P3 - P2)) ∨
    (3 / 4 ≤ t ∧ poly4 P0 P1 P2 P3 P4 t = P3 + ((4 * t - 3 : ℝ) : ℂ) * (P4 - P3)) := by
  by_cases h1 : t ≤ 1 / 4
  · exact Or.inl ⟨h1, poly4_eq1 _ _ _ _ _ h1⟩
  · by_cases h2 : t ≤ 1 / 2
    · exact Or.inr (Or.inl ⟨le_of_not_ge h1, h2, poly4_eq2 _ _ _ _ _ (le_of_not_ge h1) h2⟩)
    · by_cases h3 : t ≤ 3 / 4
      · exact Or.inr (Or.inr (Or.inl ⟨le_of_not_ge h2, h3,
          poly4_eq3 _ _ _ _ _ (le_of_not_ge h2) h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨le_of_not_ge h3, poly4_eq4 _ _ _ _ _ (le_of_not_ge h3)⟩))

/-- The path obtained from the four-leg polygon by the affine map `x ↦ a + (b-a) x`. -/
private def polyPath (a b P2 P3 w : ℂ) (t : ℝ) : ℂ :=
  a + (b - a) * poly4 0 Complex.I P2 P3 w t

private lemma polyPath_pw (a b P2 P3 w : ℂ) : PiecewiseC1On (polyPath a b P2 P3 w) 0 1 := by
  have hA : ∀ (A B : ℂ) (k : ℝ) (p q : ℝ) (hpq : p ≤ q),
      (∀ t ∈ Icc p q, polyPath a b P2 P3 w t =
        a + (b - a) * (A + ((4 * t - k : ℝ) : ℂ) * (B - A))) →
      ContDiffOn ℝ 1 (polyPath a b P2 P3 w) (Icc p q) := by
    intro A B k p q hpq h
    exact (contDiff_leg a (b - a) A B k).contDiffOn.congr h
  refine PiecewiseC1On.trans (m := 1 / 4) (by norm_num) (by norm_num)
    (PiecewiseC1On.arc (by norm_num) (hA 0 Complex.I 0 0 (1 / 4) (by norm_num) ?_))
    (PiecewiseC1On.trans (m := 1 / 2) (by norm_num) (by norm_num)
      (PiecewiseC1On.arc (by norm_num) (hA Complex.I P2 1 (1 / 4) (1 / 2) (by norm_num) ?_))
      (PiecewiseC1On.trans (m := 3 / 4) (by norm_num) (by norm_num)
        (PiecewiseC1On.arc (by norm_num) (hA P2 P3 2 (1 / 2) (3 / 4) (by norm_num) ?_))
        (PiecewiseC1On.arc (by norm_num) (hA P3 w 3 (3 / 4) 1 (by norm_num) ?_))))
  · intro t ht
    simp [polyPath, poly4_eq1 _ _ _ _ _ ht.2]
  · intro t ht
    simp only [polyPath, poly4_eq2 _ _ _ _ _ ht.1 ht.2]
  · intro t ht
    simp only [polyPath, poly4_eq3 _ _ _ _ _ ht.1 ht.2]
  · intro t ht
    simp only [polyPath, poly4_eq4 _ _ _ _ _ ht.1]

private lemma deriv_leg1 (a d : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => a + d * (((4 * u : ℝ) : ℂ) * Complex.I)) (d * (4 * Complex.I)) t := by
  have h4 : HasDerivAt (fun u : ℝ => ((4 * u : ℝ) : ℂ)) 4 t := by
    have := ((hasDerivAt_id' t).const_mul (4 : ℝ)).ofReal_comp
    simpa using this
  exact ((h4.mul_const Complex.I).const_mul d).const_add a

private lemma reach_of_poly {a b : ℂ} (hab : a ≠ b) {S : ℂ → ℂ} (hS : IsSquareRootSheet a b S)
    (P2 P3 w : ℂ) (hgood : ∀ t ∈ Ioc (0 : ℝ) 1, GoodPt (poly4 0 Complex.I P2 P3 w t)) :
    ∃ c : ℝ → ℂ, IsGapPath a b (a + (b - a) * w) c ∧ ∃ I : ℂ, HasGapIntegral S c I := by
  have hd0 : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hΩ : ∀ t ∈ Ioc (0 : ℝ) 1, polyPath a b P2 P3 w t ∈ cutDomain a b :=
    fun t ht => mem_cutDomain_of_good hab (hgood t ht)
  have hpw := polyPath_pw a b P2 P3 w
  have hc0 : polyPath a b P2 P3 w 0 = a := by
    simp [polyPath, poly4_eq1 _ _ _ _ _ (show (0 : ℝ) ≤ 1 / 4 by norm_num)]
  have hc1 : polyPath a b P2 P3 w 1 = a + (b - a) * w := by
    have : poly4 0 Complex.I P2 P3 w 1 = w := by
      rw [poly4_eq4 _ _ _ _ _ (by norm_num : (3 : ℝ) / 4 ≤ 1)]
      push_cast
      ring
    simp only [polyPath, this]
  refine ⟨polyPath a b P2 P3 w, ⟨hc0, hc1, hpw, hΩ⟩, ?_⟩
  set c := polyPath a b P2 P3 w with hc
  have hleg1 : ∀ t : ℝ, t ≤ 1 / 4 → c t = a + (b - a) * (((4 * t : ℝ) : ℂ) * Complex.I) := by
    intro t ht
    simp [hc, polyPath, poly4_eq1 _ _ _ _ _ ht]
  set f : ℝ → ℂ := fun t => deriv c t / S (c t) with hf
  have hrest : IntervalIntegrable f MeasureTheory.volume (1 / 4) 1 := by
    have hpw' := pw_restrict hpw (1 / 4) (by norm_num) (by norm_num)
    exact (pw_ftc hS (ε := 1) (by norm_num) hpw'
      (fun u hu => hΩ u ⟨by linarith [hu.1], hu.2⟩)).1
  have hder : ∀ t ∈ Ioo (0 : ℝ) (1 / 4), deriv c t = (b - a) * (4 * Complex.I) := by
    intro t ht
    have hev : c =ᶠ[𝓝 t] (fun u : ℝ => a + (b - a) * (((4 * u : ℝ) : ℂ) * Complex.I)) := by
      filter_upwards [Iio_mem_nhds ht.2] with u hu
      exact hleg1 u hu.le
    rw [hev.deriv_eq]
    exact (deriv_leg1 a (b - a) t).deriv
  have hbound : ∀ t ∈ Ioo (0 : ℝ) (1 / 4), ‖f t‖ ≤ 2 * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have ht1 : t ≤ 1 := by linarith [ht.2]
    have htΩ := hΩ t ⟨ht.1, ht1⟩
    have hct := hleg1 t ht.2.le
    have hS0 := sheet_ne_zero hS htΩ
    have hSpos : 0 < ‖S (c t)‖ := norm_pos_iff.2 hS0
    have hd' : 0 < ‖b - a‖ := norm_pos_iff.2 hd0
    have hn1 : ‖a - c t‖ = ‖b - a‖ * (4 * t) := by
      rw [hct]
      have : a - (a + (b - a) * (((4 * t : ℝ) : ℂ) * Complex.I)) =
          -((b - a) * (((4 * t : ℝ) : ℂ) * Complex.I)) := by ring
      rw [this, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
    have hn2 : ‖b - a‖ ≤ ‖b - c t‖ := by
      rw [hct]
      have : b - (a + (b - a) * (((4 * t : ℝ) : ℂ) * Complex.I)) =
          (b - a) * (1 - ((4 * t : ℝ) : ℂ) * Complex.I) := by ring
      rw [this, norm_mul]
      have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) - ((4 * t : ℝ) : ℂ) * Complex.I‖ := by
        have := Complex.abs_re_le_norm ((1 : ℂ) - ((4 * t : ℝ) : ℂ) * Complex.I)
        simpa using this
      nlinarith [hd']
    have hSsq : ‖S (c t)‖ ^ 2 = ‖b - c t‖ * ‖a - c t‖ := by
      rw [← norm_pow, hS.sq _ htΩ, norm_mul]
    have hlow : ‖b - a‖ * (‖b - a‖ * (4 * t)) ≤ ‖S (c t)‖ ^ 2 := by
      rw [hSsq, hn1]
      exact mul_le_mul_of_nonneg_right hn2 (mul_nonneg hd'.le (by linarith [ht.1]))
    have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    have hSge : 2 * ‖b - a‖ * Real.sqrt t ≤ ‖S (c t)‖ := by
      rw [← sq_le_sq₀ (by positivity) hSpos.le, mul_pow, mul_pow, Real.sq_sqrt ht.1.le]
      nlinarith [hlow]
    have hfn : ‖f t‖ = 4 * ‖b - a‖ / ‖S (c t)‖ := by
      simp only [hf]
      rw [hder t ht, norm_div, norm_mul, norm_mul, Complex.norm_I]
      norm_num
      ring
    rw [hfn, Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow, div_le_iff₀ hSpos]
    rw [mul_comm 2 ((Real.sqrt t)⁻¹), mul_assoc]
    have h5 : (Real.sqrt t)⁻¹ * (2 * ‖S (c t)‖) ≥ (Real.sqrt t)⁻¹ * (2 * (2 * ‖b - a‖ * Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h6 : (Real.sqrt t)⁻¹ * (2 * (2 * ‖b - a‖ * Real.sqrt t)) = 4 * ‖b - a‖ := by
      field_simp
      ring
    linarith
  have hsing : IntervalIntegrable f MeasureTheory.volume 0 (1 / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num),
      integrableOn_Ioc_iff_integrableOn_Ioo]
    have hg : IntegrableOn (fun t : ℝ => 2 * t ^ (-(1 / 2 : ℝ))) (Ioo (0 : ℝ) (1 / 4)) := by
      have h1 : IntervalIntegrable (fun t : ℝ => 2 * t ^ (-(1 / 2 : ℝ))) MeasureTheory.volume 0
          (1 / 4) :=
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h1
      exact (integrableOn_Ioc_iff_integrableOn_Ioo).1 h1
    have hcontc : ContinuousOn c (Ioo (0 : ℝ) (1 / 4)) :=
      (pw_continuousOn hpw).mono (fun t ht => ⟨ht.1.le, by linarith [ht.2]⟩)
    have hmaps : MapsTo c (Ioo (0 : ℝ) (1 / 4)) (cutDomain a b) :=
      fun t ht => hΩ t ⟨ht.1, by linarith [ht.2]⟩
    have hScont : ContinuousOn (fun t => S (c t)) (Ioo (0 : ℝ) (1 / 4)) :=
      hS.analytic.continuousOn.comp hcontc hmaps
    have hgc : ContinuousOn (fun t => ((b - a) * (4 * Complex.I)) / S (c t))
        (Ioo (0 : ℝ) (1 / 4)) :=
      continuousOn_const.div hScont (fun t ht => sheet_ne_zero hS (hmaps ht))
    have hmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioo (0 : ℝ) (1 / 4))) := by
      refine (hgc.aestronglyMeasurable measurableSet_Ioo).congr ?_
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      simp only [hf]
      rw [hder t ht]
    exact Integrable.mono' hg hmeas
      ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hbound))
  have hall : IntervalIntegrable f MeasureTheory.volume 0 1 := hsing.trans hrest
  refine ⟨∫ t in (0 : ℝ)..1, f t, ?_⟩
  have hprim : ContinuousOn (fun u => ∫ x in (0 : ℝ)..u, f x) (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval' hall
      (left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 1)
    rwa [Set.uIcc_of_le zero_le_one] at this
  have h0 : Tendsto (fun δ : ℝ => ∫ x in (0 : ℝ)..δ, f x) (𝓝[>] 0) (𝓝 0) := by
    have h := (hprim 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioc_mem_nhdsGT zero_lt_one) Ioc_subset_Icc_self)
    unfold ContinuousWithinAt at h
    simpa using h
  have h1 : Tendsto (fun δ : ℝ => (∫ t in (0 : ℝ)..1, f t) - ∫ x in (0 : ℝ)..δ, f x)
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
    simpa using (tendsto_const_nhds (x := ∫ t in (0 : ℝ)..1, f t)).sub h0
  refine h1.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with δ hδ
  have hint0 : IntervalIntegrable f MeasureTheory.volume 0 δ :=
    hall.mono_set (by
      rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hδ.1.le]
      exact Icc_subset_Icc le_rfl hδ.2)
  exact intervalIntegral.integral_interval_sub_left hall hint0

private lemma good_of_region {x : ℂ} (h : 0 < 0 * x.re + 1 * x.im + 0 ∨ 0 < 1 * x.re + 0 * x.im + (-1) ∨
    0 < (-1) * x.re + 0 * x.im + 0) : GoodPt x := by
  rcases h with h | h | h
  · right; right; intro h0; simp [h0] at h
  · left; linarith
  · right; left; linarith

private lemma gap_reachable_aux {a b : ℂ} (hab : a ≠ b) {S : ℂ → ℂ} (hS : IsSquareRootSheet a b S)
    (w : ℂ) (hw : GoodPt w) :
    ∃ c : ℝ → ℂ, IsGapPath a b (a + (b - a) * w) c ∧ ∃ I : ℂ, HasGapIntegral S c I := by
  -- first leg: points 4 t I are in the upper half plane
  have leg1 : ∀ (P0 : ℂ), P0 = 0 → ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      0 < (P0 + ((4 * t : ℝ) : ℂ) * (Complex.I - P0)).im := by
    intro P0 hP t ht _
    subst hP
    simp
    linarith
  by_cases hU : 0 < w.im
  · -- upper half plane: waypoints (0, I, w, w, w)
    refine reach_of_poly hab hS w w w ?_
    intro t ht
    rcases poly4_cases 0 Complex.I w w w ht.2 with ⟨h1, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩
    · rw [he]; apply good_of_region; left; have := leg1 0 rfl t ht.1 h1; simpa using this
    · rw [he]; apply good_of_region; left
      have := leg_pos 0 1 0 (A := Complex.I) (B := w) (s := 4 * t - 1) (by simp) (by simpa using hU)
        (by linarith) (by linarith)
      simpa using this
    · rw [he]; apply good_of_region; left
      have := leg_pos 0 1 0 (A := w) (B := w) (s := 4 * t - 2) (by simpa using hU) (by simpa using hU)
        (by linarith) (by linarith)
      simpa using this
    · rw [he]; apply good_of_region; left
      have := leg_pos 0 1 0 (A := w) (B := w) (s := 4 * t - 3) (by simpa using hU) (by simpa using hU)
        (by linarith) (by linarith [ht.2])
      simpa using this
  · by_cases hRD : 1 < w.re ∨ w.im < 0
    · -- waypoints (0, I, 2 + I, 2, w)
      refine reach_of_poly hab hS (2 + Complex.I) 2 w ?_
      intro t ht
      rcases poly4_cases 0 Complex.I (2 + Complex.I) 2 w ht.2 with
        ⟨h1, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩
      · rw [he]; apply good_of_region; left; have := leg1 0 rfl t ht.1 h1; simpa using this
      · rw [he]; apply good_of_region; left
        have := leg_pos 0 1 0 (A := Complex.I) (B := 2 + Complex.I) (s := 4 * t - 1)
          (by simp) (by simp) (by linarith) (by linarith)
        simpa using this
      · rw [he]; apply good_of_region; right; left
        have := leg_pos 1 0 (-1) (A := 2 + Complex.I) (B := 2) (s := 4 * t - 2)
          (by simp <;> norm_num) (by simp <;> norm_num) (by linarith) (by linarith)
        simpa using this
      · rw [he]
        rcases hRD with hR | hD
        · apply good_of_region; right; left
          have := leg_pos 1 0 (-1) (A := 2) (B := w) (s := 4 * t - 3)
            (by simp <;> norm_num) (by simpa using hR) (by linarith) (by linarith [ht.2])
          simpa using this
        · by_cases hs : 4 * t - 3 = 0
          · rw [hs]; simp only [Complex.ofReal_zero, zero_mul, add_zero]
            apply good_of_region; right; left; simp <;> norm_num
          · right; right
            have : (2 + ((4 * t - 3 : ℝ) : ℂ) * (w - 2)).im = (4 * t - 3) * w.im := by simp
            rw [this]
            exact mul_ne_zero hs hD.ne
    · -- left half plane: waypoints (0, I, -1 + I, -1, w)
      have hL : w.re < 0 := by
        push_neg at hRD hU
        rcases hw with h | h | h
        · exact absurd h (not_lt.2 hRD.1)
        · exact h
        · exfalso
          rcases lt_or_gt_of_ne h with h' | h'
          · exact absurd h' (not_lt.2 hRD.2)
          · exact absurd h' (not_lt.2 hU)
      refine reach_of_poly hab hS (-1 + Complex.I) (-1) w ?_
      intro t ht
      rcases poly4_cases 0 Complex.I (-1 + Complex.I) (-1) w ht.2 with
        ⟨h1, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, h2, he⟩ | ⟨h1, he⟩
      · rw [he]; apply good_of_region; left; have := leg1 0 rfl t ht.1 h1; simpa using this
      · rw [he]; apply good_of_region; left
        have := leg_pos 0 1 0 (A := Complex.I) (B := -1 + Complex.I) (s := 4 * t - 1)
          (by simp) (by simp) (by linarith) (by linarith)
        simpa using this
      · rw [he]; apply good_of_region; right; right
        have := leg_pos (-1) 0 0 (A := -1 + Complex.I) (B := -1) (s := 4 * t - 2)
          (by simp) (by simp) (by linarith) (by linarith)
        simpa using this
      · rw [he]; apply good_of_region; right; right
        have := leg_pos (-1) 0 0 (A := -1) (B := w) (s := 4 * t - 3)
          (by simp) (by simpa using hL) (by linarith) (by linarith [ht.2])
        simpa using this

/-- KSN-003 reachability: every point of the cut domain is reached by an admissible piecewise
`C^1` path with a convergent improper integral. -/
theorem gap_reachable (a b : ℂ) (hab : a ≠ b) (S : ℂ → ℂ) (hS : IsSquareRootSheet a b S) :
    ∀ mu ∈ cutDomain a b, ∃ c : ℝ → ℂ, IsGapPath a b mu c ∧ ∃ I : ℂ, HasGapIntegral S c I := by
  intro mu hmu
  have hd0 : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  set w : ℂ := (mu - a) / (b - a) with hw
  have hmuw : mu = a + (b - a) * w := by
    rw [hw]; field_simp; ring
  have hgood : GoodPt w := by
    by_contra hbad
    unfold GoodPt at hbad
    push_neg at hbad
    obtain ⟨h1, h2, h3⟩ := hbad
    apply hmu
    refine ⟨1 - w.re, w.re, by linarith, h2, by ring, ?_⟩
    rw [hmuw]
    have hw' : w = (w.re : ℂ) := by
      apply Complex.ext <;> simp [h3]
    simp only [Complex.real_smul]
    conv_rhs => rw [hw']
    push_cast
    ring
  rw [hmuw]
  exact gap_reachable_aux hab hS w hgood

end NlsGge.Atomic.KSN003Design
