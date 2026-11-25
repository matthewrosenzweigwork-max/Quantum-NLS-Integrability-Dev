import Mathlib
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.XiSqPeriod
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M008EndpointBound

section Part0

/- M-008 SUPPORT E3a (proof development, AUTHOR; not reviewed).  Hypothesis-free elementary lemmas for the Joukowski-type parametrization
   `jouk tau d v = tau - d cosh v` of a neighbourhood of the segment `[tau - d, tau + d]`: real/imaginary parts of `cosh`, the
   segment test, and the rectangles `Rfull`, `Rpos` in the `v`-plane. -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- Cosine parametrization of the cut disc around the segment `[tau - d, tau + d]`. -/
def jouk (τ d v : ℂ) : ℂ := τ - d * Complex.cosh v

theorem cosh_re_im (x θ : ℝ) :
    Complex.cosh ((x : ℂ) + (θ : ℂ) * Complex.I) =
      ((Real.cosh x * Real.cos θ : ℝ) : ℂ) + ((Real.sinh x * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

theorem cosh_eq_re_im (v : ℂ) :
    Complex.cosh v = ((Real.cosh v.re * Real.cos v.im : ℝ) : ℂ) +
      ((Real.sinh v.re * Real.sin v.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im v]
  exact cosh_re_im v.re v.im

theorem ofReal_add_mul_I_im (A B : ℝ) : ((A : ℂ) + (B : ℂ) * Complex.I).im = B := by simp

theorem ofReal_add_mul_I_re (A B : ℝ) : ((A : ℂ) + (B : ℂ) * Complex.I).re = A := by simp

theorem cosh_im (v : ℂ) : (Complex.cosh v).im = Real.sinh v.re * Real.sin v.im := by
  rw [cosh_eq_re_im, ofReal_add_mul_I_im]

theorem cosh_re (v : ℂ) : (Complex.cosh v).re = Real.cosh v.re * Real.cos v.im := by
  rw [cosh_eq_re_im, ofReal_add_mul_I_re]

/-- For `Re v > 0`, `cosh v` is never a real number of modulus at most one. -/
theorem cosh_not_unit_real {v : ℂ} (hv : 0 < v.re) (r : ℝ) (hr : |r| ≤ 1) : Complex.cosh v ≠ (r : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 := congrArg Complex.re h
  rw [cosh_im, Complex.ofReal_im] at h1
  rw [cosh_re, Complex.ofReal_re] at h2
  have hs : 0 < Real.sinh v.re := Real.sinh_pos_iff.2 hv
  have hsin : Real.sin v.im = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hs.ne'
    · exact h
  have hcos : Real.cos v.im ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq v.im; rw [hsin] at this; linarith
  have hch : 1 < Real.cosh v.re := by
    have := Real.cosh_sq v.re
    nlinarith [Real.cosh_pos v.re, Real.sinh_sq v.re, sq_nonneg (Real.sinh v.re)]
  have : r ^ 2 = Real.cosh v.re ^ 2 := by rw [← h2, mul_pow, hcos, mul_one]
  have hr2 : r ^ 2 ≤ 1 := by
    have := sq_le_one_iff_abs_le_one r |>.2 hr; exact this
  nlinarith [Real.cosh_pos v.re]

theorem jouk_mem_segment_of_real {τ d : ℂ} (c : ℝ) (hc : |c| ≤ 1) :
    τ - d * (c : ℂ) ∈ segment ℝ (τ - d) (τ + d) := by
  rw [segment_eq_image']
  refine ⟨(1 - c) / 2, ⟨by have := (abs_le.1 hc).2; linarith, by have := (abs_le.1 hc).1; linarith⟩, ?_⟩
  simp only [Complex.real_smul]
  push_cast
  ring

theorem jouk_notMem_segment {τ d : ℂ} (hd : d ≠ 0) {v : ℂ} (hv : 0 < v.re) :
    jouk τ d v ∉ segment ℝ (τ - d) (τ + d) := by
  intro h
  rw [segment_eq_image'] at h
  obtain ⟨s, hs01, hs⟩ := h
  simp only [Complex.real_smul] at hs
  unfold jouk at hs
  have h1 : d * (Complex.cosh v - ((1 - 2 * s : ℝ) : ℂ)) = 0 := by
    push_cast
    linear_combination hs
  rcases mul_eq_zero.1 h1 with h | h
  · exact hd h
  · refine cosh_not_unit_real hv (1 - 2 * s) ?_ (sub_eq_zero.1 h)
    exact abs_le.2 ⟨by linarith [hs01.2], by linarith [hs01.1]⟩

end
end NlsGge.ThirdConsultation.MContour

end Part0

section Part1

/- M-008 SUPPORT E3b (proof development, AUTHOR; not reviewed).  Joukowski-type coordinates `z = tau - d cosh v` on the cut isolating disc
   of an open gap (`tau` the midpoint, `d` the half gap): rectangles in the `v`-plane mapping into the cut disc, the constant sign of
   the root factor, the reduction `omega dz = -sigma B(v) dv` with `B` analytic, and a primitive `b` of `B` with `b (i pi) = b 0`
   (from S3, zero period on the loop `Re v = const`). -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

def gapMid (φ : PotPair) (n : ℤ) : ℂ := (lamMinus φ n + lamPlus φ n) / 2
def gapHalf (φ : PotPair) (n : ℤ) : ℂ := (lamPlus φ n - lamMinus φ n) / 2

theorem lamMinus_eq (φ : PotPair) (n : ℤ) : lamMinus φ n = gapMid φ n - gapHalf φ n := by
  unfold gapMid gapHalf; ring

theorem lamPlus_eq (φ : PotPair) (n : ℤ) : lamPlus φ n = gapMid φ n + gapHalf φ n := by
  unfold gapMid gapHalf; ring

theorem gapHalf_ne_zero (φ : PotPair) (n : ℤ) (hne : lamMinus φ n ≠ lamPlus φ n) : gapHalf φ n ≠ 0 := by
  unfold gapHalf
  intro h
  apply hne
  have : lamPlus φ n - lamMinus φ n = 0 := by
    have := mul_eq_zero.1 (show (lamPlus φ n - lamMinus φ n) / 2 = 0 from h)
    simpa using h
  exact (sub_eq_zero.1 this).symm

/-- Rectangles in the `v`-plane. -/
def Rfull (δ0 : ℝ) : Set ℂ :=
  {v : ℂ | -δ0 < v.re} ∩ {v : ℂ | v.re < δ0} ∩ {v : ℂ | -1 < v.im} ∩ {v : ℂ | v.im < 2 * Real.pi + 1}

def Rpos (δ0 : ℝ) : Set ℂ :=
  {v : ℂ | 0 < v.re} ∩ {v : ℂ | v.re < δ0} ∩ {v : ℂ | -1 < v.im} ∩ {v : ℂ | v.im < 2 * Real.pi + 1}

theorem Rfull_convex (δ0 : ℝ) : Convex ℝ (Rfull δ0) :=
  (((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter (convex_halfSpace_im_gt _)).inter
    (convex_halfSpace_im_lt _)

theorem Rpos_convex (δ0 : ℝ) : Convex ℝ (Rpos δ0) :=
  (((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter (convex_halfSpace_im_gt _)).inter
    (convex_halfSpace_im_lt _)

theorem Rfull_isOpen (δ0 : ℝ) : IsOpen (Rfull δ0) :=
  ((((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter
    (isOpen_lt Complex.continuous_im continuous_const))

theorem Rpos_subset_Rfull {δ0 : ℝ} (h : 0 < δ0) : Rpos δ0 ⊆ Rfull δ0 := by
  intro v hv
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
  exact ⟨⟨⟨by simp only [mem_setOf_eq] at h1 ⊢; linarith, h2⟩, h3⟩, h4⟩

/-- A uniform `delta` such that the vertical strip around the imaginary axis maps into the isolating disc. -/
theorem jouk_ball_nbhd (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ v : ℂ, v ∈ Rfull δ0 →
      jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n := by
  set τ := gapMid φ n with hτ
  set d := gapHalf φ n with hd
  set K : Set ℝ := Icc (-1 : ℝ) (2 * Real.pi + 1) with hK
  set N : Set (ℝ × ℝ) := {q : ℝ × ℝ | jouk τ d ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ discU φ n} with hN
  have hcont : Continuous fun q : ℝ × ℝ => jouk τ d ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
    unfold jouk
    exact continuous_const.sub (continuous_const.mul
      (Complex.continuous_cosh.comp (by fun_prop)))
  have hNo : IsOpen N := isOpen_ball.preimage hcont
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ N := by
    rintro ⟨x, θ⟩ ⟨hx, hθ⟩
    simp only [mem_singleton_iff] at hx
    subst hx
    show jouk τ d (((0 : ℝ) : ℂ) + (θ : ℂ) * Complex.I) ∈ discU φ n
    have e : jouk τ d (((0 : ℝ) : ℂ) + (θ : ℂ) * Complex.I) = τ - d * ((Real.cos θ : ℝ) : ℂ) := by
      unfold jouk; rw [cosh_re_im]; simp
    rw [e]
    refine own_segment_subset_disc φ hφ n ?_
    rw [lamMinus_eq, lamPlus_eq]
    exact jouk_mem_segment_of_real (Real.cos θ) (Real.abs_cos_le_one θ)
  obtain ⟨u, w, hu, hw, hs0, hKw, huw⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hNo hsub
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.1 hu 0 (hs0 rfl)
  refine ⟨δ0, hδ0, fun v hv => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
  have hx : v.re ∈ ball (0 : ℝ) δ0 := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_lt]; exact ⟨h1, h2⟩
  have hθ : v.im ∈ K := ⟨h3.le, h4.le⟩
  have := huw (show (v.re, v.im) ∈ u ×ˢ w from ⟨hball hx, hKw hθ⟩)
  have e : ((v.re : ℝ) : ℂ) + (v.im : ℂ) * Complex.I = v := Complex.re_add_im v
  simpa [hN, e] using this

theorem jouk_mem_domain (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hne : lamMinus φ n ≠ lamPlus φ n)
    {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n)
    {v : ℂ} (hv : v ∈ Rpos δ0) :
    jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
  refine ⟨hball v (Rpos_subset_Rfull hδ0 hv), ?_⟩
  rw [lamMinus_eq, lamPlus_eq]
  exact jouk_notMem_segment (gapHalf_ne_zero φ n hne) hv.1.1.1

/-- The model integrand `A0`: numerator over the omitted product. -/
def Bfun (φ : PotPair) (n : ℤ) (z : ℂ) : ℂ :=
  (Lib.piN n : ℂ) * deriv (discrim φ) z / (2 * Complex.I * a5OmittedRootProduct38 n (φ, z))

theorem Bfun_analytic (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    AnalyticOnNhd ℂ (Bfun φ n) (discU φ n) := by
  intro z hz
  have hep : (φ, z) ∈ a5OmittedRootDomain38 n := by
    refine ⟨hφ, fun m hmn hseg => ?_⟩
    exact Set.disjoint_left.1 ((isolating φ hφ).1 hmn.symm) hz (own_segment_subset_disc φ hφ m hseg)
  have hP : AnalyticAt ℂ (fun w : ℂ => a5OmittedRootProduct38 n (φ, w)) z :=
    AnalyticAt.comp (g := a5OmittedRootProduct38 n) (f := fun w : ℂ => (φ, w))
      (a5OmittedRoot_analytic38 n (φ, z) hep) (analyticAt_const.prod analyticAt_id)
  have hD : AnalyticAt ℂ (deriv (discrim φ)) z := (analyticOnNhd_discrim_z φ).deriv z (mem_univ _)
  exact (analyticAt_const.mul hD).div (analyticAt_const.mul hP)
    (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (a5OmittedRoot_ne_zero38 n (φ, z) hep))

/-- The root factor has a constant sign relative to `d sinh v` on the positive rectangle. -/
theorem rootFactor_jouk_sign (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hne : lamMinus φ n ≠ lamPlus φ n)
    {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n) :
    ∃ σ : ℂ, σ ^ 2 = 1 ∧ ∀ v ∈ Rpos δ0,
      rootFactor38 n (φ, jouk (gapMid φ n) (gapHalf φ n) v) * (Lib.piN n : ℂ) =
        σ * (gapHalf φ n * Complex.sinh v) := by
  set τ := gapMid φ n with hτ
  set d := gapHalf φ n with hd
  have hd0 : d ≠ 0 := gapHalf_ne_zero φ n hne
  have hdom : ∀ v ∈ Rpos δ0, (φ, jouk τ d v) ∈ rootDomain38 := fun v hv =>
    domain_mem_rootDomain φ hφ n (jouk_mem_domain φ hφ n hne hδ0 hball hv)
  have hjc : Continuous (jouk τ d) := by
    unfold jouk; exact continuous_const.sub (continuous_const.mul Complex.continuous_cosh)
  have hf : ContinuousOn (fun v => rootFactor38 n (φ, jouk τ d v) * (Lib.piN n : ℂ)) (Rpos δ0) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (rootFactor_analytic38 n).continuousOn.comp
      (continuousOn_const.prodMk hjc.continuousOn) (fun v hv => hdom v hv)
  have hg : ContinuousOn (fun v => d * Complex.sinh v) (Rpos δ0) :=
    (continuousOn_const.mul Complex.continuous_sinh.continuousOn)
  have hsq : EqOn ((fun v => rootFactor38 n (φ, jouk τ d v) * (Lib.piN n : ℂ)) ^ 2)
      ((fun v => d * Complex.sinh v) ^ 2) (Rpos δ0) := by
    intro v hv
    have h := rootFactor_sq38 n (φ, jouk τ d v) (hdom v hv)
    simp only at h
    have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
    simp only [Pi.pow_apply]
    rw [mul_pow, h, div_mul_cancel₀ _ (pow_ne_zero 2 hpi), mul_pow, Complex.sinh_sq]
    unfold jouk
    rw [lamMinus_eq, lamPlus_eq]
    have := Complex.cosh_sq v
    ring
  have hne' : ∀ {v : ℂ}, v ∈ Rpos δ0 → d * Complex.sinh v ≠ 0 := by
    intro v hv
    refine mul_ne_zero hd0 (fun hs => ?_)
    have h1 : (Complex.cosh v - 1) * (Complex.cosh v + 1) = 0 := by
      have := Complex.cosh_sq v
      rw [hs] at this
      linear_combination this
    rcases mul_eq_zero.1 h1 with h | h
    · exact cosh_not_unit_real hv.1.1.1 1 (by simp) (by simpa [sub_eq_zero] using h)
    · exact cosh_not_unit_real hv.1.1.1 (-1) (by simp) (by
        have : Complex.cosh v = -1 := by linear_combination h
        simpa using this)
  have hpre : IsPreconnected (Rpos δ0) := (Rpos_convex δ0).isPreconnected
  rcases hpre.eq_or_eq_neg_of_sq_eq hf hg hsq hne' with h | h
  · exact ⟨1, by norm_num, fun v hv => by simpa using h hv⟩
  · exact ⟨-1, by norm_num, fun v hv => by simpa using h hv⟩

end
end NlsGge.ThirdConsultation.MContour

end Part1

section Part2

/- M-008 SUPPORT E3c (proof development, AUTHOR; not reviewed).  R4d: an explicit admissible endpoint curve
   `p t = tau - d cosh (delta sin (pi t) + i pi t)` of an open gap has joint improper integral zero.
   Route: `omega dz = -sigma B(v) dv` (E3b), a primitive `b` of `B` on a rectangle, the zero period of `omega` on the loop
   `v = delta' + 2 pi i t` (S3) gives `b (2 pi i) = b 0`, evenness/periodicity of `cosh` gives `b (i pi) = b 0`. -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- Shorthand: the model integrand in the `v`-plane. -/
def Bj (φ : PotPair) (n : ℤ) (v : ℂ) : ℂ := Bfun φ n (jouk (gapMid φ n) (gapHalf φ n) v)

theorem jouk_hasDerivAt (τ d v : ℂ) : HasDerivAt (jouk τ d) (-(d * Complex.sinh v)) v :=
  ((Complex.hasDerivAt_cosh v).const_mul d).const_sub τ

theorem jouk_continuous (τ d : ℂ) : Continuous (jouk τ d) := by
  unfold jouk; exact continuous_const.sub (continuous_const.mul Complex.continuous_cosh)

theorem jouk_two_pi_sub (τ d v : ℂ) :
    jouk τ d (((2 * Real.pi : ℝ) : ℂ) * Complex.I - v) = jouk τ d v := by
  unfold jouk
  rw [Complex.cosh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I]
  have h1 : Complex.cos ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_cos, Real.cos_two_pi]; simp
  have h2 : Complex.sin ((2 * Real.pi : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sin, Real.sin_two_pi]; simp
  rw [h1, h2]; ring

theorem jouk_add_two_pi (τ d v : ℂ) :
    jouk τ d (v + ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = jouk τ d v := by
  unfold jouk
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  have h1 : Complex.cos ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_cos, Real.cos_two_pi]; simp
  have h2 : Complex.sin ((2 * Real.pi : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sin, Real.sin_two_pi]; simp
  rw [h1, h2]; ring

/-- Pointwise reduction `omega dz = -sigma B dv`. -/
theorem omega_jouk_reduction (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hne : lamMinus φ n ≠ lamPlus φ n)
    {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n)
    {σ : ℂ} (hσ2 : σ ^ 2 = 1)
    (hσ : ∀ v ∈ Rpos δ0, rootFactor38 n (φ, jouk (gapMid φ n) (gapHalf φ n) v) * (Lib.piN n : ℂ) =
        σ * (gapHalf φ n * Complex.sinh v))
    {v : ℂ} (hv : v ∈ Rpos δ0) :
    omega φ (jouk (gapMid φ n) (gapHalf φ n) v) * (-(gapHalf φ n * Complex.sinh v)) =
      -σ * Bj φ n v := by
  set z := jouk (gapMid φ n) (gapHalf φ n) v with hz
  have hzdom := jouk_mem_domain φ hφ n hne hδ0 hball hv
  have hp := domain_mem_rootDomain φ hφ n hzdom
  have hfac := a5CanonRoot_omitted_factorization38 n (φ, z) hp
  simp only at hfac
  have hep : (φ, z) ∈ a5OmittedRootDomain38 n := ⟨hφ, fun m _ => rootDomain_avoids38 hp m⟩
  have hrf0 : rootFactor38 n (φ, z) ≠ 0 := rootFactor_ne_zero38 n (φ, z) hp
  have hP0 : a5OmittedRootProduct38 n (φ, z) ≠ 0 := a5OmittedRoot_ne_zero38 n (φ, z) hep
  have h := hσ v hv
  rw [← hz] at h
  unfold omega Bj Bfun
  rw [← hz, hfac]
  set rf := rootFactor38 n (φ, z)
  set P := a5OmittedRootProduct38 n (φ, z)
  set D' := deriv (discrim φ) z
  set s := Complex.sinh v
  set d := gapHalf φ n
  set pn : ℂ := (Lib.piN n : ℂ)
  have h2 : (2 * Complex.I * rf * P) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hrf0) hP0
  have h3 : (2 * Complex.I * P) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hP0
  rw [div_mul_eq_mul_div, div_eq_iff h2]
  have e1 : pn * D' / (2 * Complex.I * P) * (2 * Complex.I * rf * P) = pn * D' * rf := by
    field_simp
  have e2 : -σ * (pn * D' / (2 * Complex.I * P)) * (2 * Complex.I * rf * P) =
      -σ * (pn * D' / (2 * Complex.I * P) * (2 * Complex.I * rf * P)) := by ring
  rw [e2, e1]
  linear_combination (σ * D') * h + (D' * d * s) * hσ2

/-- Chain rule: the integrand along a `C^1` curve `v` in the positive rectangle. -/
theorem omega_jouk_curve_integrand (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hne : lamMinus φ n ≠ lamPlus φ n)
    {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n)
    {σ : ℂ} (hσ2 : σ ^ 2 = 1)
    (hσ : ∀ v ∈ Rpos δ0, rootFactor38 n (φ, jouk (gapMid φ n) (gapHalf φ n) v) * (Lib.piN n : ℂ) =
        σ * (gapHalf φ n * Complex.sinh v))
    (v : ℝ → ℂ) (v' : ℂ) (t : ℝ) (hvd : HasDerivAt v v' t) (hv : v t ∈ Rpos δ0) :
    omega φ (jouk (gapMid φ n) (gapHalf φ n) (v t)) *
        deriv (fun s => jouk (gapMid φ n) (gapHalf φ n) (v s)) t =
      -σ * (Bj φ n (v t) * v') := by
  have hd : HasDerivAt (fun s => jouk (gapMid φ n) (gapHalf φ n) (v s))
      (v' • (-(gapHalf φ n * Complex.sinh (v t)))) t :=
    (jouk_hasDerivAt (gapMid φ n) (gapHalf φ n) (v t)).scomp t hvd
  rw [hd.deriv, smul_eq_mul]
  have := omega_jouk_reduction φ hφ n hne hδ0 hball hσ2 hσ hv
  calc omega φ (jouk (gapMid φ n) (gapHalf φ n) (v t)) * (v' * -(gapHalf φ n * Complex.sinh (v t)))
      = (omega φ (jouk (gapMid φ n) (gapHalf φ n) (v t)) * (-(gapHalf φ n * Complex.sinh (v t)))) * v' := by ring
    _ = -σ * (Bj φ n (v t) * v') := by rw [this]; ring

theorem Bj_differentiableOn (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {δ0 : ℝ}
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n) :
    DifferentiableOn ℂ (Bj φ n) (Rfull δ0) := by
  intro v hv
  have h1 : DifferentiableAt ℂ (Bfun φ n) (jouk (gapMid φ n) (gapHalf φ n) v) :=
    (Bfun_analytic φ hφ n _ (hball v hv)).differentiableAt
  exact (h1.comp v (jouk_hasDerivAt _ _ v).differentiableAt).differentiableWithinAt

/-- A primitive of `B` on the full rectangle. -/
theorem Bj_primitive (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {δ0 : ℝ}
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n) :
    ∃ b : ℂ → ℂ, ∀ v ∈ Rfull δ0, HasDerivAt b (Bj φ n v) v := by
  obtain ⟨b, hb⟩ := (Rfull_convex δ0).exists_forall_hasDerivWithinAt (Bj_differentiableOn φ hφ n hball)
  exact ⟨b, fun v hv => (hb v hv).hasDerivAt ((Rfull_isOpen δ0).mem_nhds hv)⟩

/-- Zero period on the loop `Re v = delta'` gives `b (delta' + 2 pi i) = b delta'`. -/
theorem primitive_loop_eq (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hne : lamMinus φ n ≠ lamPlus φ n)
    {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n)
    {σ : ℂ} (hσ2 : σ ^ 2 = 1)
    (hσ : ∀ v ∈ Rpos δ0, rootFactor38 n (φ, jouk (gapMid φ n) (gapHalf φ n) v) * (Lib.piN n : ℂ) =
        σ * (gapHalf φ n * Complex.sinh v))
    {b : ℂ → ℂ} (hb : ∀ v ∈ Rfull δ0, HasDerivAt b (Bj φ n v) v)
    {δ' : ℝ} (hδ'0 : 0 < δ') (hδ'1 : δ' < δ0) :
    b ((δ' : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I) = b (δ' : ℂ) := by
  set v : ℝ → ℂ := fun t => (δ' : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I with hv
  set v' : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I with hv'
  have hvd : ∀ t, HasDerivAt v v' t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((2 * Real.pi * t : ℝ) : ℂ)) ((2 * Real.pi : ℝ) : ℂ) t := by
      have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).ofReal_comp
      simpa using this
    simpa [hv, hv'] using (h1.mul_const Complex.I).const_add (δ' : ℂ)
  have hvmem : ∀ t ∈ Icc (0 : ℝ) 1, v t ∈ Rpos δ0 := by
    intro t ht
    have h2 : (v t).re = δ' := by simp [hv]
    have h3 : (v t).im = 2 * Real.pi * t := by simp [hv]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · show 0 < (v t).re; rw [h2]; exact hδ'0
    · show (v t).re < δ0; rw [h2]; exact hδ'1
    · show -1 < (v t).im; rw [h3]; nlinarith [Real.pi_pos, ht.1]
    · show (v t).im < 2 * Real.pi + 1; rw [h3]; nlinarith [Real.pi_pos, ht.2]
  have hvfull : ∀ t ∈ Icc (0 : ℝ) 1, v t ∈ Rfull δ0 := fun t ht =>
    Rpos_subset_Rfull hδ0 (hvmem t ht)
  set p : ℝ → ℂ := fun t => jouk (gapMid φ n) (gapHalf φ n) (v t) with hp
  have hvcd : ContDiff ℝ 1 v := by
    simp only [hv]
    exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
      contDiff_const)
  have hpcd : ContDiff ℝ 1 p := by
    simp only [hp, jouk]
    exact contDiff_const.sub (contDiff_const.mul ((Complex.contDiff_cosh.restrict_scalars ℝ).comp hvcd))
  have hadm : AdmissibleGapLoop φ n p := by
    refine ⟨hpcd.contDiffOn, ?_, fun t ht => ?_⟩
    · have : v 1 = v 0 + ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by simp [hv]
      simp only [hp]
      rw [this, jouk_add_two_pi]
    · have hd := jouk_mem_domain φ hφ n hne hδ0 hball (hvmem t ht)
      exact hd
  obtain ⟨-, hzero⟩ := omega_gap_loop_zero φ hφ n p hadm
  unfold contourIntegral at hzero
  have hcongr : ∫ t in (0 : ℝ)..1, omega φ (p t) * deriv p t =
      ∫ t in (0 : ℝ)..1, (-σ) * (Bj φ n (v t) * v') := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le zero_le_one] at ht
    exact omega_jouk_curve_integrand φ hφ n hne hδ0 hball hσ2 hσ v v' t (hvd t) (hvmem t ht)
  rw [hcongr, intervalIntegral.integral_const_mul] at hzero
  have hBcont : ContinuousOn (fun t : ℝ => Bj φ n (v t) * v') (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (Bj_differentiableOn φ hφ n hball).continuousOn.comp hvcd.continuous.continuousOn hvfull
  have hftc : ∫ t in (0 : ℝ)..1, Bj φ n (v t) * v' = b (v 1) - b (v 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => b (v t)) (fun t ht => ?_)
      (hBcont.intervalIntegrable)
    rw [uIcc_of_le zero_le_one] at ht
    have h := (hb (v t) (hvfull t ht)).scomp t (hvd t)
    simp only [smul_eq_mul] at h
    exact h.congr_deriv (mul_comm _ _)
  rw [hftc] at hzero
  have hσ0 : σ ≠ 0 := by
    intro h; rw [h] at hσ2; norm_num at hσ2
  have hdiff : b (v 1) - b (v 0) = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd (neg_eq_zero.1 h) hσ0
    · exact h
  have h1 : v 1 = (δ' : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by simp [hv]
  have h0 : v 0 = (δ' : ℂ) := by simp [hv]
  rw [h1, h0] at hdiff
  exact sub_eq_zero.1 hdiff

end
end NlsGge.ThirdConsultation.MContour

end Part2

section Part3

/- M-008 SUPPORT E3d (proof development, AUTHOR; not reviewed).  Continuation of E3c: `b (i pi) = b 0`, and the explicit admissible
   endpoint curve with zero joint improper integral (R4d). -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

theorem mem_Rfull_of_imag {δ0 : ℝ} (hδ0 : 0 < δ0) (x : ℝ) (hx1 : -1 < x) (hx2 : x < 2 * Real.pi + 1) :
    ((x : ℂ) * Complex.I) ∈ Rfull δ0 := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp [hx1, hx2, hδ0]

theorem primitive_symm (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hne : lamMinus φ n ≠ lamPlus φ n)
    {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hball : ∀ v : ℂ, v ∈ Rfull δ0 → jouk (gapMid φ n) (gapHalf φ n) v ∈ discU φ n)
    {σ : ℂ} (hσ2 : σ ^ 2 = 1)
    (hσ : ∀ v ∈ Rpos δ0, rootFactor38 n (φ, jouk (gapMid φ n) (gapHalf φ n) v) * (Lib.piN n : ℂ) =
        σ * (gapHalf φ n * Complex.sinh v))
    {b : ℂ → ℂ} (hb : ∀ v ∈ Rfull δ0, HasDerivAt b (Bj φ n v) v) :
    b (((Real.pi : ℝ) : ℂ) * Complex.I) = b 0 := by
  set c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I with hc
  have hpi := Real.pi_pos
  have h0mem : (0 : ℂ) ∈ Rfull δ0 := by
    have := mem_Rfull_of_imag hδ0 0 (by norm_num) (by linarith)
    simpa using this
  have hcmem : c ∈ Rfull δ0 := mem_Rfull_of_imag hδ0 _ (by linarith) (by linarith)
  have hpmem : ((Real.pi : ℝ) : ℂ) * Complex.I ∈ Rfull δ0 :=
    mem_Rfull_of_imag hδ0 _ (by linarith) (by linarith)
  -- (a) b c = b 0
  have hbc0 : ContinuousAt b 0 := (hb 0 h0mem).continuousAt
  have hbcc : ContinuousAt b c := (hb c hcmem).continuousAt
  have hmap1 : Tendsto (fun δ' : ℝ => (δ' : ℂ) + c) (𝓝[>] 0) (𝓝 c) := by
    have : Continuous (fun δ' : ℝ => (δ' : ℂ) + c) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hmap0 : Tendsto (fun δ' : ℝ => (δ' : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous (fun δ' : ℝ => (δ' : ℂ)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 := hbcc.tendsto.comp hmap1
  have h0 := hbc0.tendsto.comp hmap0
  have heq : (fun δ' : ℝ => b ((δ' : ℂ) + c)) =ᶠ[𝓝[>] 0] (fun δ' : ℝ => b (δ' : ℂ)) := by
    filter_upwards [Ioo_mem_nhdsGT hδ0] with δ' hδ'
    exact primitive_loop_eq φ hφ n hne hδ0 hball hσ2 hσ hb hδ'.1 hδ'.2
  have hbc : b c = b 0 := tendsto_nhds_unique (h1.congr' heq) h0
  -- (b) reflection
  have hrefl : ∀ v ∈ Rfull δ0, c - v ∈ Rfull δ0 := by
    intro v hv
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
    simp only [mem_setOf_eq] at h1 h2 h3 h4
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp [hc] <;> linarith
  have hHd : ∀ v ∈ Rfull δ0, HasDerivAt (fun w => b w + b (c - w)) 0 v := by
    intro v hv
    have h1 := hb v hv
    have h2 := (hb (c - v) (hrefl v hv)).comp v ((hasDerivAt_id v).const_sub c)
    have h3 : HasDerivAt (fun w => b w + b (c - w)) (Bj φ n v + Bj φ n (c - v) * -1) v := h1.add h2
    have hBeq : Bj φ n (c - v) = Bj φ n v := by
      unfold Bj; rw [hc, jouk_two_pi_sub]
    rw [hBeq] at h3
    exact h3.congr_deriv (by ring)
  have hconst := (Rfull_isOpen δ0).is_const_of_deriv_eq_zero (Rfull_convex δ0).isPreconnected
    (f := fun w => b w + b (c - w))
    (fun v hv => (hHd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hHd v hv).deriv) hpmem h0mem
  have hcp : c - ((Real.pi : ℝ) : ℂ) * Complex.I = ((Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [hc]; push_cast; ring
  rw [hcp, sub_zero, hbc] at hconst
  linear_combination (1 / 2 : ℂ) * hconst

end
end NlsGge.ThirdConsultation.MContour

end Part3

