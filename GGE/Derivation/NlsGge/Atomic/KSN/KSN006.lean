import Mathlib
import NlsGge.GK38.TauGamma
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.G4.G4019
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN006Host

/- KSN-006 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN006.lean.
   Head `KSN006_main`: design STATEMENTS/KSN.md KSN-006 section, verbatim (STATEMENTS/KSN.md and DEFINITIONS/KSN.lean.md are
   byte-identical in followup1..10; no Pro round response or BINDING_INDEX entry touches KSN-006; no lexical repair).
   Host objects (collapsedDD, nearSegment, nearRoot, dividedIntegrand, dividedPart) are in KSN006Host.
   Route (source skeleton): U, M from the landed G4-019 (nbhd, convex isolating ball, |zeta'| <= M on it; the data of G4-018/G4-019, no
   analytic anchor); Cauchy/mean-value bound |DD| <= M (divided difference of a function with |zeta'| <= M on a convex set);
   nearer-endpoint segment lambda_-(1-t)+mu t; |A - seg| >= |gamma|/2 (A = lamPlus; half-plane argument from |mu-B| <= |mu-A|);
   |nearRoot| = sqrt t sqrt|mu-B| sqrt|A-seg| from KSN002's (terminalRoot)^2 = (A-mu)(B-mu); integrate t^(-1/2), retaining
   both geometric terms; constant 4M. The prerequisites G4-021/G4-036/G4-038/KSN-004/G4-007 are not needed by this route. -/
set_option autoImplicit false

namespace NlsGge.Atomic.KSN006Support
noncomputable section
open Set Filter Topology MeasureTheory

/-- Pure real inequality behind the KSN-006 pointwise bound. -/
theorem key_real {g m t w M D T : ℝ} (hg : 0 < g) (hm : 0 < m) (ht : 0 < t)
    (hw1 : g / 2 ≤ w) (hw2 : w ≤ g + t * m) (hM : 0 ≤ M) (hD : D ≤ M)
    (hT : T ≤ g / 2 + w) (hT0 : 0 ≤ T) :
    m * D * T / (Real.sqrt t * Real.sqrt m * Real.sqrt w)
      ≤ 2 * M * Real.sqrt m * Real.sqrt g * (Real.sqrt t)⁻¹ + M * m := by
  have hw : 0 < w := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have ha2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  have hs2 : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  have hb2 : (Real.sqrt t * Real.sqrt m) ^ 2 = t * m := by
    rw [mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt hm.le]
  have hb0 : 0 ≤ Real.sqrt t * Real.sqrt m := by positivity
  have hsa : Real.sqrt g / 2 ≤ Real.sqrt w := by
    by_contra h
    have h' := not_le.1 h
    nlinarith [mul_pos (sub_pos.2 h') (add_pos (div_pos hsg two_pos) hsw)]
  have hsb : Real.sqrt w ≤ Real.sqrt g + Real.sqrt t * Real.sqrt m := by
    by_contra h
    have h' := not_le.1 h
    have hpos : 0 < Real.sqrt w + (Real.sqrt g + Real.sqrt t * Real.sqrt m) := by linarith
    nlinarith [mul_pos (sub_pos.2 h') hpos, mul_nonneg hsg.le hb0]
  have hC1 : g / 2 + w ≤ (2 * Real.sqrt g + Real.sqrt t * Real.sqrt m) * Real.sqrt w := by
    have e1 : Real.sqrt g * (Real.sqrt g / 2) ≤ Real.sqrt g * Real.sqrt w :=
      mul_le_mul_of_nonneg_left hsa hsg.le
    have e2 : Real.sqrt w * Real.sqrt w
        ≤ (Real.sqrt g + Real.sqrt t * Real.sqrt m) * Real.sqrt w :=
      mul_le_mul_of_nonneg_right hsb hsw.le
    nlinarith [e1, e2, ha2, hs2]
  have hden : 0 < Real.sqrt t * Real.sqrt m * Real.sqrt w := by positivity
  rw [div_le_iff₀ hden]
  have h1 : m * D * T ≤ m * M * (g / 2 + w) := by
    have h0 : D * T ≤ M * (g / 2 + w) := by
      by_cases hD0 : 0 ≤ D
      · exact mul_le_mul hD hT hT0 hM
      · have : D * T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_le.1 hD0).le hT0
        have : 0 ≤ M * (g / 2 + w) := by positivity
        linarith
    calc m * D * T = m * (D * T) := by ring
      _ ≤ m * (M * (g / 2 + w)) := mul_le_mul_of_nonneg_left h0 hm.le
      _ = m * M * (g / 2 + w) := by ring
  have h2 : m * M * (g / 2 + w)
      ≤ m * M * ((2 * Real.sqrt g + Real.sqrt t * Real.sqrt m) * Real.sqrt w) :=
    mul_le_mul_of_nonneg_left hC1 (by positivity)
  have hinv : (Real.sqrt t)⁻¹ * Real.sqrt t = 1 := inv_mul_cancel₀ hst.ne'
  have hqq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have hE : (2 * M * Real.sqrt m * Real.sqrt g * (Real.sqrt t)⁻¹ + M * m)
        * (Real.sqrt t * Real.sqrt m * Real.sqrt w)
      = m * M * ((2 * Real.sqrt g + Real.sqrt t * Real.sqrt m) * Real.sqrt w) := by
    linear_combination (2 * M * Real.sqrt g * Real.sqrt w * ((Real.sqrt t)⁻¹ * Real.sqrt t)) * hqq
      + (2 * M * Real.sqrt g * Real.sqrt w * m) * hinv
  rw [hE]
  exact h1.trans h2

/-- Collapsed divided difference equals minus `dslope`. -/
theorem dd_eq_dslope (f : ℂ → ℂ) (τ z : ℂ) :
    (if z = τ then -deriv f τ else (f z - f τ) / (τ - z)) = -dslope f τ z := by
  by_cases h : z = τ
  · subst h
    simp
  · rw [if_neg h, dslope_of_ne f h, slope_def_field]
    have : τ - z = -(z - τ) := by ring
    rw [this, div_neg]

theorem dd_continuousOn {f : ℂ → ℂ} {s : Set ℂ} {τ : ℂ}
    (hd : ∀ w ∈ s, DifferentiableAt ℂ f w) :
    ContinuousOn (fun z => if z = τ then -deriv f τ else (f z - f τ) / (τ - z)) s := by
  refine ContinuousOn.congr (f := fun z => -dslope f τ z) (fun z hz => ?_)
    (fun z _ => dd_eq_dslope f τ z)
  have hc : ContinuousAt (dslope f τ) z := by
    by_cases h : z = τ
    · subst h
      exact continuousAt_dslope_same.2 (hd z hz)
    · exact (continuousAt_dslope_of_ne h).2 (hd z hz).continuousAt
  exact hc.neg.continuousWithinAt

theorem dd_bound {f : ℂ → ℂ} {s : Set ℂ} {τ : ℂ} {M : ℝ} (hs : Convex ℝ s) (hτ : τ ∈ s)
    (hd : ∀ w ∈ s, DifferentiableAt ℂ f w) (hM : ∀ w ∈ s, ‖deriv f w‖ ≤ M)
    {z : ℂ} (hz : z ∈ s) :
    ‖if z = τ then -deriv f τ else (f z - f τ) / (τ - z)‖ ≤ M := by
  by_cases h : z = τ
  · rw [if_pos h, norm_neg]
    exact hM τ hτ
  · rw [if_neg h, norm_div]
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) hd hM hs hτ hz
    have hpos : 0 < ‖τ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))
    rw [div_le_iff₀ hpos, norm_sub_rev τ z]
    exact hmv

/-- Distance from the far endpoint along the near segment. -/
theorem seg_lower {g m : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hg : g ≠ 0)
    (hn : ‖m‖ ≤ ‖m - g‖) : ‖g‖ / 2 ≤ ‖g - (t : ℂ) * m‖ := by
  have hre : 2 * (m.re * g.re + m.im * g.im) ≤ g.re ^ 2 + g.im ^ 2 := by
    have h2 : ‖m‖ ^ 2 ≤ ‖m - g‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
    simp only [Complex.sub_re, Complex.sub_im] at h2
    nlinarith [h2]
  have hS : 0 ≤ g.re ^ 2 + g.im ^ 2 := by positivity
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hgS : ‖g‖ ^ 2 = g.re ^ 2 + g.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hxre : (g - (t : ℂ) * m).re = g.re - t * m.re := by simp
  have hxim : (g - (t : ℂ) * m).im = g.im - t * m.im := by simp
  have hP : (g.re ^ 2 + g.im ^ 2) / 2
      ≤ (g - (t : ℂ) * m).re * g.re + (g - (t : ℂ) * m).im * g.im := by
    rw [hxre, hxim]
    nlinarith [mul_nonneg ht0 (sub_nonneg.2 hre), mul_nonneg (sub_nonneg.2 ht1) hS]
  have hCS : (g - (t : ℂ) * m).re * g.re + (g - (t : ℂ) * m).im * g.im
      ≤ ‖g - (t : ℂ) * m‖ * ‖g‖ := by
    have h1 : ((g - (t : ℂ) * m) * (starRingEnd ℂ) g).re
        = (g - (t : ℂ) * m).re * g.re + (g - (t : ℂ) * m).im * g.im := by
      simp [Complex.mul_re]
    have h2 : ((g - (t : ℂ) * m) * (starRingEnd ℂ) g).re
        ≤ ‖(g - (t : ℂ) * m) * (starRingEnd ℂ) g‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [norm_mul, Complex.norm_conj] at h2
    linarith
  have hfin : (‖g‖ / 2) * ‖g‖ ≤ ‖g - (t : ℂ) * m‖ * ‖g‖ := by
    nlinarith [hP, hCS, hgS]
  exact le_of_mul_le_mul_right hfin hgpos


/-- Parametrised data of KSN-006 (segment, divided difference, near root, integrand). -/
def segF (B μ : ℂ) (t : ℝ) : ℂ := B + (t : ℂ) * (μ - B)

def ddF (ζ : ℂ → ℂ) (τ z : ℂ) : ℂ :=
  if z = τ then -deriv ζ τ else (ζ z - ζ τ) / (τ - z)

def nrF (A B μ R : ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt t : ℂ) * R * Complex.sqrt ((A - segF B μ t) / (A - μ))

def coreF (A B μ τ R : ℂ) (ζ : ℂ → ℂ) (t : ℝ) : ℂ :=
  (μ - B) * ddF ζ τ (segF B μ t) * (τ - segF B μ t) / nrF A B μ R t

theorem continuous_segF (B μ : ℂ) : Continuous (segF B μ) := by
  unfold segF
  fun_prop

theorem norm_csqrt {z : ℂ} (hz : z ≠ 0) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
  rw [Complex.sqrt, Complex.norm_cpow_of_ne_zero hz]
  have h2 : (2⁻¹ : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; norm_num
  rw [h2, Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one,
    Real.sqrt_eq_rpow]

theorem nr_norm {A B μ R : ℂ} {t : ℝ} (ht : 0 < t) (hR : R ^ 2 = (A - μ) * (B - μ))
    (hAμ : A - μ ≠ 0) (hAs : A - segF B μ t ≠ 0) :
    ‖nrF A B μ R t‖ = Real.sqrt t * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - segF B μ t‖ := by
  have hratio : (A - segF B μ t) / (A - μ) ≠ 0 := div_ne_zero hAs hAμ
  have hRn : ‖R‖ = Real.sqrt ‖A - μ‖ * Real.sqrt ‖μ - B‖ := by
    have h1 : ‖R‖ ^ 2 = ‖A - μ‖ * ‖μ - B‖ := by
      have h0 := congrArg norm hR
      rw [norm_pow, norm_mul, norm_sub_rev B μ] at h0
      exact h0
    rw [← Real.sqrt_mul (norm_nonneg _), ← h1, Real.sqrt_sq (norm_nonneg _)]
  have hsa : 0 < Real.sqrt ‖A - μ‖ := Real.sqrt_pos.2 (norm_pos_iff.2 hAμ)
  unfold nrF
  rw [norm_mul, norm_mul, norm_csqrt hratio, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), hRn, Real.sqrt_div (norm_nonneg _)]
  field_simp

theorem core {A B μ τ R : ℂ} {ζ : ℂ → ℂ} {s : Set ℂ} {M : ℝ}
    (hs : Convex ℝ s) (hB : B ∈ s) (hμ : μ ∈ s) (hτm : τ ∈ s)
    (hd : ∀ w ∈ s, DifferentiableAt ℂ ζ w) (hM : ∀ w ∈ s, ‖deriv ζ w‖ ≤ M) (hM0 : 0 ≤ M)
    (hτ : τ = (A + B) / 2) (hg : A - B ≠ 0) (hnear : ‖μ - B‖ ≤ ‖μ - A‖)
    (hR : R ^ 2 = (A - μ) * (B - μ)) :
    IntervalIntegrable (coreF A B μ τ R ζ) volume 0 1 ∧
    ‖∫ t in (0 : ℝ)..1, coreF A B μ τ R ζ t‖ ≤
      4 * M * (Real.sqrt ‖A - B‖ * Real.sqrt ‖μ - B‖ + ‖μ - B‖) := by
  by_cases hm : μ = B
  · have hF : coreF A B μ τ R ζ = fun _ => 0 := by
      funext t
      simp [coreF, hm]
    rw [hF]
    refine ⟨intervalIntegrable_const, ?_⟩
    simp [hm]
  · have hmne : μ - B ≠ 0 := sub_ne_zero.2 hm
    have hmpos : 0 < ‖μ - B‖ := norm_pos_iff.2 hmne
    have hgpos : 0 < ‖A - B‖ := norm_pos_iff.2 hg
    have hAμ : A - μ ≠ 0 := by
      intro h
      have hA : A = μ := sub_eq_zero.1 h
      apply hm
      have h0 : ‖μ - A‖ = 0 := by rw [← hA, sub_self, norm_zero]
      have h1 : ‖μ - B‖ ≤ 0 := by linarith
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
    have hseg_mem : ∀ t ∈ Icc (0 : ℝ) 1, segF B μ t ∈ s := by
      intro t ht
      have h1 := hs hB hμ (sub_nonneg.2 ht.2) ht.1 (by ring)
      convert h1 using 1
      simp only [segF, Complex.real_smul]
      push_cast
      ring
    have hlow : ∀ t ∈ Icc (0 : ℝ) 1, ‖A - B‖ / 2 ≤ ‖A - segF B μ t‖ := by
      intro t ht
      have hn : ‖μ - B‖ ≤ ‖(μ - B) - (A - B)‖ := by
        have e : (μ - B) - (A - B) = μ - A := by ring
        rw [e]
        exact hnear
      have h1 := seg_lower ht.1 ht.2 hg hn
      have e : A - B - (t : ℂ) * (μ - B) = A - segF B μ t := by
        simp only [segF]
        ring
      rwa [e] at h1
    have hAs : ∀ t ∈ Icc (0 : ℝ) 1, A - segF B μ t ≠ 0 := by
      intro t ht h
      have h1 := hlow t ht
      rw [h, norm_zero] at h1
      linarith
    have hup : ∀ t ∈ Icc (0 : ℝ) 1, ‖A - segF B μ t‖ ≤ ‖A - B‖ + t * ‖μ - B‖ := by
      intro t ht
      have e : A - segF B μ t = (A - B) - (t : ℂ) * (μ - B) := by
        simp only [segF]
        ring
      rw [e]
      calc ‖(A - B) - (t : ℂ) * (μ - B)‖ ≤ ‖A - B‖ + ‖(t : ℂ) * (μ - B)‖ := norm_sub_le _ _
        _ = ‖A - B‖ + t * ‖μ - B‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hτA : ‖τ - A‖ = ‖A - B‖ / 2 := by
      have e : τ - A = -((A - B) / 2) := by rw [hτ]; ring
      rw [e, norm_neg, norm_div]
      norm_num
    have hTb : ∀ t ∈ Icc (0 : ℝ) 1, ‖τ - segF B μ t‖ ≤ ‖A - B‖ / 2 + ‖A - segF B μ t‖ := by
      intro t ht
      have e : τ - segF B μ t = (τ - A) + (A - segF B μ t) := by ring
      rw [e]
      calc ‖(τ - A) + (A - segF B μ t)‖ ≤ ‖τ - A‖ + ‖A - segF B μ t‖ := norm_add_le _ _
        _ = ‖A - B‖ / 2 + ‖A - segF B μ t‖ := by rw [hτA]
    have hpt : ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖coreF A B μ τ R ζ t‖ ≤
          (2 * M * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ))
            + M * ‖μ - B‖ := by
      intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hnr := nr_norm ht.1 hR hAμ (hAs t htI)
      have hDD : ‖ddF ζ τ (segF B μ t)‖ ≤ M := dd_bound hs hτm hd hM (hseg_mem t htI)
      have key := key_real (g := ‖A - B‖) (m := ‖μ - B‖) (t := t) (w := ‖A - segF B μ t‖)
        (M := M) (D := ‖ddF ζ τ (segF B μ t)‖) (T := ‖τ - segF B μ t‖) hgpos hmpos ht.1
        (hlow t htI) (hup t htI) hM0 hDD (hTb t htI) (norm_nonneg _)
      have e : ‖coreF A B μ τ R ζ t‖ = ‖μ - B‖ * ‖ddF ζ τ (segF B μ t)‖ * ‖τ - segF B μ t‖ /
          (Real.sqrt t * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - segF B μ t‖) := by
        unfold coreF
        rw [norm_div, norm_mul, norm_mul, hnr]
      rw [e]
      have hrp : (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.1.le]
      rw [hrp] at key
      exact key
    have hG : IntervalIntegrable
        (fun t : ℝ => (2 * M * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ))
          + M * ‖μ - B‖) volume 0 1 :=
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul
        _).add intervalIntegrable_const
    have hcont : ContinuousOn (fun t : ℝ => ddF ζ τ (segF B μ t)) (Icc 0 1) :=
      (dd_continuousOn hd).comp (continuous_segF B μ).continuousOn hseg_mem
    have hmeas : AEStronglyMeasurable (coreF A B μ τ R ζ) (volume.restrict (Ioc (0 : ℝ) 1)) := by
      have h1 : AEMeasurable (fun t : ℝ => ddF ζ τ (segF B μ t))
          (volume.restrict (Ioc (0 : ℝ) 1)) :=
        (hcont.aemeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self
      have hseg : Measurable (segF B μ) := (continuous_segF B μ).measurable
      have hnum : AEMeasurable
          (fun t : ℝ => (μ - B) * ddF ζ τ (segF B μ t) * (τ - segF B μ t))
          (volume.restrict (Ioc (0 : ℝ) 1)) :=
        (h1.const_mul (μ - B)).mul (measurable_const.sub hseg).aemeasurable
      have hsq : Measurable (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp Real.continuous_sqrt).measurable
      have hcs : Measurable (fun t : ℝ => Complex.sqrt ((A - segF B μ t) / (A - μ))) := by
        have h2 : Measurable (fun t : ℝ => (A - segF B μ t) / (A - μ)) :=
          (measurable_const.sub hseg).div_const _
        exact h2.pow_const (2⁻¹ : ℂ)
      have hden : Measurable (nrF A B μ R) := (hsq.mul measurable_const).mul hcs
      exact (hnum.div hden.aemeasurable).aestronglyMeasurable
    have hint : IntervalIntegrable (coreF A B μ τ R ζ) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      have hGi := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hG
      refine Integrable.mono' hGi hmeas ?_
      exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt)
    refine ⟨hint, ?_⟩
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall hpt) hG
    have hI : ∫ t in (0 : ℝ)..1,
        ((2 * M * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ)) + M * ‖μ - B‖)
        = 2 * (2 * M * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) + M * ‖μ - B‖ := by
      rw [intervalIntegral.integral_add
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul _)
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
      have h0 : (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
      rw [h0]
      simp only [Real.one_rpow, intervalIntegral.integral_const, smul_eq_mul]
      norm_num
      ring
    calc ‖∫ t in (0 : ℝ)..1, coreF A B μ τ R ζ t‖
        ≤ ∫ t in (0 : ℝ)..1,
          ((2 * M * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) * t ^ (-(1 / 2 : ℝ))
            + M * ‖μ - B‖) := hnorm
      _ = 2 * (2 * M * Real.sqrt ‖μ - B‖ * Real.sqrt ‖A - B‖) + M * ‖μ - B‖ := hI
      _ ≤ 4 * M * (Real.sqrt ‖A - B‖ * Real.sqrt ‖μ - B‖ + ‖μ - B‖) := by
        nlinarith [mul_nonneg hM0 hmpos.le]

end
end NlsGge.Atomic.KSN006Support

namespace NlsGge.ThirdConsultation.KSN
noncomputable section
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign

theorem KSN006_main (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ (U : Set PotPair) (C : ℝ), IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧ 0 ≤ C ∧
    ∀ φ ∈ U, ∀ n : ℤ, gamma2 φ n ≠ 0 →
      ‖muSeq φ n - lamMinus φ n‖ ≤ ‖muSeq φ n - lamPlus φ n‖ →
      (muSeq φ n = lamMinus φ n ∨ lamPlus φ n - muSeq φ n ≠ 0) ∧
      IntervalIntegrable (dividedIntegrand n φ) volume 0 1 ∧
      ‖dividedPart n φ‖ ≤ C *
        (Real.sqrt ‖lamPlus φ n - lamMinus φ n‖ *
          Real.sqrt ‖muSeq φ n - lamMinus φ n‖ + ‖muSeq φ n - lamMinus φ n‖) := by
  obtain ⟨V, hVn, hVo, hVB, C, R, r, ε, M, hε, hM, hfam, hrR, hseg, hdiff⟩ :=
    G4019 φ₀ hφ₀
  refine ⟨V, 4 * M, hVo, mem_of_mem_nhds hVn, hVB, by linarith, ?_⟩
  intro φ hφ n hγ hnear
  have hφS : φ ∈ sourceBetaW := hVB hφ
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφS)
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hgk n
  have hg2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  have hg : lamPlus φ n - lamMinus φ n ≠ 0 := by
    intro h
    apply hγ
    rw [hg2, h]
    norm_num
  have hRsq := ((KSN002_main n).2 φ hφS).2.2.2
  have hconv : Convex ℝ (Metric.ball (C n) (r n)) := convex_ball _ _
  have hBm : lamMinus φ n ∈ Metric.ball (C n) (r n) :=
    (hseg φ hφ n).1 (left_mem_segment ℝ _ _)
  have hAm : lamPlus φ n ∈ Metric.ball (C n) (r n) :=
    (hseg φ hφ n).1 (right_mem_segment ℝ _ _)
  have hμm : muSeq φ n ∈ Metric.ball (C n) (r n) := (hseg φ hφ n).2
  have hτm : tauN φ n ∈ Metric.ball (C n) (r n) := by
    have h1 := hconv hAm hBm (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert h1 using 1
    rw [hτ]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hdiffn : ∀ w ∈ Metric.ball (C n) (r n), DifferentiableAt ℂ (normalizedZeta n φ) w :=
    fun w hw => (hdiff φ hφ n w hw).1
  have hMb : ∀ w ∈ Metric.ball (C n) (r n), ‖deriv (normalizedZeta n φ) w‖ ≤ M :=
    fun w hw => (hdiff φ hφ n w hw).2
  have hcore := NlsGge.Atomic.KSN006Support.core (A := lamPlus φ n) (B := lamMinus φ n)
    (μ := muSeq φ n) (τ := tauN φ n) (R := terminalRoot n φ) (ζ := normalizedZeta n φ)
    hconv hBm hμm hτm hdiffn hMb hM.le hτ hg hnear hRsq
  refine ⟨?_, hcore.1, hcore.2⟩
  by_cases hm : muSeq φ n = lamMinus φ n
  · exact Or.inl hm
  · right
    intro h
    apply hm
    have hA : lamPlus φ n = muSeq φ n := sub_eq_zero.1 h
    have h0 : ‖muSeq φ n - lamPlus φ n‖ = 0 := by rw [← hA, sub_self, norm_zero]
    have h1 : ‖muSeq φ n - lamMinus φ n‖ ≤ 0 := by linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)

end
end NlsGge.ThirdConsultation.KSN
