import NlsGge.Hierarchy.ALSamplingV2Formula38
import NlsGge.Atomic.G1.G1036
import NlsGge.ThirdConsultation.M.M053Sup2

/-! ORIGINAL record L04, clause B086.C01 (paper/v2.tex 2028-2033, `C:eq:V2positive`).

Statement `alNormSq_weakDeriv_V2_38` is the independently reviewed (SOL-STMTL-20261111,
APPROVABLE_AS_STATED) frozen command of `AuthOrig-20261111/STATEMENTS_L03_L04.md`, copied
byte-for-byte from the elaborated probe `probe-AllSAOrigL0304Probe.lean`.

Imports (each needed):
* `NlsGge.Hierarchy.ALSamplingV2Formula38`: `alCanon38`, `alDeriv38`, `alV2_38`,
  `alV2_eq_integral38`, `alLiftInt38`, and the H¹ carrier API.
* `NlsGge.Atomic.G1.G1036`: `g36_s2a_fourierRepresentative_ftc` (FTC on `[0,1]`),
  `g36_s1b_fourierRepresentative_eq`, `g36_s1b_physical_sobolev_summable`,
  `g36_s1b_ae_real_phys`; `coverRep38_ae_phys`.
* `NlsGge.ThirdConsultation.M.M053Sup2`: `weakDerivative_eq_of_hasWeak` and, through its import
  of `NlsGge.Atomic.LIB.LIB006`, `LIB006.h1_mul_weakDeriv` and `LIB002`;
  `physicalSobolev_iff_ordinary`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open MeasureTheory NlsGge.Pilot

-- same proved local instance as G01H2/LIB006/ALSamplingV2Formula38 (a Prop class; no hypothesis)
local instance alProbL04 : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

section L04Helpers

open NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.GK38

/-- The canonical continuous representative is a representative of the carrier's `L²` class. -/
theorem l04_toLp_canon (u : SobolevHilbert 1) :
    ContinuousMap.toLp 2 spatialMeasure ℂ (physicalH1CanonicalContinuousRepresentativeCLM u) =
      physicalH1CarrierToL2AfterAcceptedCoordinate u :=
  physicalH1Continuous_toLp _ (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable u)

/-- Uniqueness of the literal weak derivative (all smooth periodic tests). -/
theorem l04_weak_unique {q w₁ w₂ : PhysicalL2}
    (h₁ : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 q w₁)
    (h₂ : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 q w₂) : w₁ = w₂ := by
  apply physicalFourierL2.injective
  apply Subtype.ext
  funext n
  change physicalFourierL2 w₁ n = physicalFourierL2 w₂ n
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  have e₁ : physicalFourier w₁ n =
      NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * physicalFourier q n :=
    (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := 1)).mp h₁ n
  have e₂ : physicalFourier w₂ n =
      NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * physicalFourier q n :=
    (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := 1)).mp h₂ n
  rw [e₁, e₂]

/-- (0) The carrier derivative class is the literal weak derivative of `u`. -/
theorem l04_deriv_weak (u : SobolevHilbert 1) :
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1
      (ContinuousMap.toLp 2 spatialMeasure ℂ (physicalH1CanonicalContinuousRepresentativeCLM u))
      (physicalH1DerivativeL2CLM u) := by
  rw [l04_toLp_canon]
  refine (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := 1)).mpr ?_
  intro n
  show physicalFourier (physicalH1DerivativeL2CLM u) n =
    NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 *
      physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate u) n
  rw [physicalH1DerivativeL2CLM_apply, physicalH1FourierDerivativeClass_fourier]
  simp [NlsGge.Atomic.LIB002.fourierMultiplier, NlsGge.Pilot.fourierMultiplier]

/-- The canonical representative is bounded. -/
theorem l04_canon_bdd (u : SobolevHilbert 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ.image
    (physicalH1CanonicalContinuousRepresentativeCLM u).continuous).isBounded.exists_norm_le
  refine ⟨max M 0, le_max_right _ _, fun y => le_trans (hM _ ⟨y, trivial, rfl⟩) (le_max_left _ _)⟩

/-- Real `L²` membership of `|u|²`. -/
theorem l04_normSq_memLp_real (u : SobolevHilbert 1) :
    MemLp (fun y : PhysicalCircle =>
      ‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 2) 2 spatialMeasure := by
  obtain ⟨M, hM0, hM⟩ := l04_canon_bdd u
  refine MemLp.of_bound
    (((physicalH1CanonicalContinuousRepresentativeCLM u).continuous.norm.pow 2).aestronglyMeasurable)
    (M ^ 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM y) 2

/-- Real `L²` membership of `2 Re(ū u')`. -/
theorem l04_dnormSq_memLp_real (u : SobolevHilbert 1) :
    MemLp (fun y : PhysicalCircle =>
      2 * ((starRingEnd ℂ) (physicalH1CanonicalContinuousRepresentativeCLM u y) *
        physicalH1DerivativeL2CLM u y).re) 2 spatialMeasure := by
  obtain ⟨M, hM0, hM⟩ := l04_canon_bdd u
  set f := physicalH1CanonicalContinuousRepresentativeCLM u
  set d : PhysicalL2 := physicalH1DerivativeL2CLM u
  have hdm : AEStronglyMeasurable (fun y : PhysicalCircle => d y) spatialMeasure :=
    (Lp.memLp d).aestronglyMeasurable
  refine MemLp.of_le_mul (c := 2 * M) (Lp.memLp d) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (Complex.continuous_re.comp_aestronglyMeasurable
      ((f.continuous.star.aestronglyMeasurable).mul hdm)).const_mul 2
  · have h1 := Complex.abs_re_le_norm ((starRingEnd ℂ) (f y) * d y)
    rw [norm_mul, Complex.norm_conj] at h1
    have h2 : ‖f y‖ * ‖d y‖ ≤ M * ‖d y‖ :=
      mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
    nlinarith [norm_nonneg (d y)]

/-- Transfer of a.e. equalities on the circle to the real line. -/
theorem l04_ae_real {p : PhysicalCircle → Prop} (h : ∀ᵐ y ∂spatialMeasure, p y) :
    ∀ᵐ t : ℝ, p (t : PhysicalCircle) :=
  g36_s1b_ae_real_phys h

/-- (3) The literal weak derivative of `|u|²` is `2 Re(ū u')` (from `LIB006.h1_mul_weakDeriv`). -/
theorem l04_normSq_hasWeak (u : SobolevHilbert 1)
    (hq : MemLp (fun y : PhysicalCircle =>
          ((‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 2 : ℝ) : ℂ)) 2 spatialMeasure)
    (hdq : MemLp (fun y : PhysicalCircle =>
          ((2 * ((starRingEnd ℂ) (physicalH1CanonicalContinuousRepresentativeCLM u y) *
            physicalH1DerivativeL2CLM u y).re : ℝ) : ℂ)) 2 spatialMeasure) :
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 (hq.toLp _) (hdq.toLp _) := by
  have hX := physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable u
  obtain ⟨C, -, H⟩ := NlsGge.Atomic.LIB006.h1_mul_weakDeriv
  obtain ⟨-, -, du, -, q, dq, hdu, -, -, -, hqdq, hqae, hdqae⟩ :=
    H (physicalH1CarrierToL2AfterAcceptedCoordinate u)
      (physicalH1CarrierToL2AfterAcceptedCoordinate u) hX hX
  have hd0 := l04_deriv_weak u
  rw [l04_toLp_canon] at hd0
  have hdu' : du = physicalH1DerivativeL2CLM u := l04_weak_unique hdu hd0
  have hXf : ((physicalH1CarrierToL2AfterAcceptedCoordinate u : PhysicalL2) :
      PhysicalCircle → ℂ) =ᵐ[spatialMeasure] physicalH1CanonicalContinuousRepresentativeCLM u := by
    have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
      (physicalH1CanonicalContinuousRepresentativeCLM u)
    rw [l04_toLp_canon] at h
    exact h
  have e1 : hq.toLp _ = q := by
    apply Lp.ext
    filter_upwards [hq.coeFn_toLp, hqae, hXf] with y h1 h2 h3
    rw [h1, h2]
    simp only [h3]
  have e2 : hdq.toLp _ = dq := by
    apply Lp.ext
    filter_upwards [hdq.coeFn_toLp, hdqae, hXf] with y h1 h2 h3
    rw [h1, h2, hdu']
    simp only [h3]
    rfl
  rw [e1, e2]
  exact hqdq

local instance alOpenPosL04 : spatialMeasure.IsOpenPosMeasure := by
  unfold spatialMeasure; infer_instance

/-- (1) on `[0,1]`: FTC for `|u|²` from `g36_s2a_fourierRepresentative_ftc`. -/
theorem l04_ftc01 (u : SobolevHilbert 1) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖alCanon38 u t‖ ^ 2 - ‖alCanon38 u 0‖ ^ 2 =
      ∫ s in (0 : ℝ)..t, 2 * ((starRingEnd ℂ) (alCanon38 u s) * alDeriv38 u s).re := by
  have hq : MemLp (fun y : PhysicalCircle =>
      ((‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 2 : ℝ) : ℂ)) 2 spatialMeasure :=
    (l04_normSq_memLp_real u).ofReal
  have hdq : MemLp (fun y : PhysicalCircle =>
      ((2 * ((starRingEnd ℂ) (physicalH1CanonicalContinuousRepresentativeCLM u y) *
        physicalH1DerivativeL2CLM u y).re : ℝ) : ℂ)) 2 spatialMeasure :=
    (l04_dnormSq_memLp_real u).ofReal
  have hW := l04_normSq_hasWeak u hq hdq
  have hQS : physicalSobolev 1 (hq.toLp _) :=
    (physicalSobolev_iff_ordinary 1 _).2
      ((NlsGge.Atomic.LIB004.h1_iff_weak_derivative _).2 ⟨_, hW⟩)
  have hwD := NlsGge.ThirdConsultation.M.weakDerivative_eq_of_hasWeak _ _ hQS hW
  have hftc := g36_s2a_fourierRepresentative_ftc _ hQS t ht
  rw [g36_s1b_fourierRepresentative_eq _ hQS t, g36_s1b_fourierRepresentative_eq _ hQS 0,
    hwD] at hftc
  let Fc : C(PhysicalCircle, ℂ) :=
    ⟨fun y => ((‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 2 : ℝ) : ℂ),
      Complex.continuous_ofReal.comp
        ((physicalH1CanonicalContinuousRepresentativeCLM u).continuous.norm.pow 2)⟩
  have hcont : physicalH1Continuous (hq.toLp _) (g36_s1b_physical_sobolev_summable _ hQS) = Fc := by
    have hae : ((physicalH1Continuous (hq.toLp _) (g36_s1b_physical_sobolev_summable _ hQS) :
        C(PhysicalCircle, ℂ)) : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (Fc : PhysicalCircle → ℂ) := by
      have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
        (physicalH1Continuous (hq.toLp _) (g36_s1b_physical_sobolev_summable _ hQS))
      rw [physicalH1Continuous_toLp] at h
      filter_upwards [h, hq.coeFn_toLp] with y h1 h2
      rw [← h1, h2]
      rfl
    exact ContinuousMap.coe_injective
      ((Continuous.ae_eq_iff_eq spatialMeasure (ContinuousMap.continuous _) Fc.continuous).1 hae)
  rw [hcont] at hftc
  have hint : (∫ s in (0 : ℝ)..t, coverRep38 (hdq.toLp _) s) =
      ∫ s in (0 : ℝ)..t,
        (((2 * ((starRingEnd ℂ) (alCanon38 u s) * alDeriv38 u s).re : ℝ)) : ℂ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [coverRep38_ae_phys (hdq.toLp _), l04_ae_real hdq.coeFn_toLp] with s h1 h2 _
    rw [h1, h2]
    rfl
  rw [hint, intervalIntegral.integral_ofReal] at hftc
  have e : (((‖alCanon38 u t‖ ^ 2 - ‖alCanon38 u 0‖ ^ 2 : ℝ)) : ℂ) =
      ((∫ s in (0 : ℝ)..t, 2 * ((starRingEnd ℂ) (alCanon38 u s) * alDeriv38 u s).re : ℝ) : ℂ) := by
    rw [← hftc, Complex.ofReal_sub]
    rfl
  exact_mod_cast e

/-- (1) on every real interval: periodic extension of `l04_ftc01`. -/
theorem l04_ftc (u : SobolevHilbert 1) (a b : ℝ) :
    IntervalIntegrable
        (fun t : ℝ => 2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) volume a b ∧
      ‖alCanon38 u b‖ ^ 2 - ‖alCanon38 u a‖ ^ 2 =
        ∫ t in a..b, 2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re := by
  set g : ℝ → ℝ := fun t => 2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re with hg
  have hc : ∀ t : ℝ, ((t + 1 : ℝ) : PhysicalCircle) = (t : PhysicalCircle) := fun t => by
    simp
  have hgp : Function.Periodic g 1 := fun t => by
    simp only [hg, alCanon38, alDeriv38, hc]
  have hg01 : IntervalIntegrable g volume 0 1 :=
    alLiftInt38 (fun y : PhysicalCircle =>
      2 * ((starRingEnd ℂ) (physicalH1CanonicalContinuousRepresentativeCLM u y) *
        physicalH1DerivativeL2CLM u y).re)
      ((l04_dnormSq_memLp_real u).integrable one_le_two)
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hgp.intervalIntegrable one_ne_zero (t := 0) (by simpa using hg01) a b
  set F : ℝ → ℝ := fun t => ‖alCanon38 u t‖ ^ 2 with hF
  have hFp : Function.Periodic F 1 := fun t => by
    simp only [hF, alCanon38, hc]
  set G : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hG
  have h1z : ∫ s in (0 : ℝ)..1, g s = 0 := by
    rw [← l04_ftc01 u 1 ⟨zero_le_one, le_rfl⟩]
    have h10 : ((1 : ℝ) : PhysicalCircle) = ((0 : ℝ) : PhysicalCircle) := by
      simp
    simp only [alCanon38, h10, sub_self]
  have hGp : Function.Periodic G 1 := fun t => by
    simp only [hG]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi 0 t) (hgi t (t + 1)),
      hgp.intervalIntegral_add_eq t 0, zero_add, h1z, add_zero]
  set H : ℝ → ℝ := fun t => F t - F 0 - G t with hH
  have hHp : Function.Periodic H 1 := fun t => by
    simp only [hH]
    rw [hFp t, hGp t]
  have hH01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, H t = 0 := fun t ht => by
    simp only [hH, hF, hG]
    rw [l04_ftc01 u t ht, sub_self]
  have hH0 : ∀ t : ℝ, H t = 0 := fun t => by
    rw [← hHp.sub_int_mul_eq (n := ⌊t⌋), mul_one]
    apply hH01
    exact ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  refine ⟨hgi a b, ?_⟩
  have ha := hH0 a
  have hb := hH0 b
  simp only [hH, hF, hG] at ha hb
  rw [← intervalIntegral.integral_interval_sub_left (hgi 0 b) (hgi 0 a)]
  linarith

end L04Helpers

/-- B086.C01 (paper/v2.tex 2028-2033, `C:eq:V2positive`) on EVERY genuine `H¹` field. -/
theorem alNormSq_weakDeriv_V2_38 (β₁ β₂ : ℝ) (u : SobolevHilbert 1) :
    -- (0) `u'` is the literal weak derivative of `u` (project notion, all smooth periodic tests)
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1
      (ContinuousMap.toLp 2 spatialMeasure ℂ (physicalH1CanonicalContinuousRepresentativeCLM u))
      (physicalH1DerivativeL2CLM u) ∧
    -- (1) absolute continuity / W^{1,1}: FTC for the continuous `|u|²` on every interval
    (∀ a b : ℝ,
      IntervalIntegrable
        (fun t : ℝ => 2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) volume a b ∧
      ‖alCanon38 u b‖ ^ 2 - ‖alCanon38 u a‖ ^ 2 =
        ∫ t in a..b, 2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) ∧
    -- (2) `|u|²` and `2 Re(ū u')` are square integrable on the circle
    MemLp (fun y : PhysicalCircle =>
      ((‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 2 : ℝ) : ℂ)) 2 spatialMeasure ∧
    MemLp (fun y : PhysicalCircle =>
      ((2 * ((starRingEnd ℂ) (physicalH1CanonicalContinuousRepresentativeCLM u y) *
        physicalH1DerivativeL2CLM u y).re : ℝ) : ℂ)) 2 spatialMeasure ∧
    ∀ (hq : MemLp (fun y : PhysicalCircle =>
          ((‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 2 : ℝ) : ℂ)) 2 spatialMeasure)
      (hdq : MemLp (fun y : PhysicalCircle =>
          ((2 * ((starRingEnd ℂ) (physicalH1CanonicalContinuousRepresentativeCLM u y) *
            physicalH1DerivativeL2CLM u y).re : ℝ) : ℂ)) 2 spatialMeasure),
      -- (3) literal weak-derivative statement: (|u|²)' = 2 Re(ū u')
      NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 (hq.toLp _) (hdq.toLp _) ∧
      -- (4) for EVERY weak derivative `w` of `|u|²` (the source's `(|u|²)'`): uniqueness and
      --     the exact integrable V2 formula with `((|u|²)')²` written literally as `(w t)²`
      ∀ w : PhysicalL2, NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 (hq.toLp _) w →
        (w : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (hdq.toLp _ : PhysicalCircle → ℂ) ∧
        IntervalIntegrable (fun t : ℝ => 2 * ‖alCanon38 u t‖ ^ 6
            + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
            + ((w : PhysicalCircle → ℂ) (t : PhysicalCircle)).re ^ 2) volume 0 1 ∧
        alV2_38 β₁ β₂ u =
          β₁ * (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4)
          + β₂ * (∫ t in (0 : ℝ)..1, (2 * ‖alCanon38 u t‖ ^ 6
            + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
            + ((w : PhysicalCircle → ℂ) (t : PhysicalCircle)).re ^ 2)) := by

  refine ⟨l04_deriv_weak u, fun a b => l04_ftc u a b, (l04_normSq_memLp_real u).ofReal,
    (l04_dnormSq_memLp_real u).ofReal, ?_⟩
  intro hq hdq
  have hW := l04_normSq_hasWeak u hq hdq
  refine ⟨hW, ?_⟩
  intro w hw
  have hwe : w = hdq.toLp _ := l04_weak_unique hw hW
  rw [hwe]
  obtain ⟨-, hI, hV⟩ := alV2_eq_integral38 β₁ β₂ u
  have hae : ∀ᵐ t : ℝ, (2 * ‖alCanon38 u t‖ ^ 6
        + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
        + (2 * ((starRingEnd ℂ) (alCanon38 u t) * alDeriv38 u t).re) ^ 2) =
      (2 * ‖alCanon38 u t‖ ^ 6
        + 6 * ‖alCanon38 u t‖ ^ 2 * ‖alDeriv38 u t‖ ^ 2
        + ((hdq.toLp _ : PhysicalCircle → ℂ) (t : PhysicalCircle)).re ^ 2) := by
    filter_upwards [l04_ae_real hdq.coeFn_toLp] with t ht
    rw [ht]
    rfl
  refine ⟨Filter.EventuallyEq.rfl, intervalIntegrable_iff.2
    (Integrable.congr (intervalIntegrable_iff.1 hI) (ae_restrict_of_ae hae)), ?_⟩
  rw [hV, intervalIntegral.integral_congr_ae (hae.mono fun t ht _ => ht)]

end NlsGge.AblowitzLadik
