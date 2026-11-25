import NlsGge.Schur.ActualSchurShiftedRoots38V1

/-!
# Radius independence of `σ_n`, `q_n`; canonical versions; F:eq:gaplocal

* Review note N2: the radius-indexed center and coordinate agree for any two
  admissible radii; canonical radius-free versions are defined and agree with
  every admissible indexed version.
* F:eq:gaplocal (source line 1142): the real Schur roots `λ^±` (zeros of
  `F ∓ |b_n|`) satisfy `|λ^± - nπ| ≤ C R^3/|n|`.  Their identification with the
  labelled periodic eigenvalues remains open (F03.07/E02).
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

theorem actualSchurCenter38_radius_indep
    (R R' : ℝ) (hR : 1 ≤ R) (hR' : 1 ≤ R') (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (hthr' : actualSchurCenterThresholdConstant38 * R' ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) (hp₁' : ‖p.1‖ ≤ R') (hp₂' : ‖p.2‖ ≤ R') :
    actualSchurCenter38 R n p = actualSchurCenter38 R' n p := by
  obtain ⟨hb, hfix⟩ := actualSchurCenter38_spec R hR n hthr p hp₁ hp₂
  exact (actualSchurCenter38_eq_of_fixed R' hR' n hthr' p hp₁' hp₂' _ hb hfix).symm

/-- The canonical admissible radius `max 1 (max ‖p.1‖ ‖p.2‖)`. -/
def actualSchurCanonicalRadius38 (p : ActualSchurEffectiveH1PairV3_30) : ℝ :=
  max 1 (max ‖p.1‖ ‖p.2‖)

/-- Radius-free moving center. -/
def actualSchurCenterCanonical38 (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) : ℂ :=
  actualSchurCenter38 (actualSchurCanonicalRadius38 p) n p

/-- Radius-free version of the auxiliary coordinate `q_n(p) = b_n(σ_n(p); p)`.  "Canonical" here
means ONLY that the radius parameter has been removed (it agrees with every admissible
radius-indexed `actualSchurQn38`); `q_n` is NOT a canonical (symplectic/Birkhoff) coordinate. -/
def actualSchurQnCanonical38 (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) : ℂ :=
  actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
    (actualSchurCenterCanonical38 n p, p)

theorem actualSchurCenterCanonical38_eq
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    actualSchurCenterCanonical38 n p = actualSchurCenter38 R n p := by
  have hK : 0 ≤ actualSchurCenterThresholdConstant38 :=
    (actualSchurShiftedRootsConstant38_ge).2.2.2
  set R0 := actualSchurCanonicalRadius38 p with hR0
  have hR01 : 1 ≤ R0 := le_max_left _ _
  have hR0R : R0 ≤ R := max_le hR (max_le hp₁ hp₂)
  have hp₁0 : ‖p.1‖ ≤ R0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hp₂0 : ‖p.2‖ ≤ R0 := le_trans (le_max_right _ _) (le_max_right _ _)
  have hthr0 : actualSchurCenterThresholdConstant38 * R0 ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_trans zero_le_one hR01) hR0R 3) hK) hthr
  exact actualSchurCenter38_radius_indep R0 R hR01 hR n hthr0 hthr p hp₁0 hp₂0 hp₁ hp₂

theorem actualSchurQnCanonical38_eq
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    actualSchurQnCanonical38 n p = actualSchurQn38 R n p := by
  unfold actualSchurQnCanonical38 actualSchurQn38
  rw [actualSchurCenterCanonical38_eq R hR n hthr p hp₁ hp₂]

/-- Absolute constant of F:eq:gaplocal. -/
def actualSchurGapLocalConstant38 : ℝ :=
  2 * freeResolventSchurUniformConstant * freeResolventComplementaryInverseUniformConstant22 *
    physicalH1MultiplierConstant + 1 + actualSchurBremConstant38

/-- F:eq:gaplocal for both real Schur roots: any real `λ` in
`[nπ - 1/2, nπ + 1/2]` with `F(λ) = ±|b_n(λ)|` satisfies `|λ - nπ| ≤ C R^3/|n|`. -/
theorem actualSchurRoot_gapLocal38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (l : ℝ) (hl : l ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hroot : l - Real.pi * n - (actualSchurAlpha38 n p l).re -
        ‖actualSchurCoefficientAfterDext31 n
          (true, resonantIndex n) (false, resonantIndex n) ((l : ℂ), p)‖ = 0 ∨
      l - Real.pi * n - (actualSchurAlpha38 n p l).re +
        ‖actualSchurCoefficientAfterDext31 n
          (true, resonantIndex n) (false, resonantIndex n) ((l : ℂ), p)‖ = 0) :
    |l - Real.pi * n| ≤ actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| := by
  obtain ⟨hKge, hB0, hK3, hT0⟩ := actualSchurShiftedRootsConstant38_ge
  have hthrC : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge (by positivity)) hthr
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthrC
  have hdisk : ((l : ℂ)) ∈ spectralDisk n := by
    change ‖(l : ℂ) - spectralCenter n‖ ≤ 1
    have he : (l : ℂ) - spectralCenter n = ((l - Real.pi * n : ℝ) : ℂ) := by
      simp [spectralCenter]; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := hl
    constructor <;> linarith
  set N := |(n : ℝ)| with hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hn
  have hα := actualSchurAlpha_boundAfterDextV6_32 R hR n hn hlarge (l : ℂ) p hdisk hp₁ hp₂
  have hb := actualSchurOffDiagonal_sub_fourier_bound38V1 R hR n hn hlarge (l : ℂ) p hdisk hp₁ hp₂
  rw [physicalH1ComplexCarrierToL2Actual22_fourier] at hb
  have hun : N * ‖p.1 n‖ ≤ ‖p.1‖ := weightedH1_fourier_norm_le38V1 p.1 n
  have hun' : ‖p.1 n‖ ≤ R / N := by
    rw [le_div_iff₀ hNpos]; nlinarith
  set b := actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (false, resonantIndex n) ((l : ℂ), p) with hbdef
  have hbnorm : ‖b‖ ≤ R / N + actualSchurBremConstant38 * R ^ 4 / N ^ 2 := by
    have h1 : ‖b‖ ≤ ‖b - p.1 n‖ + ‖p.1 n‖ := by
      have := norm_add_le (b - p.1 n) (p.1 n)
      simpa using this
    unfold actualSchurBremConstant38
    linarith
  have hαre : |(actualSchurAlpha38 n p l).re| ≤
      2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 3 / N :=
    le_trans (Complex.abs_re_le_norm _) hα
  -- comparison of scales: R/N ≤ R^3/N and R^4/N^2 ≤ R^3/N
  have hR3 : R ≤ R ^ 3 := by nlinarith [sq_nonneg R, sq_nonneg (R - 1)]
  have hRN : R ≤ N := by
    have : 3 * R ^ 3 ≤ N := le_trans (mul_le_mul_of_nonneg_right hK3 (by positivity)) hthr
    nlinarith
  have hs1 : R / N ≤ R ^ 3 / N := div_le_div_of_nonneg_right hR3 hNpos.le
  have hs2 : R ^ 4 / N ^ 2 ≤ R ^ 3 / N := by
    rw [div_le_div_iff₀ (by positivity) hNpos]
    have : R ^ 4 * N = R ^ 3 * (R * N) := by ring
    have h' : R ^ 3 * N ^ 2 = R ^ 3 * (N * N) := by ring
    rw [this, h']
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRN hNpos.le) (by positivity)
  have hbnorm' : ‖b‖ ≤ (1 + actualSchurBremConstant38) * (R ^ 3 / N) := by
    have : actualSchurBremConstant38 * R ^ 4 / N ^ 2 =
        actualSchurBremConstant38 * (R ^ 4 / N ^ 2) := by ring
    rw [this] at hbnorm
    nlinarith [mul_le_mul_of_nonneg_left hs2 hB0]
  have hαre' : |(actualSchurAlpha38 n p l).re| ≤
      (2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant) * (R ^ 3 / N) := by
    have : 2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 3 / N =
        (2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant) * (R ^ 3 / N) := by ring
    rw [this] at hαre
    exact hαre
  have hgoal : actualSchurGapLocalConstant38 * R ^ 3 / N =
      (2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant) * (R ^ 3 / N) +
      (1 + actualSchurBremConstant38) * (R ^ 3 / N) := by
    unfold actualSchurGapLocalConstant38; ring
  rw [hgoal]
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
  rw [abs_le] at hαre' ⊢
  rcases hroot with h | h <;> constructor <;> linarith [hαre'.1, hαre'.2]

end NlsGge.Schur
