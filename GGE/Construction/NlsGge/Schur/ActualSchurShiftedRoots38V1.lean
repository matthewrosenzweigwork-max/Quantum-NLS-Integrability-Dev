import NlsGge.Schur.ActualSchurGapComparisonRealization38V1
import NlsGge.Schur.ActualSchurQnCauchy38V1

/-!
# Existence and uniqueness of the shifted roots `λ_n^±` (NEW-F03.08, first part)

Source: `paper/v2.tex` lines 1158-1162.  On the real segment
`I = [nπ - 1/2, nπ + 1/2]` put `F(λ) = λ - nπ - Re α_n(λ)` and
`β(λ) = |b_n(λ)|` for the ACTUAL Schur coefficients.  After enlarging the
absolute constant to `actualSchurShiftedRootsConstant38`, the functions
`F - β` and `F + β` each have exactly one zero in `I`.

Formulation note: as in `actualSchurGapComparison38V1`, `Re α_n` replaces the
source's `α_n` (which is real for real-type potentials and real `λ`).  The
identification of the two zeros with the labelled periodic eigenvalues
`λ_n^±` is NOT part of this theorem.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- Absolute constant (independent of `R`, `n`, `p`) for the shifted-root
threshold `|n| ≥ K R^3`: the center threshold plus `3 (1 + C_brem)`. -/
def actualSchurShiftedRootsConstant38 : ℝ :=
  actualSchurCenterThresholdConstant38 + 3 * (1 + actualSchurBremConstant38)

/-- A single Fourier mode of an `H¹` element is at most `‖x‖/|n|`. -/
theorem weightedH1_fourier_norm_le38V1
    (x : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (n : ℤ) :
    |(n : ℝ)| * ‖x n‖ ≤ ‖x‖ := by
  have h := weightedHilbert_hasSum (sobolevModeWeight (1 : ℝ)) x
  have hle := le_hasSum h n (fun j _ => mul_nonneg ((sobolevModeWeightPositive (1 : ℝ)).out j).le (sq_nonneg _))
  have hw : sobolevModeWeight (1 : ℝ) n = 1 + (n : ℝ) ^ 2 := by
    unfold sobolevModeWeight
    exact japaneseBracket_h1_weight n
  rw [hw] at hle
  have hsq : (|(n : ℝ)| * ‖x n‖) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg ‖x n‖]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 hsq

/-- A function that is `d`-Lipschitz (in the `|·|` sense) on a set is
continuous there. -/
theorem continuousOn_of_abs_sub_le38V1 (g : ℝ → ℝ) (s : Set ℝ) (d : ℝ)
    (h : ∀ x ∈ s, ∀ y ∈ s, |g y - g x| ≤ d * |y - x|) : ContinuousOn g s := by
  have hl : LipschitzOnWith (Real.toNNReal d) g s := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have := h y hy x hx
    rw [Real.dist_eq, Real.dist_eq]
    have hd : (Real.toNNReal d : ℝ) = max d 0 := rfl
    rw [hd]
    exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  exact hl.continuousOn

theorem actualSchurShiftedRootsConstant38_ge :
    actualSchurCenterThresholdConstant38 ≤ actualSchurShiftedRootsConstant38 ∧
      0 ≤ actualSchurBremConstant38 ∧ 3 ≤ actualSchurShiftedRootsConstant38 ∧
      0 ≤ actualSchurCenterThresholdConstant38 := by
  have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hM : 0 < physicalH1MultiplierConstant := physicalH1MultiplierConstant_pos
  have hB : 0 ≤ actualSchurBremConstant38 := by
    unfold actualSchurBremConstant38 freeResolventSchurUniformConstant
    positivity
  have hT : 0 ≤ actualSchurCenterThresholdConstant38 := by
    unfold actualSchurCenterThresholdConstant38 freeResolventSchurUniformConstant
    positivity
  unfold actualSchurShiftedRootsConstant38
  refine ⟨by linarith, hB, by linarith, hT⟩

theorem actualSchurShiftedRoots38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    (∃! lp : ℝ, lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
      lp - Real.pi * n - (actualSchurAlpha38 n p lp).re -
        ‖actualSchurCoefficientAfterDext31 n
          (true, resonantIndex n) (false, resonantIndex n) ((lp : ℂ), p)‖ = 0) ∧
    (∃! lm : ℝ, lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
      lm - Real.pi * n - (actualSchurAlpha38 n p lm).re +
        ‖actualSchurCoefficientAfterDext31 n
          (true, resonantIndex n) (false, resonantIndex n) ((lm : ℂ), p)‖ = 0) := by
  obtain ⟨hKge, hB, hK3, hT⟩ := actualSchurShiftedRootsConstant38_ge
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR3 : 0 ≤ R ^ 3 := by positivity
  have hthr0 : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge hR3) hthr
  obtain ⟨hn, hlarge, h18, h14⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr0
  have hd0 : 0 ≤ actualSchurGapParameter38 R n := by
    have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
      freeResolventComplementaryInverseUniformConstant22_posV2_31
    rw [actualSchurGapParameter38]
    positivity
  set d := actualSchurGapParameter38 R n with hd
  have hd14 : d ≤ 1 / 4 := h14
  set K := actualSchurShiftedRootsConstant38 with hK
  have hKM : 3 * (1 + actualSchurBremConstant38) ≤ K := by
    rw [hK]; unfold actualSchurShiftedRootsConstant38; linarith
  set M := actualSchurBremConstant38 with hM
  set N := |(n : ℝ)| with hN
  have hN1 : 1 ≤ N := hn
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hKpos : 0 < K := by linarith
  -- elementary size bounds: `R/N ≤ 1/K` and `R^4/N^2 ≤ 1/K`
  have hR3R : R ≤ R ^ 3 := by nlinarith [sq_nonneg R, sq_nonneg (R - 1)]
  have hRN : R / N ≤ 1 / K := by
    rw [div_le_div_iff₀ hNpos hKpos]
    nlinarith
  have hR4N : R ^ 4 / N ^ 2 ≤ 1 / K := by
    rw [div_le_div_iff₀ (by positivity) hKpos]
    have h1 : K * R ^ 3 ≤ N := hthr
    have h2 : (K * R ^ 3) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : R ^ 4 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left h3 hKpos.le]
  have hsmall : (1 + M) / K ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hKpos (by norm_num)]
    linarith
  let a : ℝ := Real.pi * n - 1 / 2
  let b : ℝ := Real.pi * n + 1 / 2
  let F : ℝ → ℝ := fun x => x - Real.pi * n - (actualSchurAlpha38 n p x).re
  let β : ℝ → ℝ := fun x => ‖actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (false, resonantIndex n) ((x : ℂ), p)‖
  have hdisk : ∀ x ∈ Set.Icc a b, ((x : ℂ)) ∈ spectralDisk n := by
    intro x hx
    change ‖(x : ℂ) - spectralCenter n‖ ≤ 1
    have he : (x : ℂ) - spectralCenter n = ((x - Real.pi * n : ℝ) : ℂ) := by
      simp [spectralCenter]
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := hx
    change Real.pi * n - 1 / 2 ≤ x at h1
    change x ≤ Real.pi * n + 1 / 2 at h2
    constructor <;> linarith
  have hlipα : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      ‖actualSchurAlpha38 n p y - actualSchurAlpha38 n p x‖ ≤ d * |y - x| := by
    intro x hx y hy
    have h := actualSchurEntry_lipschitz38V1 R hR n hn hlarge
      (true, resonantIndex n) (true, resonantIndex n) p hp₁ hp₂
      (y : ℂ) (x : ℂ) (hdisk y hy) (hdisk x hx)
    have hn' : ‖(y : ℂ) - (x : ℂ)‖ = |y - x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn'] at h
    exact h
  have hre : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |(actualSchurAlpha38 n p y).re - (actualSchurAlpha38 n p x).re| ≤
        d * |y - x| := by
    intro x hx y hy
    rw [← Complex.sub_re]
    exact le_trans (Complex.abs_re_le_norm _) (hlipα x hx y hy)
  have hFinc : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      (1 - d) * (y - x) ≤ F y - F x := by
    intro x hx y hy hxy
    have h := hre x hx y hy
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at h
    have h' := (abs_le.mp h).2
    simp only [F]
    nlinarith
  have hFlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      F y - F x ≤ (1 + d) * (y - x) := by
    intro x hx y hy hxy
    have h := hre x hx y hy
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at h
    have h' := (abs_le.mp h).1
    simp only [F]
    nlinarith
  have hβlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |β y - β x| ≤ d * |y - x| := by
    intro x hx y hy
    have h := actualSchurEntry_lipschitz38V1 R hR n hn hlarge
      (true, resonantIndex n) (false, resonantIndex n) p hp₁ hp₂
      (y : ℂ) (x : ℂ) (hdisk y hy) (hdisk x hx)
    have hn' : ‖(y : ℂ) - (x : ℂ)‖ = |y - x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn'] at h
    exact le_trans (abs_norm_sub_norm_le _ _) h
  -- size of `β` on the segment
  have hFourier : ‖p.1 n‖ ≤ R / N := by
    rw [le_div_iff₀ hNpos]
    have := weightedH1_fourier_norm_le38V1 p.1 n
    nlinarith [norm_nonneg (p.1 n)]
  have hβsmall : ∀ x ∈ Set.Icc a b, β x ≤ 1 / 3 := by
    intro x hx
    have h := actualSchurOffDiagonal_sub_fourier_bound38V1 R hR n hn hlarge
      (x : ℂ) p (hdisk x hx) hp₁ hp₂
    rw [physicalH1ComplexCarrierToL2Actual22_fourier] at h
    have h' : ‖actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) ((x : ℂ), p) - p.1 n‖ ≤
        M * R ^ 4 / N ^ 2 := by
      rw [hM]; unfold actualSchurBremConstant38; exact h
    have h2 := norm_sub_norm_le (actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) ((x : ℂ), p)) (p.1 n)
    have h3 : M * R ^ 4 / N ^ 2 ≤ M * (1 / K) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hR4N hB
    have h4 : M * (1 / K) + 1 / K = (1 + M) / K := by ring
    show ‖actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) ((x : ℂ), p)‖ ≤ 1 / 3
    linarith
  have hαsmall : ∀ x ∈ Set.Icc a b, |(actualSchurAlpha38 n p x).re| ≤ 1 / 8 := by
    intro x hx
    have h := actualSchurAlpha_boundAfterDextV6_32 R hR n hn hlarge (x : ℂ) p
      (hdisk x hx) hp₁ hp₂
    exact le_trans (Complex.abs_re_le_norm _) (le_trans h h18)
  have hab : a ≤ b := by simp only [a, b]; linarith
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hFa : F a ≤ -(3 / 8) := by
    have := (abs_le.mp (hαsmall a haI)).1
    simp only [F, a]; linarith
  have hFb : 3 / 8 ≤ F b := by
    have := (abs_le.mp (hαsmall b hbI)).2
    simp only [F, b]; linarith
  have hcα : ContinuousOn (fun x : ℝ => (actualSchurAlpha38 n p x).re) (Set.Icc a b) :=
    continuousOn_of_abs_sub_le38V1 _ _ d hre
  have hcβ : ContinuousOn β (Set.Icc a b) :=
    continuousOn_of_abs_sub_le38V1 _ _ d hβlip
  have hcF : ContinuousOn F (Set.Icc a b) :=
    (continuousOn_id.sub continuousOn_const).sub hcα
  obtain ⟨hmonoM, hmonoP⟩ := gapCenter_shifted_strictMonoOn38V1 a b d F β hd0 hd14
    hFinc hβlip
  have hβ0 : ∀ x, 0 ≤ β x := fun x => norm_nonneg _
  have hβa := hβsmall a haI
  have hβb := hβsmall b hbI
  have hβa0 := hβ0 a
  have hβb0 := hβ0 b
  constructor
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hab (hcF.sub hcβ)
      (show (0 : ℝ) ∈ Set.Icc (F a - β a) (F b - β b) from ⟨by linarith, by linarith⟩)
    refine ⟨x, ⟨hx, ?_⟩, fun y hy => ?_⟩
    · exact hx0
    · exact hmonoM.injOn hy.1 hx (hy.2.trans hx0.symm)
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hab (hcF.add hcβ)
      (show (0 : ℝ) ∈ Set.Icc (F a + β a) (F b + β b) from ⟨by linarith, by linarith⟩)
    refine ⟨x, ⟨hx, ?_⟩, fun y hy => ?_⟩
    · exact hx0
    · exact hmonoP.injOn hy.1 hx (hy.2.trans hx0.symm)

end NlsGge.Schur
