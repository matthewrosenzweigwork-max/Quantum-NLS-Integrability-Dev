import NlsGge.Schur.ActualSchurEntryDerivative38V1
import NlsGge.Schur.GapCenterComparison38V1

/-!
# Actual instantiation of the monotone gap comparison (NEW-F03.08)

Source: `paper/v2.tex` lines 1158-1168.  On the real segment
`[nπ - 1/2, nπ + 1/2]` put `F(λ) = λ - nπ - Re α_n(λ)` and `β(λ) = |b_n(λ)|`,
with the ACTUAL Schur coefficients.  With `d_n = C R^4/n^2 ≤ 1/4`
(checked Green-product constant), any real solution `σ` of the actual center
equation and any real zeros `λ⁺` of `F - β` and `λ⁻` of `F + β` in the segment
satisfy `λ⁻ ≤ σ ≤ λ⁺` and `λ⁺ - λ⁻ ≥ 2 |b_n(σ)| / (1 + 2 d_n)`.

Formulation note: the source writes `F = λ - nπ - α_n(λ)` using that `α_n` is
real for real-type potentials and real `λ`; here `Re α_n` is used so that the
statement holds for every pair, and coincides with the source on the real
subspace once reality is proved.  The identification of `λ^±` with the labelled
periodic eigenvalues (F03.07) is NOT part of this theorem.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The derivative-size parameter `d_n = C R^4 / n^2` of the source. -/
def actualSchurGapParameter38 (R : ℝ) (n : ℤ) : ℝ :=
  freeResolventComplementaryInverseUniformConstant22 ^ 2 *
    freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2

theorem actualSchurGapComparison38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (σ lm lp : ℝ)
    (hσI : σ ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlmI : lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlpI : lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hσ : (σ : ℂ) = spectralCenter n + actualSchurAlpha38 n p σ)
    (hlp : lp - Real.pi * n - (actualSchurAlpha38 n p lp).re -
      ‖actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) ((lp : ℂ), p)‖ = 0)
    (hlm : lm - Real.pi * n - (actualSchurAlpha38 n p lm).re +
      ‖actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) ((lm : ℂ), p)‖ = 0) :
    lm ≤ σ ∧ σ ≤ lp ∧
      2 * ‖actualSchurCoefficientAfterDext31 n
          (true, resonantIndex n) (false, resonantIndex n) ((σ : ℂ), p)‖ /
        (1 + 2 * actualSchurGapParameter38 R n) ≤ lp - lm := by
  obtain ⟨hn, hlarge, -, h14⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  set d := actualSchurGapParameter38 R n with hd
  have hd14 : d ≤ 1 / 4 := h14
  have hd0 : 0 ≤ d := by
    have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
      freeResolventComplementaryInverseUniformConstant22_posV2_31
    rw [hd, actualSchurGapParameter38]
    positivity
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
  have hβ0 : ∀ x ∈ Set.Icc a b, 0 ≤ β x := fun x _ => norm_nonneg _
  have hFσ : F σ = 0 := by
    have h := congrArg Complex.re hσ
    simp only [Complex.ofReal_re, Complex.add_re, spectralCenter] at h
    simp only [F]
    have hc : ((n : ℂ) * (Real.pi : ℂ)).re = Real.pi * n := by
      simp [Complex.mul_re]
      ring
    rw [hc] at h
    linarith
  obtain ⟨h1, h2, -, -, h5⟩ := gapCenter_comparison38V1 a b d σ lm lp F β
    hd0 hd14 hσI hlmI hlpI hFinc hFlip hβlip hβ0 hFσ hlp hlm
  exact ⟨h1, h2, h5⟩

end NlsGge.Schur
