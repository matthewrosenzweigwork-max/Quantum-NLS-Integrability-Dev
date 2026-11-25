import Mathlib
import NlsGge.Schur.GapCenterComparison38V1
import NlsGge.Schur.ActualSchurGapComparisonRealization38V1
import NlsGge.Schur.ActualSchurCenterContraction38V1
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                                                                                                                  
                                                                                                                                                                                                 
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem effectiveRoot_strictMono :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (n : ℤ),
      K * R ^ 3 ≤ |(n : ℝ)| → ∀ (w : SchurH1), ‖w‖ ≤ R →
      let I := Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2)
      let F := scalarRootAt n w
      let B := fun r : ℝ => ‖bAt n r (schurRealPair w)‖
      let d := gapParameter R n
      d ≤ (1 / 4 : ℝ) ∧
      (∀ x ∈ I, ∀ y ∈ I, x < y →
        (1 - 2 * d) * (y - x) ≤ (F y + B y) - (F x + B x) ∧
        (1 - 2 * d) * (y - x) ≤ (F y - B y) - (F x - B x)) ∧
      StrictMonoOn (fun r => F r + B r) I ∧ StrictMonoOn (fun r => F r - B r) I := by
  refine ⟨max actualSchurCenterThresholdConstant38 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro R hR n hKn w hwR
  have hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| := by
    have h1 : actualSchurCenterThresholdConstant38 ≤ max actualSchurCenterThresholdConstant38 1 :=
      le_max_left _ _
    have h3 : 0 ≤ R ^ 3 := by positivity
    have h4 := mul_le_mul_of_nonneg_right h1 h3
    linarith
  obtain ⟨hn, hlarge, -, h14⟩ := actualSchurCenterThresholdConstant38_consequences R hR n hthr
  have hd14 : gapParameter R n ≤ 1 / 4 := h14
  have hd0 : 0 ≤ gapParameter R n := by
    unfold gapParameter actualSchurGapParameter38
    positivity
  have hp₁ : ‖(schurRealPair w).1‖ ≤ R := hwR
  have hp₂ : ‖(schurRealPair w).2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]
    exact hwR
  have hdisk : ∀ x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      ((x : ℝ) : ℂ) ∈ spectralDisk n := by
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
  have hlipα : ∀ x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      ∀ y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      ‖actualSchurAlpha38 n (schurRealPair w) y - actualSchurAlpha38 n (schurRealPair w) x‖ ≤
        gapParameter R n * |y - x| := by
    intro x hx y hy
    have h := actualSchurEntry_lipschitz38V1 R hR n hn hlarge
      (true, resonantIndex n) (true, resonantIndex n) (schurRealPair w) hp₁ hp₂
      (y : ℂ) (x : ℂ) (hdisk y hy) (hdisk x hx)
    have hn' : ‖(y : ℂ) - (x : ℂ)‖ = |y - x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn'] at h
    exact h
  have hre : ∀ x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      ∀ y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      |(actualSchurAlpha38 n (schurRealPair w) y).re -
          (actualSchurAlpha38 n (schurRealPair w) x).re| ≤ gapParameter R n * |y - x| := by
    intro x hx y hy
    rw [← Complex.sub_re]
    exact le_trans (Complex.abs_re_le_norm _) (hlipα x hx y hy)
  have hFinc : ∀ x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      ∀ y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2), x ≤ y →
      (1 - gapParameter R n) * (y - x) ≤
        (y - Real.pi * n - (actualSchurAlpha38 n (schurRealPair w) y).re) -
          (x - Real.pi * n - (actualSchurAlpha38 n (schurRealPair w) x).re) := by
    intro x hx y hy hxy
    have h := hre x hx y hy
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at h
    have h' := (abs_le.mp h).2
    nlinarith
  have hβlip : ∀ x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      ∀ y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2),
      |‖actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
            ((y : ℂ), schurRealPair w)‖ -
          ‖actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
            ((x : ℂ), schurRealPair w)‖| ≤ gapParameter R n * |y - x| := by
    intro x hx y hy
    have h := actualSchurEntry_lipschitz38V1 R hR n hn hlarge
      (true, resonantIndex n) (false, resonantIndex n) (schurRealPair w) hp₁ hp₂
      (y : ℂ) (x : ℂ) (hdisk y hy) (hdisk x hx)
    have hn' : ‖(y : ℂ) - (x : ℂ)‖ = |y - x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn'] at h
    exact le_trans (abs_norm_sub_norm_le _ _) h
  have key := gapCenter_shifted_strictMonoOn38V1 (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2)
    (gapParameter R n)
    (fun x : ℝ => x - Real.pi * n - (actualSchurAlpha38 n (schurRealPair w) x).re)
    (fun x : ℝ => ‖actualSchurCoefficientAfterDext31 n (true, resonantIndex n)
      (false, resonantIndex n) ((x : ℂ), schurRealPair w)‖)
    hd0 hd14 hFinc hβlip
  have hF : ∀ x : ℝ, scalarRootAt n w x =
      x - Real.pi * n - (actualSchurAlpha38 n (schurRealPair w) x).re :=
    fun x => rfl
  have hB : ∀ x : ℝ, ‖bAt n (x : ℂ) (schurRealPair w)‖ =
      ‖actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
        ((x : ℂ), schurRealPair w)‖ :=
    fun x => rfl
  dsimp only
  refine ⟨hd14, ?_, key.2, key.1⟩
  intro x hx y hy hxy
  have hA := hFinc x hx y hy hxy.le
  have hBl := hβlip x hx y hy
  rw [abs_of_pos (sub_pos.mpr hxy)] at hBl
  obtain ⟨hB1, hB2⟩ := abs_le.mp hBl
  rw [hF x, hF y, hB x, hB y]
  constructor <;> nlinarith

end NlsGge.ThirdConsultation.S
