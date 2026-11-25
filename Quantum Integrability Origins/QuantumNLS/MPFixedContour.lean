import Mathlib
import QuantumNLS.PeriodReconstruction
import QuantumNLS.MPFamily
import QuantumNLS.MPContourBound

/-!
# PROP-026: the background family `BgFam` for the actual Cauchy transform, and the fixed action contours `Γ = ∂([x₋,x₊] × [−h,h])`

New module.  Binds the abstract background of `MPFamily.BgFam` to the actual objects of the source's setup:

* **`bgfamOfG`**: for ANY `G : ℂ → ℂ` complex differentiable at every point of a set `Z`, with the uniform bounds
  `η ≤ ‖D‖`, `‖A‖, ‖A⁻¹‖, ‖e‖ ≤ M` and `‖G‖ ≤ Gb` on `Z` (`A = e^{iκG}`, `D = A − e/A`, `s = A + e/A`, `e = e^{iLz}`), the family
  `c₀ = iκG`, `D = Df L κ G`, `s = sf L κ G`, `A = Af κ G` is a `BgFam Z η (M+M²) (1/M) (κ Gb)`
  (the algebraic relation `A = (s+D)/2` is automatic).
* **`gam_background`**: for the actual indexed scalar measure `S` (DEF-043 `IndexedScalarMeasureCuts`), `G = cauchyTransform S.μ`, two regular
  cutpoints `x₋ < x₊` in `S.cuts` with the label hypotheses of PROP-006, and `h > 0`, the bounds above hold on the compact fixed
  contour `Gam x₋ x₊ h` (reusing `PeriodReconstruction`: `differentiableAt_cauchy`, `D_ne_zero_of_im`, `D_ne_zero_real`, `norm_cauchy_le`,
  and the compactness minimum of `‖D‖`): this is the same bundle as inside `log_reconstruction`, exported.
* **`gam_bgfam`**: the resulting `BgFam (Gam x₋ x₊ h)` for the actual `G`.
* **`rectGen`**: the six affine pieces of `∂([x₋,x₊] × [−h,h])` (split at the real axis); `rectGen_mem_Gam`, `rectGen_im_le`,
  `rectGen_im_ne`, and `rectGen_wlen_le`: for the constant weight `θ_n`, `Σ_i wlen ≤ |θ_n| (2(x₊−x₋) + 4h)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.MPFixedContour

open QuantumNLS.MPContour QuantumNLS.MPFamily QuantumNLS.MPChartSmooth
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction
open QuantumNLS.EmpiricalRapidity (cauchyTransform)
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts

/-! ### The background family for a general `G` -/

section BgG

variable (L κ : ℝ) (G : ℂ → ℂ) (Z : Set ℂ)

/-- `BgFam` for `c₀ = iκG`, `D = Df`, `s = sf`, `A = Af`. -/
def bgfamOfG {η M Gb : ℝ} (hη : 0 < η) (hM : 1 ≤ M) (hGb : 0 ≤ Gb)
    (hdiff : ∀ z ∈ Z, DifferentiableAt ℂ G z) (hD : ∀ z ∈ Z, η ≤ ‖Df L κ G z‖)
    (hA : ∀ z ∈ Z, ‖Af κ G z‖ ≤ M) (hAi : ∀ z ∈ Z, ‖(Af κ G z)⁻¹‖ ≤ M) (he : ∀ z ∈ Z, ‖ef L z‖ ≤ M)
    (hGn : ∀ z ∈ Z, ‖G z‖ ≤ Gb) (hκ : 0 ≤ κ) :
    BgFam Z η (M + M * M) (1 / M) (κ * Gb) where
  c0 := fun z => I * κ * G z
  D := Df L κ G
  s := sf L κ G
  A := Af κ G
  hc0 := fun z hz => (((hdiff z hz.1).continuousAt.const_mul (I * κ)).continuousWithinAt)
  hD := fun z hz => by
    have hA' : ContinuousAt (Af κ G) z := ((hdiff z hz.1).continuousAt.const_mul (I * κ)).cexp
    have he' : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    exact (hA'.sub (he'.div hA' (exp_ne_zero _))).continuousWithinAt
  hs := fun z hz => by
    have hA' : ContinuousAt (Af κ G) z := ((hdiff z hz.1).continuousAt.const_mul (I * κ)).cexp
    have he' : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    exact (hA'.add (he'.div hA' (exp_ne_zero _))).continuousWithinAt
  hA := fun z hz => (((hdiff z hz.1).continuousAt.const_mul (I * κ)).cexp).continuousWithinAt
  bg := fun z hz _ => by
    have hMpos : 0 < M := by linarith
    have hAne : Af κ G z ≠ 0 := exp_ne_zero _
    have hnorm : ‖Af κ G z‖ * ‖(Af κ G z)⁻¹‖ = 1 := by
      rw [← norm_mul, mul_inv_cancel₀ hAne, norm_one]
    refine ⟨hη, by positivity, by positivity, hD z hz, ?_, ?_, ?_⟩
    · -- ‖s‖ ≤ M + M²
      show ‖Af κ G z + ef L z / Af κ G z‖ ≤ M + M * M
      calc ‖Af κ G z + ef L z / Af κ G z‖ ≤ ‖Af κ G z‖ + ‖ef L z / Af κ G z‖ := norm_add_le _ _
        _ ≤ M + M * M := by
          rw [div_eq_mul_inv, norm_mul]
          exact add_le_add (hA z hz) (mul_le_mul (he z hz) (hAi z hz) (norm_nonneg _) (by linarith))
    · -- a₀ ≤ ‖A‖
      show 1 / M ≤ ‖Af κ G z‖
      have h1 : 0 < ‖Af κ G z‖ := norm_pos_iff.2 (exp_ne_zero _)
      rw [div_le_iff₀ hMpos]
      calc 1 = ‖Af κ G z‖ * ‖(Af κ G z)⁻¹‖ := hnorm.symm
        _ ≤ ‖Af κ G z‖ * M := mul_le_mul_of_nonneg_left (hAi z hz) h1.le
    · show Af κ G z = (sf L κ G z + Df L κ G z) / 2
      unfold sf Df; ring
  c0le := fun z hz _ => by
    show ‖I * κ * G z‖ ≤ κ * Gb
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
    exact mul_le_mul_of_nonneg_left (hGn z hz) hκ
  s_le := fun z hz => by
    have hMpos : 0 < M := by linarith
    show ‖Af κ G z + ef L z / Af κ G z‖ ≤ M + M * M
    calc ‖Af κ G z + ef L z / Af κ G z‖ ≤ ‖Af κ G z‖ + ‖ef L z / Af κ G z‖ := norm_add_le _ _
      _ ≤ M + M * M := by
        rw [div_eq_mul_inv, norm_mul]
        exact add_le_add (hA z hz) (mul_le_mul (he z hz) (hAi z hz) (norm_nonneg _) (by linarith))

end BgG

/-! ### The fixed contour for the actual indexed scalar measure -/

section GamBg

/-- **The background bundle on the fixed contour `Γ = ∂([x₋,x₊]×[−h,h])` for the actual `G = G_{S.μ}`** (exported from the proof of
`PeriodReconstruction.log_reconstruction`; same hypotheses: regular cutpoints and the PROP-006 label brackets). -/
theorem gam_background {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {n : ℤ} {xm xp h : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ η M Gb : ℝ, 0 < η ∧ 1 ≤ M ∧ 0 ≤ Gb ∧ ∀ z ∈ Gam xm xp h,
      DifferentiableAt ℂ (cauchyTransform S.μ) z ∧ η ≤ ‖Df L κ (cauchyTransform S.μ) z‖ ∧
      ‖Af κ (cauchyTransform S.μ) z‖ ≤ M ∧ ‖(Af κ (cauchyTransform S.μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
      ‖cauchyTransform S.μ z‖ ≤ Gb := by
  have : IsProbabilityMeasure S.μ := S.isProb
  have hL := S.hL
  have hκ := S.hκ
  set G := cauchyTransform S.μ with hG
  set Γ := Gam xm xp h with hΓ
  have hΓc : IsCompact Γ := isCompact_Gam xm xp h
  obtain ⟨rm, hrm, hbm⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xm
    (S.cuts_sub hxm)
  obtain ⟨rp, hrp, hbp⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xp
    (S.cuts_sub hxp)
  have hsm : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xm| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbm (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_left _ _)) ht
  have hsp : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xp| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbp (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_right _ _)) ht
  set d0 := min (min rm rp) h with hd0def
  have hd0 : 0 < d0 := by positivity
  have hsupp : ∀ z ∈ Γ, ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖ := fun z hz t ht =>
    Gam_dist hh (hsm t ht) (hsp t ht) hz
  have hGd : ∀ z ∈ Γ, DifferentiableAt ℂ G z := fun z hz =>
    differentiableAt_cauchy S.μ hd0 (hsupp z hz)
  have hDz : ∀ z ∈ Γ, Df L κ G z ≠ 0 := by
    intro z hz
    rcases Gam_im_ne_zero_or hh hz with him | hreal
    · exact D_ne_zero_of_im hL hκ (im_sign_cauchy S.μ him)
    · rcases hreal with rfl | rfl
      · exact D_ne_zero_real S.μ (F_not_mem h1 h2)
      · exact D_ne_zero_real S.μ (F_not_mem (n := n + 1) (by push_cast; linarith)
          (by push_cast; linarith))
  have hDc : ∀ z ∈ Γ, ContinuousAt (Df L κ G) z := fun z hz => by
    have hA : ContinuousAt (Af κ G) z := ((hGd z hz).continuousAt.const_mul (I * κ)).cexp
    have he : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    exact hA.sub (he.div hA (exp_ne_zero _))
  obtain ⟨z0, hz0, hmin⟩ := hΓc.exists_isMinOn (Gam_nonempty hlt.le)
    (f := fun z => ‖Df L κ G z‖) (fun z hz => (hDc z hz).norm.continuousWithinAt)
  set η := ‖Df L κ G z0‖
  have hη : 0 < η := norm_pos_iff.2 (hDz z0 hz0)
  set M := max 1 (max (Real.exp (κ / d0)) (Real.exp (L * h)))
  have hM0 : 1 ≤ M := le_max_left _ _
  refine ⟨η, M, 1 / d0, hη, hM0, by positivity, fun z hz => ?_⟩
  have hGb := norm_cauchy_le S.μ hd0 (hsupp z hz)
  have himG : |(G z).im| ≤ 1 / d0 := (Complex.abs_im_le_norm _).trans hGb
  have hk : κ * |(G z).im| ≤ κ / d0 := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left himG hκ.le
  have hzim := Gam_abs_im hh hz
  have hexp1 : Real.exp (κ / d0) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hexp2 : Real.exp (L * h) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hGd z hz, hmin hz, ?_, ?_, ?_, hGb⟩
  · rw [norm_Af]
    refine (Real.exp_le_exp.2 ?_).trans hexp1
    nlinarith [neg_abs_le (G z).im, le_abs_self (G z).im]
  · rw [norm_inv_Af]
    refine (Real.exp_le_exp.2 ?_).trans hexp1
    nlinarith [neg_abs_le (G z).im, le_abs_self (G z).im]
  · rw [norm_ef]
    refine (Real.exp_le_exp.2 ?_).trans hexp2
    nlinarith [neg_abs_le z.im, le_abs_self z.im]

/-- **`BgFam` on the fixed contour for the actual `G`.** -/
theorem gam_bgfam {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {n : ℤ} {xm xp h : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ d₀ s₁ a₀ c₁ : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧
      ∃ B : BgFam (Gam xm xp h) d₀ s₁ a₀ c₁,
        B.c0 = (fun z => I * κ * cauchyTransform S.μ z) ∧ B.D = Df L κ (cauchyTransform S.μ) ∧
        B.s = sf L κ (cauchyTransform S.μ) ∧ B.A = Af κ (cauchyTransform S.μ) := by
  obtain ⟨η, M, Gb, hη, hM, hGb, hb⟩ := gam_background S hxm hxp hlt hh h1 h2 h3 h4
  have hκ := S.hκ
  refine ⟨η, M + M * M, 1 / M, κ * Gb, hη, by positivity, by positivity, by positivity, ?_⟩
  exact ⟨bgfamOfG L κ (cauchyTransform S.μ) (Gam xm xp h) hη hM hGb
    (fun z hz => (hb z hz).1) (fun z hz => (hb z hz).2.1) (fun z hz => (hb z hz).2.2.1)
    (fun z hz => (hb z hz).2.2.2.1) (fun z hz => (hb z hz).2.2.2.2.1) (fun z hz => (hb z hz).2.2.2.2.2)
    hκ.le, rfl, rfl, rfl, rfl⟩

end GamBg

/-! ### The six pieces of `∂([x₋,x₊] × [−h,h])` -/

section Rect

variable (xm xp h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω)

def rectGen : Fin 6 → Piece :=
  ![affinePiece ((xm : ℂ) - h * I) ((xp : ℂ) - h * I) ω hω,
    affinePiece ((xp : ℂ) - h * I) (xp : ℂ) ω hω,
    affinePiece (xp : ℂ) ((xp : ℂ) + h * I) ω hω,
    affinePiece ((xp : ℂ) + h * I) ((xm : ℂ) + h * I) ω hω,
    affinePiece ((xm : ℂ) + h * I) (xm : ℂ) ω hω,
    affinePiece (xm : ℂ) ((xm : ℂ) - h * I) ω hω]

lemma rectGen_re_im (i : Fin 6) (τ : ℝ) :
    ((rectGen xm xp h ω hω i).γ τ).re = ![xm + τ * (xp - xm), xp, xp, xp - τ * (xp - xm), xm, xm] i ∧
    ((rectGen xm xp h ω hω i).γ τ).im = ![-h, -h + h * τ, h * τ, h, h - h * τ, -(h * τ)] i := by
  fin_cases i <;> simp [rectGen, affinePiece] <;> ring_nf

lemma rectGen_mem_Gam (hxx : xm ≤ xp) (hh : 0 ≤ h) (i : Fin 6) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    (rectGen xm xp h ω hω i).γ τ ∈ Gam xm xp h := by
  obtain ⟨h0, h1⟩ := hτ
  obtain ⟨hre, him⟩ := rectGen_re_im xm xp h ω hω i τ
  generalize (rectGen xm xp h ω hω i).γ τ = z at hre him ⊢
  simp only [Gam, mem_union, Set.mem_setOf_eq]
  fin_cases i <;> simp at hre him <;> rw [hre, him]
  · exact Or.inl ⟨⟨by nlinarith, by nlinarith⟩, Or.inl rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inr rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inr rfl⟩
  · exact Or.inl ⟨⟨by nlinarith, by nlinarith⟩, Or.inr rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inl rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inl rfl⟩

lemma rectGen_im_ne (hh : 0 < h) (i : Fin 6) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ((rectGen xm xp h ω hω i).γ τ).im ≠ 0 := by
  obtain ⟨h0, h1⟩ := hτ
  rw [(rectGen_re_im xm xp h ω hω i τ).2]
  intro hc
  fin_cases i <;> simp at hc <;> (try rcases hc with hc | hc) <;> nlinarith

lemma rectGen_im_le (hh : 0 < h) (i : Fin 6) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    |((rectGen xm xp h ω hω i).γ τ).im| ≤ h := by
  obtain ⟨h0, h1⟩ := hτ
  have p1 := mul_nonneg hh.le h0
  have p2 := mul_nonneg hh.le (sub_nonneg.2 h1)
  rw [(rectGen_re_im xm xp h ω hω i τ).2]
  fin_cases i <;>
    (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_succ]
     <;> rw [abs_le] <;> constructor <;> nlinarith [hh])

lemma wlen_affine_const (p q c : ℂ) :
    wlen (affinePiece p q (fun _ => c) continuous_const) ≤ ‖c‖ * ‖q - p‖ :=
  wlen_le _ (norm_nonneg c) (fun τ _ => by simp [affinePiece]) (fun τ => by simp [affinePiece])

/-- Weighted length of the fixed contour for the constant weight `c = θ_n`: `Σ_i wlen ≤ |θ_n| (2(x₊−x₋) + 4h)`. -/
theorem rectGen_wlen_le (c : ℂ) (hxx : xm ≤ xp) (hh : 0 ≤ h) :
    ∑ i : Fin 6, wlen (rectGen xm xp h (fun _ => c) continuous_const i) ≤ ‖c‖ * (2 * (xp - xm) + 4 * h) := by
  have hI : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := fun x => by simp
  rw [Fin.sum_univ_six]
  have e0 : rectGen xm xp h (fun _ => c) continuous_const 0 =
      affinePiece ((xm : ℂ) - h * I) ((xp : ℂ) - h * I) (fun _ => c) continuous_const := rfl
  have e1 : rectGen xm xp h (fun _ => c) continuous_const 1 =
      affinePiece ((xp : ℂ) - h * I) (xp : ℂ) (fun _ => c) continuous_const := rfl
  have e2 : rectGen xm xp h (fun _ => c) continuous_const 2 =
      affinePiece (xp : ℂ) ((xp : ℂ) + h * I) (fun _ => c) continuous_const := rfl
  have e3 : rectGen xm xp h (fun _ => c) continuous_const 3 =
      affinePiece ((xp : ℂ) + h * I) ((xm : ℂ) + h * I) (fun _ => c) continuous_const := rfl
  have e4 : rectGen xm xp h (fun _ => c) continuous_const 4 =
      affinePiece ((xm : ℂ) + h * I) (xm : ℂ) (fun _ => c) continuous_const := rfl
  have e5 : rectGen xm xp h (fun _ => c) continuous_const 5 =
      affinePiece (xm : ℂ) ((xm : ℂ) - h * I) (fun _ => c) continuous_const := rfl
  rw [e0, e1, e2, e3, e4, e5]
  have n0 : ‖((xp : ℂ) - h * I) - ((xm : ℂ) - h * I)‖ = xp - xm := by
    have : ((xp : ℂ) - h * I) - ((xm : ℂ) - h * I) = ((xp - xm : ℝ) : ℂ) := by push_cast; ring
    rw [this, hI, abs_of_nonneg (by linarith)]
  have n1 : ‖(xp : ℂ) - ((xp : ℂ) - h * I)‖ = h := by
    have : (xp : ℂ) - ((xp : ℂ) - h * I) = ((h : ℝ) : ℂ) * I := by ring
    rw [this, norm_mul, hI, abs_of_nonneg hh]; simp
  have n2 : ‖((xp : ℂ) + h * I) - (xp : ℂ)‖ = h := by
    have : ((xp : ℂ) + h * I) - (xp : ℂ) = ((h : ℝ) : ℂ) * I := by ring
    rw [this, norm_mul, hI, abs_of_nonneg hh]; simp
  have n3 : ‖((xm : ℂ) + h * I) - ((xp : ℂ) + h * I)‖ = xp - xm := by
    have : ((xm : ℂ) + h * I) - ((xp : ℂ) + h * I) = ((-(xp - xm) : ℝ) : ℂ) := by push_cast; ring
    rw [this, hI, abs_neg, abs_of_nonneg (by linarith)]
  have n4 : ‖(xm : ℂ) - ((xm : ℂ) + h * I)‖ = h := by
    have : (xm : ℂ) - ((xm : ℂ) + h * I) = -(((h : ℝ) : ℂ) * I) := by ring
    rw [this, norm_neg, norm_mul, hI, abs_of_nonneg hh]; simp
  have n5 : ‖((xm : ℂ) - h * I) - (xm : ℂ)‖ = h := by
    have : ((xm : ℂ) - h * I) - (xm : ℂ) = -(((h : ℝ) : ℂ) * I) := by ring
    rw [this, norm_neg, norm_mul, hI, abs_of_nonneg hh]; simp
  have w0 := wlen_affine_const ((xm : ℂ) - h * I) ((xp : ℂ) - h * I) c
  have w1 := wlen_affine_const ((xp : ℂ) - h * I) (xp : ℂ) c
  have w2 := wlen_affine_const (xp : ℂ) ((xp : ℂ) + h * I) c
  have w3 := wlen_affine_const ((xp : ℂ) + h * I) ((xm : ℂ) + h * I) c
  have w4 := wlen_affine_const ((xm : ℂ) + h * I) (xm : ℂ) c
  have w5 := wlen_affine_const (xm : ℂ) ((xm : ℂ) - h * I) c
  rw [n0] at w0; rw [n1] at w1; rw [n2] at w2; rw [n3] at w3; rw [n4] at w4; rw [n5] at w5
  nlinarith [w0, w1, w2, w3, w4, w5]

end Rect

section Union

variable (L κ : ℝ) (G : ℂ → ℂ) (Z₁ Z₂ : Set ℂ)

/-- Union of two contour sets (large contour and fixed contours): the bounds combine by `min`/`max`. -/
def bgfamOfG_union {η₁ M₁ Gb₁ η₂ M₂ Gb₂ : ℝ} (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (hGb₁ : 0 ≤ Gb₁) (hGb₂ : 0 ≤ Gb₂) (hκ : 0 ≤ κ)
    (hdiff : ∀ z ∈ Z₁ ∪ Z₂, DifferentiableAt ℂ G z)
    (hD₁ : ∀ z ∈ Z₁, η₁ ≤ ‖Df L κ G z‖) (hD₂ : ∀ z ∈ Z₂, η₂ ≤ ‖Df L κ G z‖)
    (hA₁ : ∀ z ∈ Z₁, ‖Af κ G z‖ ≤ M₁) (hA₂ : ∀ z ∈ Z₂, ‖Af κ G z‖ ≤ M₂)
    (hAi₁ : ∀ z ∈ Z₁, ‖(Af κ G z)⁻¹‖ ≤ M₁) (hAi₂ : ∀ z ∈ Z₂, ‖(Af κ G z)⁻¹‖ ≤ M₂)
    (he₁ : ∀ z ∈ Z₁, ‖ef L z‖ ≤ M₁) (he₂ : ∀ z ∈ Z₂, ‖ef L z‖ ≤ M₂)
    (hG₁ : ∀ z ∈ Z₁, ‖G z‖ ≤ Gb₁) (hG₂ : ∀ z ∈ Z₂, ‖G z‖ ≤ Gb₂) :
    BgFam (Z₁ ∪ Z₂) (min η₁ η₂) (max M₁ M₂ + max M₁ M₂ * max M₁ M₂) (1 / max M₁ M₂) (κ * max Gb₁ Gb₂) :=
  bgfamOfG L κ G (Z₁ ∪ Z₂) (lt_min hη₁ hη₂) (le_trans hM₁ (le_max_left _ _)) (le_trans hGb₁ (le_max_left _ _))
    hdiff
    (fun z hz => hz.elim (fun h => (min_le_left _ _).trans (hD₁ z h)) (fun h => (min_le_right _ _).trans (hD₂ z h)))
    (fun z hz => hz.elim (fun h => (hA₁ z h).trans (le_max_left _ _)) (fun h => (hA₂ z h).trans (le_max_right _ _)))
    (fun z hz => hz.elim (fun h => (hAi₁ z h).trans (le_max_left _ _)) (fun h => (hAi₂ z h).trans (le_max_right _ _)))
    (fun z hz => hz.elim (fun h => (he₁ z h).trans (le_max_left _ _)) (fun h => (he₂ z h).trans (le_max_right _ _)))
    (fun z hz => hz.elim (fun h => (hG₁ z h).trans (le_max_left _ _)) (fun h => (hG₂ z h).trans (le_max_right _ _)))
    hκ

end Union

end QuantumNLS.MPFixedContour

#print axioms QuantumNLS.MPFixedContour.gam_background
#print axioms QuantumNLS.MPFixedContour.gam_bgfam
#print axioms QuantumNLS.MPFixedContour.rectGen_wlen_le
#print axioms QuantumNLS.MPFixedContour.rectGen_mem_Gam
#print axioms QuantumNLS.MPFixedContour.rectGen_im_ne
#print axioms QuantumNLS.MPFixedContour.rectGen_im_le
#print axioms QuantumNLS.MPFixedContour.bgfamOfG_union
