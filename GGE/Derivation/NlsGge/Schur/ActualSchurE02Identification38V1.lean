import NlsGge.Schur.ActualSourceRealTypeEigenvalues38V1
import NlsGge.Schur.ActualSchurRealTypeCenter38V1
import NlsGge.Schur.ActualSchurCanonicalAndGapLocal38V1
import NlsGge.Schur.GapActionExponentialComparison38V1
import NlsGge.Spectral.ActualHalfTraceUniformBox38Assembly
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38

/-!
# Identification of the Schur roots with E02's labelled gap (reflected sign)

Source: `paper/v2.tex`, F:eq:qaction, F:eq:action, F:eq:gaplocal.

Setting: `U = physicalH1ComplexCarrierToL2Actual22 w`, `‖w‖ ≤ R`, `|n|` large.  The Schur
roots `λ^±` of `F ∓ β` (`actualSchurShiftedRoots38V1`) belong to the REFLECTED operator
`𝖫_U = -L_{-U}`; they are the NEGATIVES of E02's labelled endpoints at index `-n`:
`λ⁺_Schur(n) = -actualGapLowerE02_38 U (-n)`, `λ⁻_Schur(n) = -actualGapUpperE02_38 U (-n)`.

Explicit hypothesis: `hwin : ActualQuasimomentumWindowE02_38 U (-n)` is an ASSUMPTION here,
until E02's uniform (in `‖w‖_{H¹} ≤ R`) window lemma lands; E02 realizes it only qualitatively
for each fixed `U` (`exists_actualHalfTraceBox_window_E02_38`).  The box hypothesis is NOT
assumed in the `∃ K` theorems: it is produced by `actualHalfTraceBox_uniform38`.

Reflected action: the source's `I_n` for the reflected operator `𝖫_U` is the action of the
gap `[−λ⁺_E, −λ⁻_E]`-reflection, i.e. `actualGapActionE02_38 U (-n)`, because
`v_𝖫(λ) = v_L(-λ)` (`𝖫_U = -L_{-U}`, so the quasimomentum height at `λ` for `𝖫` is the
height at `-λ` for `L`, and the integral over the reflected gap is unchanged).  No Lean lemma
states this action identity (only the endpoint/eigenvalue correspondence
`source_eigenvalue_neg_gapEndpoint_E02_38`); this identification is DOCUMENTED, not proved,
and part (d) is stated directly for `actualGapActionE02_38 U (-n)`.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot NlsGge.SpectralFoundations

namespace NlsGge.Schur

/-- The `H¹` norm of the carrier equals the `physicalSobolevL2 1` norm of its image. -/
theorem physicalSobolevL2_norm_h1Carrier38
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) :
    ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 w)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w)‖ = ‖w‖ := by
  have h1 := physicalSobolevL2_norm_sq 1 (physicalH1ComplexCarrierToL2Actual22 w)
    (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w)
  have h2 := weightedHilbert_norm_sq (sobolevModeWeight (1 : ℝ)) w
  have h3 : (∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
      ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) n‖ ^ 2) =
      ∑' n : ℤ, sobolevModeWeight (1 : ℝ) n * ‖(w : ℤ → ℂ) n‖ ^ 2 := by
    refine tsum_congr (fun n => ?_)
    rw [physicalH1ComplexCarrierToL2Actual22_fourier]
    simp only [sobolevModeWeight, NlsGge.Analysis.japaneseBracket_h1_weight]
  have h4 : ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 w)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w)‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [h1, h3, ← h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h4

theorem actualSchur_realWindow_mem_disk38 (n : ℤ) (x : ℝ)
    (hx : x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2)) :
    (x : ℂ) ∈ spectralDisk n := by
  change ‖(x : ℂ) - spectralCenter n‖ ≤ 1
  have he : (x : ℂ) - spectralCenter n = ((x - Real.pi * n : ℝ) : ℂ) := by
    simp [spectralCenter]; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  obtain ⟨h1, h2⟩ := hx
  constructor <;> linarith

/-- (a) Identification with the reflected sign. -/
theorem actualSchurRoots_eq_neg_E02Gap38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hbox : ActualHalfTraceBoxE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) δ)
    (hwin : ActualQuasimomentumWindowE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n))
    (lp lm : ℝ)
    (hlpI : lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlp : actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0)
    (hlmI : lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlm : actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0) :
    lp = -actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) ∧
    lm = -actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
  set U := physicalH1ComplexCarrierToL2Actual22 w with hU
  obtain ⟨lp0, lm0, ⟨hp0I, hp0⟩, ⟨hm0I, hm0⟩, hz⟩ :=
    actualSchurRoots_halfTrace_realType38 R hR n hthr w hw
  have hp₁ : ‖(w, actualH1Conj38 w).1‖ ≤ R := hw
  have hp₂ : ‖(w, actualH1Conj38 w).2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  obtain ⟨⟨a, -, hau⟩, ⟨b, -, hbu⟩⟩ :=
    actualSchurShiftedRoots38V1 R hR n hthr (w, actualH1Conj38 w) hp₁ hp₂
  have hlp0 : lp0 = lp := by
    have e1 := hau lp0 ⟨hp0I, hp0⟩
    have e2 := hau lp ⟨hlpI, hlp⟩
    rw [e1, e2]
  have hlm0 : lm0 = lm := by
    have e1 := hbu lm0 ⟨hm0I, hm0⟩
    have e2 := hbu lm ⟨hlmI, hlm⟩
    rw [e1, e2]
  subst hlp0 hlm0
  obtain ⟨hord, hLo, hUp, hDL, hDU, -, hone⟩ :=
    actualGapStructureE02_38 U (-n) δ hδ0 hδ hbox hwin
  obtain ⟨-, -, hord2⟩ := actualSourceSectorRoots_ordered_realType38 R hR n hthr w hw lp0 lm0
    hlpI hlp hlmI hlm
  set L := actualGapLowerE02_38 U (-n) with hL
  set Up := actualGapUpperE02_38 U (-n) with hUpdef
  have hcast : (((-n : ℤ) : ℝ)) = -(n : ℝ) := by push_cast; ring
  have hc2 : Real.cos ((n : ℝ) * Real.pi) ^ 2 = 1 := real_cos_int_mul_pi_sq_E02_38 n
  have hcabs : |Real.cos ((n : ℝ) * Real.pi)| = 1 := by
    have : |Real.cos ((n : ℝ) * Real.pi)| ^ 2 = 1 := by rw [sq_abs]; exact hc2
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp this
  have hcosm : Real.cos (((-n : ℤ) : ℝ) * Real.pi) = Real.cos ((n : ℝ) * Real.pi) := by
    rw [hcast, neg_mul, Real.cos_neg]
  -- roots give norm one
  have hnorm : ∀ x : ℝ, x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
      (actualPhysicalUnitHalfTrace32 U (-(x : ℂ)) = spectralSign n) →
      ‖actualPhysicalUnitHalfTrace32 U (((-x : ℝ)) : ℂ)‖ = 1 ∧
        (-x) ∈ Set.Icc (((-n : ℤ) : ℝ) * Real.pi - 1 / 2) (((-n : ℤ) : ℝ) * Real.pi + 1 / 2) := by
    intro x hx htr
    refine ⟨?_, ?_⟩
    · rw [Complex.ofReal_neg, htr, spectralSign_eq_cos_E02_38, Complex.norm_real,
        Real.norm_eq_abs, hcabs]
    · rw [hcast]
      obtain ⟨h1, h2⟩ := hx
      constructor <;> nlinarith
  have hlpT := (hz (lp0 : ℂ) (actualSchur_realWindow_mem_disk38 n lp0 hlpI)).mpr (Or.inl rfl)
  have hlmT := (hz (lm0 : ℂ) (actualSchur_realWindow_mem_disk38 n lm0 hlmI)).mpr (Or.inr rfl)
  obtain ⟨hlp1, hlpW⟩ := hnorm lp0 hlpI hlpT
  obtain ⟨hlm1, hlmW⟩ := hnorm lm0 hlmI hlmT
  have hlpE := (hone _ hlpW).mp hlp1
  have hlmE := (hone _ hlmW).mp hlm1
  -- converse: endpoints are roots
  have hsqrt : 2 * Real.sqrt δ ≤ 1 / 8 := by
    have h1 : Real.sqrt δ ≤ Real.sqrt (1 / 256) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (1 / 256) = 1 / 16 := by
      rw [show (1 : ℝ) / 256 = (1 / 16) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hback : ∀ e : ℝ, |e - ((-n : ℤ) : ℝ) * Real.pi| ≤ 2 * Real.sqrt δ →
      actualPhysicalUnitHalfTrace32 U (e : ℂ) = (Real.cos (((-n : ℤ) : ℝ) * Real.pi) : ℂ) →
      (-e = lp0 ∨ -e = lm0) := by
    intro e he hDe
    have hdisk : ((-e : ℝ) : ℂ) ∈ spectralDisk n := by
      apply actualSchur_realWindow_mem_disk38
      rw [hcast] at he
      rw [abs_le] at he
      constructor <;> nlinarith [he.1, he.2]
    have htr : actualPhysicalUnitHalfTrace32 U (-((-e : ℝ) : ℂ)) = spectralSign n := by
      rw [spectralSign_eq_cos_E02_38, ← hcosm]
      have : -((-e : ℝ) : ℂ) = (e : ℂ) := by push_cast; ring
      rw [this]; exact hDe
    have := (hz _ hdisk).mp htr
    rcases this with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hLr := hback L hLo hDL
  have hUr := hback Up hUp hDU
  -- ordering
  have hord3 : -lp0 ≤ -lm0 := by linarith
  rcases hlpE with h1 | h1 <;> rcases hlmE with h2 | h2 <;>
    rcases hLr with h3 | h3 <;> rcases hUr with h4 | h4 <;>
    refine ⟨by linarith, by linarith⟩

/-- (b) Gap length of the Schur roots, and the lower bound of F:eq:qaction at the reflected
index. -/
theorem actualSchurGapLength_E02_38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hbox : ActualHalfTraceBoxE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) δ)
    (hwin : ActualQuasimomentumWindowE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n))
    (lp lm : ℝ)
    (hlpI : lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlp : actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0)
    (hlmI : lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlm : actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0) :
    lp - lm = actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
        actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) ∧
      2 * ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ /
          (1 + 2 * actualSchurGapParameter38 R n) ≤
        actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
          actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
  obtain ⟨e1, e2⟩ := actualSchurRoots_eq_neg_E02Gap38V1 R hR n hthr w hw δ hδ0 hδ hbox hwin
    lp lm hlpI hlp hlmI hlm
  have hlen : lp - lm = actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
        actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
    rw [e1, e2]; ring
  refine ⟨hlen, ?_⟩
  obtain ⟨hKge, -, -, -⟩ := actualSchurShiftedRootsConstant38_ge
  have hthrC : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge (by positivity)) hthr
  have h := actualSchurQnRealType_gap_lower38 R hR n hthrC w hw lm lp hlmI hlpI hlp hlm
  rw [← hlen]; exact h

/-- (c) F:eq:gaplocal for E02's labelled endpoints at the reflected index. -/
theorem actualSchurE02Endpoints_gapLocal38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hbox : ActualHalfTraceBoxE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) δ)
    (hwin : ActualQuasimomentumWindowE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n))
    (lp lm : ℝ)
    (hlpI : lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlp : actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0)
    (hlmI : lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlm : actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0) :
    |actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi| ≤
        actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| ∧
      |actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi| ≤
        actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| := by
  obtain ⟨e1, e2⟩ := actualSchurRoots_eq_neg_E02Gap38V1 R hR n hthr w hw δ hδ0 hδ hbox hwin
    lp lm hlpI hlp hlmI hlm
  have hp₁ : ‖(w, actualH1Conj38 w).1‖ ≤ R := hw
  have hp₂ : ‖(w, actualH1Conj38 w).2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  have g1 := actualSchurRoot_gapLocal38 R hR n hthr (w, actualH1Conj38 w) hp₁ hp₂ lp hlpI
    (Or.inl hlp)
  have g2 := actualSchurRoot_gapLocal38 R hR n hthr (w, actualH1Conj38 w) hp₁ hp₂ lm hlmI
    (Or.inr hlm)
  have k1 : actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi =
      -(lp - Real.pi * n) := by rw [e1]; ring
  have k2 : actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi =
      -(lm - Real.pi * n) := by rw [e2]; ring
  rw [k1, k2, abs_neg, abs_neg]
  exact ⟨g1, g2⟩

/-- (d) `I_n ≥ e^{-4d} |q_n|²`, with `I_n = actualGapActionE02_38 U (-n)`. -/
theorem actualSchurAction_exp_lower_E02_38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    (hbox : ActualHalfTraceBoxE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) δ)
    (hwin : ActualQuasimomentumWindowE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n))
    (lp lm : ℝ)
    (hlpI : lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlp : actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0)
    (hlmI : lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlm : actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0) :
    Real.exp (-4 * actualSchurGapParameter38 R n) *
        ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ ^ 2 ≤
      actualGapActionE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
  obtain ⟨-, hg⟩ := actualSchurGapLength_E02_38V1 R hR n hthr w hw δ hδ0 hδ hbox hwin
    lp lm hlpI hlp hlmI hlm
  have hI := actualGapAction_ge_sq_div_four_E02_38 (physicalH1ComplexCarrierToL2Actual22 w)
    (-n) δ hδ0 hδ hbox hwin
  have hd0 : 0 ≤ actualSchurGapParameter38 R n := by
    have hI' : 0 < freeResolventComplementaryInverseUniformConstant22 :=
      freeResolventComplementaryInverseUniformConstant22_posV2_31
    rw [actualSchurGapParameter38]
    positivity
  exact gapAction_exp_comparison38V1 _ _ _ _ hd0 (norm_nonneg _) hg hI

/-- Uniform packaging: there is an absolute `K` such that for `‖w‖ ≤ R`, `|n| ≥ K R³` (which
covers both the shifted-root threshold and the uniform box with `δ ≤ 1/1000`), and the
explicit window hypothesis at `-n`, the Schur roots exist and satisfy (a)-(d). -/
theorem actualSchurE02Identification38V1 :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → ∀ n : ℤ, K * R ^ 3 ≤ |(n : ℝ)| →
      ∀ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)), ‖w‖ ≤ R →
      ActualQuasimomentumWindowE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) →
      (∃ lp lm : ℝ,
        (lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
          actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0) ∧
        (lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
          actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0)) ∧
      ∀ lp lm : ℝ,
        lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0 →
        lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0 →
        (lp = -actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) ∧
          lm = -actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)) ∧
        (lp - lm = actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
            actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) ∧
          2 * ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ /
              (1 + 2 * actualSchurGapParameter38 R n) ≤
            actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) -
              actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)) ∧
        (|actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi| ≤
            actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)| ∧
          |actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) + n * Real.pi| ≤
            actualSchurGapLocalConstant38 * R ^ 3 / |(n : ℝ)|) ∧
        Real.exp (-4 * actualSchurGapParameter38 R n) *
            ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ ^ 2 ≤
          actualGapActionE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
  obtain ⟨Kb, Cb, hKb, hCb, hbx⟩ := actualHalfTraceBox_uniform38
  obtain ⟨-, -, hK3, -⟩ := actualSchurShiftedRootsConstant38_ge
  refine ⟨max actualSchurShiftedRootsConstant38 (Kb + 1000 * Cb), lt_of_lt_of_le
    (by linarith) (le_max_left _ _), ?_⟩
  intro R hR n hn w hw hwin
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR2R3 : R ^ 2 ≤ R ^ 3 := by nlinarith [sq_nonneg R, sq_nonneg (R - 1)]
  have hR2 : 0 ≤ R ^ 2 := by positivity
  have hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hn
  have hn2 : (Kb + 1000 * Cb) * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hn
  have hnK : Kb * R ^ 2 ≤ |(((-n : ℤ)) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
    nlinarith [mul_le_mul_of_nonneg_left hR2R3 hKb.le, mul_nonneg hCb.le (by positivity : (0:ℝ) ≤ R ^ 3)]
  have hNpos : 0 < |(((-n : ℤ)) : ℝ)| := lt_of_lt_of_le (by positivity) hnK
  have hbox := hbx R hR _ (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w)
    (by rw [physicalSobolevL2_norm_h1Carrier38]; exact hw) (-n) hnK
  have hδ0 : 0 ≤ Cb * R ^ 2 / |(((-n : ℤ)) : ℝ)| := by positivity
  have hδ : Cb * R ^ 2 / |(((-n : ℤ)) : ℝ)| ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    rw [Int.cast_neg, abs_neg]
    nlinarith [mul_le_mul_of_nonneg_left hR2R3 hCb.le, mul_nonneg hKb.le (by positivity : (0:ℝ) ≤ R ^ 3)]
  refine ⟨?_, ?_⟩
  · obtain ⟨hp₁, hp₂⟩ : ‖(w, actualH1Conj38 w).1‖ ≤ R ∧ ‖(w, actualH1Conj38 w).2‖ ≤ R :=
      ⟨hw, by change ‖actualH1Conj38 w‖ ≤ R; rw [actualH1Conj38_norm]; exact hw⟩
    obtain ⟨⟨a, ha, -⟩, ⟨b, hb, -⟩⟩ :=
      actualSchurShiftedRoots38V1 R hR n hthr (w, actualH1Conj38 w) hp₁ hp₂
    exact ⟨a, b, ha, hb⟩
  · intro lp lm hlpI hlp hlmI hlm
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact actualSchurRoots_eq_neg_E02Gap38V1 R hR n hthr w hw _ hδ0 hδ hbox hwin
        lp lm hlpI hlp hlmI hlm
    · exact actualSchurGapLength_E02_38V1 R hR n hthr w hw _ hδ0 hδ hbox hwin
        lp lm hlpI hlp hlmI hlm
    · exact actualSchurE02Endpoints_gapLocal38V1 R hR n hthr w hw _ hδ0 hδ hbox hwin
        lp lm hlpI hlp hlmI hlm
    · exact actualSchurAction_exp_lower_E02_38V1 R hR n hthr w hw _ hδ0 hδ hbox hwin
        lp lm hlpI hlp hlmI hlm

end NlsGge.Schur
