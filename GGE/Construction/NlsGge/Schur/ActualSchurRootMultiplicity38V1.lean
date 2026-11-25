import NlsGge.Schur.ActualSchurRealTypeEigenvalues38V1
import NlsGge.Schur.ActualSourceRealTypeEigenvalues38V1

/-!
# F03.07: multiplicity of the Schur determinant roots for real-type potentials

For the real-type pair `p = (w, w̄)` with `‖w‖ ≤ R`, `|n| ≥ K R³`, the analytic function
`z ↦ det((z - nπ) - A_n(z)) = actualSchurDet38 n p z` has exactly the zeros
`{λ⁻, λ⁺}` in the disk `|z - nπ| ≤ 1`; if `λ⁻ < λ⁺` both are simple
(`deriv ≠ 0`, `analyticOrderAt = 1`), and if `λ⁻ = λ⁺` the zero has
`analyticOrderAt = 2`.

Route: write `det = g₁ g₂ - b e` with `g_i = z - nπ - α_ii(z)`, all four entries analytic with
derivatives of size `≤ d ≤ 1/4`; at a real root `|g_i| = |b| = |e| = β`.  Open case:
`det' = β·(2 - α₁' - α₂')·(±1) - b'e - be'` has modulus `≥ β(2 - 4d) > 0`.  Closed case
(`g = b = e = 0`): `det = (z-λ)²(g₁'g₂' - b₁e₁)` with `g₁'g₂' - b'e' ≠ 0`
(`(1-d)² > d²`); no second derivative is needed.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

theorem analyticAt_dslope38 {f : ℂ → ℂ} {z0 : ℂ} (hf : AnalyticAt ℂ f z0) :
    AnalyticAt ℂ (dslope f z0) z0 := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

theorem analyticOrderAt_eq_one_of_deriv38 (f : ℂ → ℂ) (z0 : ℂ) (hf : AnalyticAt ℂ f z0)
    (h0 : f z0 = 0) (h1 : deriv f z0 ≠ 0) : analyticOrderAt f z0 = 1 := by
  have : analyticOrderAt f z0 = ((1 : ℕ) : ℕ∞) := by
    rw [hf.analyticOrderAt_eq_natCast]
    refine ⟨dslope f z0, analyticAt_dslope38 hf, ?_, ?_⟩
    · rw [dslope_same]; exact h1
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have := sub_smul_dslope_of_zero h0 z
      simp only [pow_one, smul_eq_mul] at this ⊢
      exact this.symm
  simpa using this

theorem analyticOrderAt_eq_two_of_factored38 (g1 g2 b e : ℂ → ℂ) (z0 : ℂ)
    (h1 : AnalyticAt ℂ g1 z0) (h2 : AnalyticAt ℂ g2 z0) (h3 : AnalyticAt ℂ b z0)
    (h4 : AnalyticAt ℂ e z0)
    (z1 : g1 z0 = 0) (z2 : g2 z0 = 0) (z3 : b z0 = 0) (z4 : e z0 = 0)
    (hne : deriv g1 z0 * deriv g2 z0 - deriv b z0 * deriv e z0 ≠ 0) :
    analyticOrderAt (fun z => g1 z * g2 z - b z * e z) z0 = 2 := by
  have : analyticOrderAt (fun z => g1 z * g2 z - b z * e z) z0 = ((2 : ℕ) : ℕ∞) := by
    rw [AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)]
    refine ⟨fun z => dslope g1 z0 z * dslope g2 z0 z - dslope b z0 z * dslope e z0 z,
      ?_, ?_, ?_⟩
    · exact ((analyticAt_dslope38 h1).mul (analyticAt_dslope38 h2)).sub
        ((analyticAt_dslope38 h3).mul (analyticAt_dslope38 h4))
    · simp only [dslope_same]; exact hne
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have a1 := sub_smul_dslope_of_zero z1 z
      have a2 := sub_smul_dslope_of_zero z2 z
      have a3 := sub_smul_dslope_of_zero z3 z
      have a4 := sub_smul_dslope_of_zero z4 z
      simp only [smul_eq_mul] at a1 a2 a3 a4 ⊢
      rw [← a1, ← a2, ← a3, ← a4]; ring
  simpa using this

/-- Open-gap algebra: the derivative of `g₁g₂ - be` at a root with `|g_i| = |b| = |e| = β > 0`. -/
theorem openGap_alg38 (γ B E a1 a2 b' e' : ℂ) (β d : ℝ) (hβ : 0 < β)
    (hd : d ≤ 1 / 4) (hγ : ‖γ‖ = β) (hB : ‖B‖ = β) (hE : ‖E‖ = β)
    (ha1 : ‖a1‖ ≤ d) (ha2 : ‖a2‖ ≤ d) (hb' : ‖b'‖ ≤ d) (he' : ‖e'‖ ≤ d) :
    (1 - a1) * γ + γ * (1 - a2) - b' * E - B * e' ≠ 0 := by
  intro h
  have h1 : γ * (2 - a1 - a2) = b' * E + B * e' := by linear_combination h
  have h2 : ‖γ * (2 - a1 - a2)‖ ≤ 2 * d * β := by
    rw [h1]
    calc ‖b' * E + B * e'‖ ≤ ‖b' * E‖ + ‖B * e'‖ := norm_add_le _ _
      _ = ‖b'‖ * β + β * ‖e'‖ := by rw [norm_mul, norm_mul, hE, hB]
      _ ≤ d * β + β * d := by gcongr
      _ = 2 * d * β := by ring
  have h3 : 2 - 2 * d ≤ ‖2 - a1 - a2‖ := by
    have : ‖(2 : ℂ)‖ - ‖a1 + a2‖ ≤ ‖(2 : ℂ) - (a1 + a2)‖ := norm_sub_norm_le _ _
    have h4 : ‖a1 + a2‖ ≤ 2 * d := le_trans (norm_add_le _ _) (by linarith)
    have e2 : (2 : ℂ) - a1 - a2 = 2 - (a1 + a2) := by ring
    rw [e2]; simp at this; linarith
  rw [norm_mul, hγ] at h2
  nlinarith [mul_le_mul_of_nonneg_left h3 hβ.le]

/-- Closed-gap algebra. -/
theorem closedGap_alg38 (a1 a2 b' e' : ℂ) (d : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 4)
    (ha1 : ‖a1‖ ≤ d) (ha2 : ‖a2‖ ≤ d) (hb' : ‖b'‖ ≤ d) (he' : ‖e'‖ ≤ d) :
    (1 - a1) * (1 - a2) - b' * e' ≠ 0 := by
  intro h
  have h1 : (1 - a1) * (1 - a2) = b' * e' := by linear_combination h
  have n1 : 1 - d ≤ ‖1 - a1‖ := by
    have := norm_sub_norm_le (1 : ℂ) a1; simp at this; linarith
  have n2 : 1 - d ≤ ‖1 - a2‖ := by
    have := norm_sub_norm_le (1 : ℂ) a2; simp at this; linarith
  have h2 : (1 - d) * (1 - d) ≤ ‖1 - a1‖ * ‖1 - a2‖ :=
    mul_le_mul n1 n2 (by linarith) (by linarith)
  have h3 : ‖b' * e'‖ ≤ d * d := by rw [norm_mul]; gcongr
  have h4 : ‖(1 - a1) * (1 - a2)‖ = ‖b' * e'‖ := by rw [h1]
  rw [norm_mul] at h4
  nlinarith

theorem actualSchurEntry_analytic_deriv_bound38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (i j : Bool × Sector n) (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) (z : ℂ) (hz : ‖z - spectralCenter n‖ < 1) :
    AnalyticAt ℂ (fun w : ℂ => actualSchurCoefficientAfterDext31 n i j (w, p)) z ∧
    ‖deriv (fun w : ℂ => actualSchurCoefficientAfterDext31 n i j (w, p)) z‖ ≤
      actualSchurGapParameter38 R n := by
  have hsub : Metric.ball (spectralCenter n) 1 ⊆ spectralDisk n := fun w hw => by
    have := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at this
    exact this.le
  have hz' : z ∈ Metric.ball (spectralCenter n) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]; exact hz
  have hder : ∀ w ∈ spectralDisk n, DifferentiableAt ℂ
      (fun w : ℂ => actualSchurCoefficientAfterDext31 n i j (w, p)) w :=
    fun w hw => (actualSchurEntry_hasDerivAt38V1 R hR n hn hlarge i j p w hw hp₁ hp₂
      ).differentiableAt
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => actualSchurCoefficientAfterDext31 n i j (w, p))
      (Metric.ball (spectralCenter n) 1) :=
    fun w hw => (hder w (hsub hw)).differentiableWithinAt
  refine ⟨hdiff.analyticAt (Metric.isOpen_ball.mem_nhds hz'), ?_⟩
  have hd0 : 0 ≤ actualSchurGapParameter38 R n := by
    have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
      freeResolventComplementaryInverseUniformConstant22_posV2_31
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    rw [actualSchurGapParameter38]; positivity
  have hlip : LipschitzOnWith (actualSchurGapParameter38 R n).toNNReal
      (fun w : ℂ => actualSchurCoefficientAfterDext31 n i j (w, p))
      (Metric.closedBall (spectralCenter n) 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hx' : x ∈ spectralDisk n := by
      have := Metric.mem_closedBall.mp hx; rw [dist_eq_norm] at this; exact this
    have hy' : y ∈ spectralDisk n := by
      have := Metric.mem_closedBall.mp hy; rw [dist_eq_norm] at this; exact this
    have := actualSchurEntry_lipschitz38V1 R hR n hn hlarge i j p hp₁ hp₂ x y hx' hy'
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hd0]
    exact this
  have hmem : Metric.closedBall (spectralCenter n) 1 ∈ nhds z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz') Metric.ball_subset_closedBall
  have := (hder z (hsub hz')).hasDerivAt.le_of_lipschitzOn hmem hlip
  simpa [Real.coe_toNNReal _ hd0] using this


/-- Local structure of the real-type determinant at a real point `r` of the window. -/
theorem actualSchurDet38_realType_local38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) (r : ℝ)
    (hrI : r ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2)) :
    AnalyticAt ℂ (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (r : ℂ) ∧
    (|actualSchurShiftedF38 n (w, actualH1Conj38 w) r| =
        actualSchurShiftedBeta38 n (w, actualH1Conj38 w) r →
      0 < actualSchurShiftedBeta38 n (w, actualH1Conj38 w) r →
      actualSchurDet38 n (w, actualH1Conj38 w) (r : ℂ) = 0 ∧
      deriv (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (r : ℂ) ≠ 0) ∧
    (actualSchurShiftedF38 n (w, actualH1Conj38 w) r = 0 →
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) r = 0 →
      analyticOrderAt (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (r : ℂ) = 2) := by
  obtain ⟨hKge, -, -, -⟩ := actualSchurShiftedRootsConstant38_ge
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hthr0 : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge (by positivity)) hthr
  obtain ⟨hn, hlarge, -, h14⟩ := actualSchurCenterThresholdConstant38_consequences R hR n hthr0
  have hd0 : 0 ≤ actualSchurGapParameter38 R n := by
    have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
      freeResolventComplementaryInverseUniformConstant22_posV2_31
    rw [actualSchurGapParameter38]; positivity
  have hd14 : actualSchurGapParameter38 R n ≤ 1 / 4 := h14
  set d := actualSchurGapParameter38 R n with hd
  set p : ActualSchurEffectiveH1PairV3_30 := (w, actualH1Conj38 w) with hp
  have hp₁ : ‖p.1‖ ≤ R := hw
  have hp₂ : ‖p.2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  have hc : spectralCenter n = ((Real.pi * n : ℝ) : ℂ) := by
    simp [spectralCenter]; ring
  have hrc : (r : ℂ) - spectralCenter n = ((r - Real.pi * n : ℝ) : ℂ) := by
    rw [hc]; push_cast; ring
  have hlt : ‖(r : ℂ) - spectralCenter n‖ < 1 := by
    rw [hrc, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    obtain ⟨h1, h2⟩ := hrI
    constructor <;> linarith
  have hdisk : (r : ℂ) ∈ spectralDisk n := hlt.le
  obtain ⟨hAa, hAd⟩ := actualSchurEntry_analytic_deriv_bound38 R hR n hn hlarge
    (true, resonantIndex n) (true, resonantIndex n) p hp₁ hp₂ r hlt
  obtain ⟨hDa, hDd⟩ := actualSchurEntry_analytic_deriv_bound38 R hR n hn hlarge
    (false, resonantIndex n) (false, resonantIndex n) p hp₁ hp₂ r hlt
  obtain ⟨hBa, hBd⟩ := actualSchurEntry_analytic_deriv_bound38 R hR n hn hlarge
    (true, resonantIndex n) (false, resonantIndex n) p hp₁ hp₂ r hlt
  obtain ⟨hEa, hEd⟩ := actualSchurEntry_analytic_deriv_bound38 R hR n hn hlarge
    (false, resonantIndex n) (true, resonantIndex n) p hp₁ hp₂ r hlt
  set A : ℂ → ℂ := fun z => actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (true, resonantIndex n) (z, p) with hA
  set D : ℂ → ℂ := fun z => actualSchurCoefficientAfterDext31 n
    (false, resonantIndex n) (false, resonantIndex n) (z, p) with hD
  set B : ℂ → ℂ := fun z => actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (false, resonantIndex n) (z, p) with hB
  set E : ℂ → ℂ := fun z => actualSchurCoefficientAfterDext31 n
    (false, resonantIndex n) (true, resonantIndex n) (z, p) with hE
  set g1 : ℂ → ℂ := fun z => z - spectralCenter n - A z with hg1
  set g2 : ℂ → ℂ := fun z => z - spectralCenter n - D z with hg2
  have hdet : (fun z : ℂ => actualSchurDet38 n p z) = fun z => g1 z * g2 z - B z * E z := rfl
  have hg1a : AnalyticAt ℂ g1 (r : ℂ) := (analyticAt_id.sub analyticAt_const).sub hAa
  have hg2a : AnalyticAt ℂ g2 (r : ℂ) := (analyticAt_id.sub analyticAt_const).sub hDa
  have hg1d : HasDerivAt g1 (1 - deriv A (r : ℂ)) (r : ℂ) :=
    ((hasDerivAt_id (r : ℂ)).sub_const _).sub hAa.differentiableAt.hasDerivAt
  have hg2d : HasDerivAt g2 (1 - deriv D (r : ℂ)) (r : ℂ) :=
    ((hasDerivAt_id (r : ℂ)).sub_const _).sub hDa.differentiableAt.hasDerivAt
  have hdetA : AnalyticAt ℂ (fun z : ℂ => actualSchurDet38 n p z) (r : ℂ) := by
    rw [hdet]; exact (hg1a.mul hg2a).sub (hBa.mul hEa)
  -- values at the real point
  have him := actualSchurAlpha38_im_eq_zero_realType38 R hR n hthr0 r hdisk w hw
  have hdiag := actualSchurCoefficient_equal_diagonal38 R hR n hn hlarge (r : ℂ) p hdisk hp₁ hp₂
  have hEr := actualSchurOffDiagonal_star_realType38 R hR n hthr0 r hdisk w hw
  have hAr : A (r : ℂ) = ((actualSchurAlpha38 n p (r : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]; rfl
    · simp only [Complex.ofReal_im]; exact him
  have hDr : D (r : ℂ) = A (r : ℂ) := hdiag
  have hg1r : g1 (r : ℂ) = ((actualSchurShiftedF38 n p r : ℝ) : ℂ) := by
    simp only [hg1, actualSchurShiftedF38]
    rw [hAr, hc]; push_cast; ring
  have hg2r : g2 (r : ℂ) = g1 (r : ℂ) := by
    simp only [hg1, hg2]; rw [hDr]
  have hEr' : E (r : ℂ) = star (B (r : ℂ)) := hEr
  have hBn : ‖B (r : ℂ)‖ = actualSchurShiftedBeta38 n p r := rfl
  have hEn : ‖E (r : ℂ)‖ = actualSchurShiftedBeta38 n p r := by rw [hEr', norm_star]; rfl
  have hg1n : ‖g1 (r : ℂ)‖ = |actualSchurShiftedF38 n p r| := by
    rw [hg1r, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨hdetA, ?_, ?_⟩
  · intro habs hβpos
    have hder : HasDerivAt (fun z : ℂ => actualSchurDet38 n p z)
        ((1 - deriv A (r : ℂ)) * g2 (r : ℂ) + g1 (r : ℂ) * (1 - deriv D (r : ℂ)) -
          (deriv B (r : ℂ) * E (r : ℂ) + B (r : ℂ) * deriv E (r : ℂ))) (r : ℂ) := by
      rw [hdet]
      exact (hg1d.mul hg2d).sub (hBa.differentiableAt.hasDerivAt.mul
        hEa.differentiableAt.hasDerivAt)
    constructor
    · -- value
      have h0 : actualSchurDet38 n p (r : ℂ) = g1 (r : ℂ) * g2 (r : ℂ) - B (r : ℂ) * E (r : ℂ) := rfl
      rw [h0, hg2r, hEr', hg1r]
      have hbb : B (r : ℂ) * star (B (r : ℂ)) = ((‖B (r : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hbb, hBn, ← habs, ← Complex.ofReal_mul, ← Complex.ofReal_sub, sq_abs]
      simp [sq]
    · rw [hder.deriv]
      rw [hg2r]
      have := openGap_alg38 (g1 (r : ℂ)) (B (r : ℂ)) (E (r : ℂ)) (deriv A (r : ℂ))
        (deriv D (r : ℂ)) (deriv B (r : ℂ)) (deriv E (r : ℂ))
        (actualSchurShiftedBeta38 n p r) d hβpos hd14 (by rw [hg1n]; exact habs) hBn hEn
        hAd hDd hBd hEd
      intro h; apply this; linear_combination h
  · intro hF hβ
    have hg1z : g1 (r : ℂ) = 0 := by rw [hg1r, hF]; simp
    have hg2z : g2 (r : ℂ) = 0 := by rw [hg2r, hg1z]
    have hBz : B (r : ℂ) = 0 := norm_eq_zero.mp (by rw [hBn, hβ])
    have hEz : E (r : ℂ) = 0 := norm_eq_zero.mp (by rw [hEn, hβ])
    rw [hdet]
    refine analyticOrderAt_eq_two_of_factored38 g1 g2 B E (r : ℂ) hg1a hg2a hBa hEa
      hg1z hg2z hBz hEz ?_
    rw [hg1d.deriv, hg2d.deriv]
    exact closedGap_alg38 _ _ _ _ d hd0 hd14 hAd hDd hBd hEd


/-- F03.07, multiplicity: for a real-type pair `(w, w̄)`, `‖w‖ ≤ R`, `|n| ≥ K R³`, there are
real roots `λ⁻ ≤ λ⁺` of `F ± β` in the window such that the zeros of the analytic function
`z ↦ actualSchurDet38 n (w, w̄) z` in the closed disk `|z - nπ| ≤ 1` are exactly
`{λ⁻, λ⁺}`; if `λ⁻ < λ⁺` both are simple (`deriv ≠ 0`, `analyticOrderAt = 1`); if
`λ⁻ = λ⁺` the zero has `analyticOrderAt = 2`. -/
theorem actualSchurDet38_realType_multiplicity38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    ∃ lp lm : ℝ, lm ≤ lp ∧
      (lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0) ∧
      (lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0) ∧
      (∀ z : ℂ, z ∈ spectralDisk n →
        (actualSchurDet38 n (w, actualH1Conj38 w) z = 0 ↔ (z = (lp : ℂ) ∨ z = (lm : ℂ)))) ∧
      AnalyticAt ℂ (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (lp : ℂ) ∧
      AnalyticAt ℂ (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (lm : ℂ) ∧
      (lm < lp →
        (deriv (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (lm : ℂ) ≠ 0 ∧
          deriv (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (lp : ℂ) ≠ 0) ∧
        analyticOrderAt (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (lm : ℂ) = 1 ∧
        analyticOrderAt (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (lp : ℂ) = 1) ∧
      (lm = lp →
        analyticOrderAt (fun z : ℂ => actualSchurDet38 n (w, actualH1Conj38 w) z) (lp : ℂ) = 2) := by
  obtain ⟨hKge, -, -, -⟩ := actualSchurShiftedRootsConstant38_ge
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hthr0 : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge (by positivity)) hthr
  obtain ⟨lp, lm, ⟨hlpI, hlp0, hlpu⟩, ⟨hlmI, hlm0, hlmu⟩, hz⟩ :=
    actualSchurCoordinateEigenvalues_realType38 R hR n hthr w hw
  have hord := actualSourceSectorRoots_ordered_realType38 R hR n hthr w hw lp lm hlpI hlp0
    hlmI hlm0
  have hp₂ : ‖(w, actualH1Conj38 w).2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  refine ⟨lp, lm, hord.2.2, ⟨hlpI, hlp0⟩, ⟨hlmI, hlm0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hzD
    rw [← actualSchurSecularDet38_eq_actualSchurDet38 n z, ← hz z hzD,
      actualSchur_eigenvalue_iff_secularDet_zero_threshold38V1 R hR n hthr0 z
        (w, actualH1Conj38 w) hzD hw hp₂]
  · exact (actualSchurDet38_realType_local38 R hR n hthr w hw lp hlpI).1
  · exact (actualSchurDet38_realType_local38 R hR n hthr w hw lm hlmI).1
  · intro hlt
    obtain ⟨-, hlpo, -⟩ := actualSchurDet38_realType_local38 R hR n hthr w hw lp hlpI
    obtain ⟨-, hlmo, -⟩ := actualSchurDet38_realType_local38 R hR n hthr w hw lm hlmI
    have hβp : 0 < actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp := by
      by_contra hne
      have h0 : actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0 :=
        le_antisymm (not_lt.mp hne) (norm_nonneg _)
      have hF : actualSchurShiftedF38 n (w, actualH1Conj38 w) lp = 0 := by linarith
      have := hlmu lp hlpI (by linarith)
      linarith
    have hβm : 0 < actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm := by
      by_contra hne
      have h0 : actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0 :=
        le_antisymm (not_lt.mp hne) (norm_nonneg _)
      have := hlpu lm hlmI (by linarith)
      linarith
    have hp := hlpo (by
      have : actualSchurShiftedF38 n (w, actualH1Conj38 w) lp =
        actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp := by linarith
      rw [this]; exact abs_of_nonneg hβp.le) hβp
    have hm := hlmo (by
      have : actualSchurShiftedF38 n (w, actualH1Conj38 w) lm =
        -actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm := by linarith
      rw [this, abs_neg]; exact abs_of_nonneg hβm.le) hβm
    refine ⟨⟨hm.2, hp.2⟩, ?_, ?_⟩
    · exact analyticOrderAt_eq_one_of_deriv38 _ _
        (actualSchurDet38_realType_local38 R hR n hthr w hw lm hlmI).1 hm.1 hm.2
    · exact analyticOrderAt_eq_one_of_deriv38 _ _
        (actualSchurDet38_realType_local38 R hR n hthr w hw lp hlpI).1 hp.1 hp.2
  · intro heq
    obtain ⟨-, -, hclosed⟩ := actualSchurDet38_realType_local38 R hR n hthr w hw lp hlpI
    subst heq
    have hβ : actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0 := by linarith
    exact hclosed (by linarith) hβ

end NlsGge.Schur

