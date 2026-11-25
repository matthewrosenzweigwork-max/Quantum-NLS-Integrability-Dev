import NlsGge.Schur.ActualSchurElimination38V1
import NlsGge.Schur.ActualSchurRealTypeDeterminant38V1
import NlsGge.Schur.ActualSchurShiftedRoots38V1
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1

/-!
# Eigenvalues of the coordinate operator in the disk for real-type potentials

Source: `paper/v2.tex` lines 1154-1158.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The secular determinant used in the elimination theorem is the determinant of
the real-type factorization (bridge between the two argument orders). -/
theorem actualSchurSecularDet38_eq_actualSchurDet38 (n : ℤ)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30) :
    actualSchurSecularDet38 n z p = actualSchurDet38 n p z := rfl

/-- Conjugating a symmetric operator by a unitary equivalence keeps it symmetric. -/
theorem transportedSymm38 {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (e : H ≃ₗᵢ[ℂ] K) (V : H →L[ℂ] H) (hV : ∀ a b, inner ℂ a (V b) = inner ℂ (V a) b)
    (y y' : K) :
    inner ℂ y (e (V (e.symm y'))) = inner ℂ (e (V (e.symm y))) y' := by
  have h := e.inner_map_map (e.symm y) (V (e.symm y'))
  have h2 := e.inner_map_map (V (e.symm y)) (e.symm y')
  rw [e.apply_symm_apply] at h h2
  rw [h, h2]
  exact hV _ _

/-- The coordinate potential `Ṽ` of a real-type pair is symmetric for the
`ℓ²` inner product. -/
theorem actualSchurCoordinatePotential_symm_realType38 (n : ℤ)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (y y' : SectorSquare n) :
    inner ℂ y (actualSchurCoordinatePotential38 n (w, actualH1Conj38 w) y') =
      inner ℂ (actualSchurCoordinatePotential38 n (w, actualH1Conj38 w) y) y' := by
  have hVe : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w) =
      coveredH1ParityPairPotential
        (physicalH1ComplexCarrierToL2Actual22 w)
        (physicalH1ComplexCarrierToL2Actual22 (actualH1Conj38 w))
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable (actualH1Conj38 w)) n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n (w, actualH1Conj38 w)
  have hVad : ContinuousLinearMap.adjoint
      (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)) =
      actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w) := by
    rw [hVe]
    exact coveredH1ParityPairPotential_adjoint_of_star38 _ _ _ _
      (physicalH1_conj38 w) n
  set V := actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)
    with hV
  have hsym : ∀ a b : ParityPair n, inner ℂ a (V b) = inner ℂ (V a) b := by
    intro a b
    have := ContinuousLinearMap.adjoint_inner_right V a b
    rw [hVad] at this
    exact this
  unfold actualSchurCoordinatePotential38
  rw [toSq_apply38, toSq_apply38]
  rw [← hV]
  exact transportedSymm38 (parityPairRepr n) V hsym y y'

/-- The free coordinate Dirac operator is symmetric on its domain:
`⟨y, L₀ y⟩ = ⟨L₀ y, y⟩`, because every coordinate multiplier `spectralCenter m = mπ`
is real. -/
theorem freeCoordinateDirac_inner_symm38 (n : ℤ) (x : freeWeightedDomainPointwise n) :
    inner ℂ x.val (freeCoordinateDirac n x) = inner ℂ (freeCoordinateDirac n x) x.val := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [freeCoordinateDirac_apply]
  simp only [RCLike.inner_apply, map_mul, spectralCenter, Complex.conj_ofReal]
  simp
  ring

/-- (a) Non-real exclusion: for a real-type potential pair `(w, w̄)` with `‖w‖ ≤ R`
and `|n| ≥ C R³`, every zero of the Schur determinant in the spectral disk is real. -/
theorem actualSchurDet38_realType_zero_im38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hdet : actualSchurDet38 n (w, actualH1Conj38 w) z = 0) : z.im = 0 := by
  have hp₂ : ‖(w, actualH1Conj38 w).2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  obtain ⟨x, hx0, heq⟩ := (actualSchur_eigenvalue_iff_secularDet_zero_threshold38V1 R hR n hthr z
    (w, actualH1Conj38 w) hz hw hp₂).mpr hdet
  have h1 := congrArg (inner ℂ x.val) heq
  rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_zero_right] at h1
  have hnorm : inner ℂ x.val x.val = (((‖x.val‖ ^ 2 : ℝ)) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  have hL := freeCoordinateDirac_inner_symm38 n x
  have hV := actualSchurCoordinatePotential_symm_realType38 n w x.val x.val
  have hs : starRingEnd ℂ (inner ℂ x.val (freeCoordinateDirac n x) +
      inner ℂ x.val (actualSchurCoordinatePotential38 n (w, actualH1Conj38 w) x.val)) =
      inner ℂ x.val (freeCoordinateDirac n x) +
      inner ℂ x.val (actualSchurCoordinatePotential38 n (w, actualH1Conj38 w) x.val) := by
    rw [map_add, inner_conj_symm, inner_conj_symm, ← hL, ← hV]
  have him := Complex.conj_eq_iff_im.mp hs
  have hz' : z * (((‖x.val‖ ^ 2 : ℝ)) : ℂ) = inner ℂ x.val (freeCoordinateDirac n x) +
      inner ℂ x.val (actualSchurCoordinatePotential38 n (w, actualH1Conj38 w) x.val) := by
    rw [hnorm] at h1
    linear_combination h1
  have him2 := congrArg Complex.im hz'
  rw [Complex.im_mul_ofReal, him] at him2
  have hne : ‖x.val‖ ^ 2 ≠ 0 := by
    have : x.val ≠ 0 := hx0
    positivity
  exact (mul_eq_zero.mp him2).resolve_right hne

/-- `F_n(x) = x - nπ - Re α_n(x)` of `actualSchurShiftedRoots38V1`. -/
def actualSchurShiftedF38 (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (x : ℝ) : ℝ :=
  x - Real.pi * n - (actualSchurAlpha38 n p x).re

/-- `β_n(x) = |b_n(x)|` of `actualSchurShiftedRoots38V1`. -/
def actualSchurShiftedBeta38 (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (x : ℝ) : ℝ :=
  ‖actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (false, resonantIndex n) ((x : ℂ), p)‖

/-- Size bounds on the whole disk under the shifted-root threshold:
`|α_n| ≤ 1/8` and `|b_n| ≤ 1/3`. -/
theorem actualSchurDiskBounds38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurAlpha38 n p z‖ ≤ 1 / 8 ∧
    ‖actualSchurCoefficientAfterDext31 n
      (true, resonantIndex n) (false, resonantIndex n) (z, p)‖ ≤ 1 / 3 := by
  obtain ⟨hKge, hB, hK3, hT⟩ := actualSchurShiftedRootsConstant38_ge
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR3 : 0 ≤ R ^ 3 := by positivity
  have hthr0 : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge hR3) hthr
  obtain ⟨hn, hlarge, h18, h14⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr0
  refine ⟨le_trans (actualSchurAlpha_boundAfterDextV6_32 R hR n hn hlarge z p hz hp₁ hp₂) h18, ?_⟩
  set K := actualSchurShiftedRootsConstant38 with hK
  have hKM : 3 * (1 + actualSchurBremConstant38) ≤ K := by
    rw [hK]; unfold actualSchurShiftedRootsConstant38; linarith
  set M := actualSchurBremConstant38 with hM
  set N := |(n : ℝ)| with hN
  have hN1 : 1 ≤ N := hn
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hKpos : 0 < K := by linarith
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
  have hFourier : ‖p.1 n‖ ≤ R / N := by
    rw [le_div_iff₀ hNpos]
    have := weightedH1_fourier_norm_le38V1 p.1 n
    nlinarith [norm_nonneg (p.1 n)]
  have h := actualSchurOffDiagonal_sub_fourier_bound38V1 R hR n hn hlarge
    z p hz hp₁ hp₂
  rw [physicalH1ComplexCarrierToL2Actual22_fourier] at h
  have h' : ‖actualSchurCoefficientAfterDext31 n
      (true, resonantIndex n) (false, resonantIndex n) (z, p) - p.1 n‖ ≤
      M * R ^ 4 / N ^ 2 := by
    rw [hM]; unfold actualSchurBremConstant38; exact h
  have h2 := norm_sub_norm_le (actualSchurCoefficientAfterDext31 n
      (true, resonantIndex n) (false, resonantIndex n) (z, p)) (p.1 n)
  have h3 : M * R ^ 4 / N ^ 2 ≤ M * (1 / K) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hR4N hB
  have h4 : M * (1 / K) + 1 / K = (1 + M) / K := by ring
  linarith

/-- (b) Real zeros of the Schur determinant in the disk, for a real-type pair: the
determinant vanishes at a real `x` of the disk iff `x ∈ [nπ - 1/2, nπ + 1/2]` and
`F_n(x) - β_n(x) = 0` or `F_n(x) + β_n(x) = 0`. -/
theorem actualSchurDet38_realType_real_zero_iff38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R)
    (x : ℝ) (hx : (x : ℂ) ∈ spectralDisk n) :
    actualSchurDet38 n (w, actualH1Conj38 w) (x : ℂ) = 0 ↔
      (x ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        (actualSchurShiftedF38 n (w, actualH1Conj38 w) x -
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) x = 0 ∨
          actualSchurShiftedF38 n (w, actualH1Conj38 w) x +
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) x = 0)) := by
  obtain ⟨hKge, -, -, -⟩ := actualSchurShiftedRootsConstant38_ge
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR3 : 0 ≤ R ^ 3 := by positivity
  have hthr0 : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge hR3) hthr
  have hp₂ : ‖(w, actualH1Conj38 w).2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  obtain ⟨hα, hβ⟩ := actualSchurDiskBounds38 R hR n hthr (x : ℂ) hx (w, actualH1Conj38 w) hw hp₂
  have hαre : |(actualSchurAlpha38 n (w, actualH1Conj38 w) x).re| ≤ 1 / 8 :=
    le_trans (Complex.abs_re_le_norm _) hα
  have hdisk : |x - Real.pi * n| ≤ 1 := by
    have h : ‖(x : ℂ) - spectralCenter n‖ ≤ 1 := hx
    have he : (x : ℂ) - spectralCenter n = ((x - Real.pi * n : ℝ) : ℂ) := by
      simp [spectralCenter]
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hfac := actualSchurDet38_realType_factor R hR n hthr0 x hx w hw
  change _ = (((actualSchurShiftedF38 n (w, actualH1Conj38 w) x -
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) x) *
      (actualSchurShiftedF38 n (w, actualH1Conj38 w) x +
      actualSchurShiftedBeta38 n (w, actualH1Conj38 w) x) : ℝ) : ℂ) at hfac
  rw [hfac, Complex.ofReal_eq_zero, mul_eq_zero]
  have hβ' : actualSchurShiftedBeta38 n (w, actualH1Conj38 w) x ≤ 1 / 3 := hβ
  have hβ0 : 0 ≤ actualSchurShiftedBeta38 n (w, actualH1Conj38 w) x := norm_nonneg _
  have hFdef : actualSchurShiftedF38 n (w, actualH1Conj38 w) x =
      x - Real.pi * n - (actualSchurAlpha38 n (w, actualH1Conj38 w) x).re := rfl
  have hαb := abs_le.mp hαre
  constructor
  · intro h
    refine ⟨?_, h⟩
    rcases h with h | h
    · constructor <;> linarith
    · constructor <;> linarith
  · exact fun h => h.2

/-- (c) For a real-type pair `(w, w̄)` with `‖w‖ ≤ R` and `|n| ≥ K R³`, the eigenvalues
`z ∈ spectralDisk n` of the coordinate operator `L₀ + Ṽ` (nonzero solutions `x` of the
domain eigenvalue equation `z x - L₀ x - Ṽ x = 0`) are exactly the two real numbers
`λ⁺` (the unique zero of `F - β` in `[nπ - 1/2, nπ + 1/2]`) and `λ⁻` (the unique zero
of `F + β` there); `λ⁺ = λ⁻` is allowed.  No multiplicity or labelling is claimed. -/
theorem actualSchurCoordinateEigenvalues_realType38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurShiftedRootsConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    ∃ lp lm : ℝ,
      (lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lp -
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lp = 0 ∧
        ∀ y : ℝ, y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
          actualSchurShiftedF38 n (w, actualH1Conj38 w) y -
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) y = 0 → y = lp) ∧
      (lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) ∧
        actualSchurShiftedF38 n (w, actualH1Conj38 w) lm +
          actualSchurShiftedBeta38 n (w, actualH1Conj38 w) lm = 0 ∧
        ∀ y : ℝ, y ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) →
          actualSchurShiftedF38 n (w, actualH1Conj38 w) y +
            actualSchurShiftedBeta38 n (w, actualH1Conj38 w) y = 0 → y = lm) ∧
      ∀ z : ℂ, z ∈ spectralDisk n →
        ((∃ x : freeWeightedDomainPointwise n, x.val ≠ 0 ∧
            z • x.val - freeCoordinateDirac n x -
              actualSchurCoordinatePotential38 n (w, actualH1Conj38 w) x.val = 0) ↔
          (z = (lp : ℂ) ∨ z = (lm : ℂ))) := by
  obtain ⟨hKge, -, -, -⟩ := actualSchurShiftedRootsConstant38_ge
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR3 : 0 ≤ R ^ 3 := by positivity
  have hthr0 : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right hKge hR3) hthr
  have hp₂ : ‖(w, actualH1Conj38 w).2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  obtain ⟨⟨lp, ⟨hlpI, hlp0⟩, hlpu⟩, ⟨lm, ⟨hlmI, hlm0⟩, hlmu⟩⟩ :=
    actualSchurShiftedRoots38V1 R hR n hthr (w, actualH1Conj38 w) hw hp₂
  refine ⟨lp, lm, ⟨hlpI, hlp0, fun y hy h => hlpu y ⟨hy, h⟩⟩,
    ⟨hlmI, hlm0, fun y hy h => hlmu y ⟨hy, h⟩⟩, fun z hz => ?_⟩
  rw [actualSchur_eigenvalue_iff_secularDet_zero_threshold38V1 R hR n hthr0 z
    (w, actualH1Conj38 w) hz hw hp₂]
  change actualSchurDet38 n (w, actualH1Conj38 w) z = 0 ↔ _
  constructor
  · intro hdet
    have him := actualSchurDet38_realType_zero_im38 R hR n hthr0 w hw z hz hdet
    have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hzr] at hdet hz
    rw [actualSchurDet38_realType_real_zero_iff38 R hR n hthr w hw z.re hz] at hdet
    obtain ⟨hI, h | h⟩ := hdet
    · left; rw [hzr, hlpu z.re ⟨hI, h⟩]
    · right; rw [hzr, hlmu z.re ⟨hI, h⟩]
  · rintro (rfl | rfl)
    · exact (actualSchurDet38_realType_real_zero_iff38 R hR n hthr w hw lp hz).mpr
        ⟨hlpI, Or.inl hlp0⟩
    · exact (actualSchurDet38_realType_real_zero_iff38 R hR n hthr w hw lm hz).mpr
        ⟨hlmI, Or.inr hlm0⟩

end NlsGge.Schur
