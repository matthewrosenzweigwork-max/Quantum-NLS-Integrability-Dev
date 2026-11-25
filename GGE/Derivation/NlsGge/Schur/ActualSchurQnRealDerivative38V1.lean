import NlsGge.Schur.ActualSchurRealTypeCenter38V1

/-!
# F:eq:qCauchy, second inequality, as a real Fréchet derivative bound (NEW-F03.06)

The complex H¹ carrier `WeightedHilbert (sobolevModeWeight 1)` is regarded as a
real normed space (restriction of scalars, same norm).  For `‖u‖_{H¹} < R`
(threshold imposed at radius `4R`, as in the source) the real map
`v ↦ q_n(v, v̄) - v_n` is real-differentiable at `u` and its real-linear
derivative has operator norm at most `C (4R)^4/n^2 / R` (`= 256 C R^3/n^2`).
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace ENNReal
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

local notation "H1" => WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-- The `n`-th Fourier coordinate on the complex H¹ carrier as a complex CLM. -/
def actualH1CoordinateCLM38 (n : ℤ) : H1 →L[ℂ] ℂ := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let ev : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n
  let iso : H1 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
    (weightedIsometry (sobolevModeWeight (1 : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap
  exact ((Real.sqrt (sobolevModeWeight (1 : ℝ) n) : ℂ)⁻¹) • (ev.comp iso)

theorem actualH1CoordinateCLM38_apply (n : ℤ) (x : H1) :
    actualH1CoordinateCLM38 n x = x n := by
  change (Real.sqrt (sobolevModeWeight (1 : ℝ) n) : ℂ)⁻¹ *
    ((weightedIsometry (sobolevModeWeight (1 : ℝ))) x) n = _
  rw [weightedIsometry_apply]
  simp only [weightedCoordinates]
  rw [← mul_assoc, inv_mul_cancel₀ (weightSqrt_ne_zero (sobolevModeWeight (1 : ℝ)) n),
    one_mul]

theorem actualH1Conj38_add (x y : H1) :
    actualH1Conj38 (x + y) = actualH1Conj38 x + actualH1Conj38 y := by
  apply Subtype.ext
  funext k
  change star ((x : ℤ → ℂ) (-k) + (y : ℤ → ℂ) (-k)) =
    star ((x : ℤ → ℂ) (-k)) + star ((y : ℤ → ℂ) (-k))
  rw [star_add]

theorem actualH1Conj38_real_smul (c : ℝ) (x : H1) :
    actualH1Conj38 (c • x) = c • actualH1Conj38 x := by
  rw [← Complex.coe_smul, ← Complex.coe_smul]
  apply Subtype.ext
  funext k
  change star ((c : ℂ) * (x : ℤ → ℂ) (-k)) = (c : ℂ) * star ((x : ℤ → ℂ) (-k))
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]

/-- The real-linear embedding `u ↦ (u, ū)` of the real H¹ carrier into the
independent complex pair space; it preserves norms. -/
def actualRealTypeEmbedding38 : H1 →L[ℝ] ActualSchurEffectiveH1PairV3_30 :=
  LinearMap.mkContinuous
    { toFun := fun v => (v, actualH1Conj38 v)
      map_add' := fun x y => by
        simp only [actualH1Conj38_add, Prod.mk_add_mk]
      map_smul' := fun c x => by
        simp only [actualH1Conj38_real_smul, RingHom.id_apply, Prod.smul_mk] }
    1 (fun v => by
      change ‖((v, actualH1Conj38 v) : ActualSchurEffectiveH1PairV3_30)‖ ≤ 1 * ‖v‖
      rw [Prod.norm_def, actualH1Conj38_norm, max_self, one_mul])

theorem actualRealTypeEmbedding38_apply (v : H1) :
    actualRealTypeEmbedding38 v = (v, actualH1Conj38 v) := rfl

/-- `v ↦ q_n(v, v̄) - v_n` on the real H¹ carrier. -/
def actualSchurQnRealRemainder38 (R : ℝ) (n : ℤ) (v : H1) : ℂ :=
  actualSchurQn38 R n (v, actualH1Conj38 v) - v n

set_option backward.isDefEq.respectTransparency false in
theorem actualSchurQnRealRemainder38_differentiableAt
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (u : H1) (hu : ‖u‖ < R) :
    DifferentiableAt ℝ (actualSchurQnRealRemainder38 R n) u := by
  have hq := actualSchurQn38_differentiableAt R hR n hthr (u, actualH1Conj38 u) hu
    (by rw [actualH1Conj38_norm]; exact hu)
  have hqR := hq.restrictScalars ℝ
  have hι : DifferentiableAt ℝ (fun v : H1 => actualRealTypeEmbedding38 v) u :=
    actualRealTypeEmbedding38.differentiableAt
  have hqR' : DifferentiableAt ℝ (actualSchurQn38 R n) (actualRealTypeEmbedding38 u) := hqR
  have h1 : DifferentiableAt ℝ
      (fun v : H1 => actualSchurQn38 R n (actualRealTypeEmbedding38 v)) u :=
    DifferentiableAt.comp (g := actualSchurQn38 R n)
      (f := fun v : H1 => actualRealTypeEmbedding38 v) u hqR' hι
  have h2 : DifferentiableAt ℝ (fun v : H1 => actualH1CoordinateCLM38 n v) u :=
    ((actualH1CoordinateCLM38 n).restrictScalars ℝ).differentiableAt
  have h := h1.sub h2
  convert h using 1
  funext v
  simp only [actualSchurQnRealRemainder38, actualRealTypeEmbedding38_apply,
    actualH1CoordinateCLM38_apply]
  rfl

/-- F:eq:qCauchy, second inequality: the real-linear derivative of
`v ↦ q_n(v, v̄) - v_n` at `‖u‖_{H¹} ≤ R` has operator norm at most
`C (4R)^4/n^2/R`, with the source threshold at radius `4R`. -/
theorem actualSchurQnRealRemainder38_fderiv_norm_le
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)|)
    (u : H1) (hu : ‖u‖ ≤ R) :
    ‖fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) u‖ ≤
      actualSchurBremConstant38 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2 / R := by
  have h4R : 1 ≤ 4 * R := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hdiff := actualSchurQnRealRemainder38_differentiableAt (4 * R) h4R n hthr u
    (by linarith)
  set M := actualSchurBremConstant38 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2 / R with hM
  have hM0 : 0 ≤ M := by
    have hC : 0 ≤ actualSchurBremConstant38 := by
      unfold actualSchurBremConstant38
      have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
        freeResolventComplementaryInverseUniformConstant22_posV2_31
      have hS : 0 ≤ freeResolventSchurUniformConstant := by
        unfold freeResolventSchurUniformConstant; positivity
      have hMp := physicalH1MultiplierConstant_pos
      positivity
    rw [hM]; positivity
  -- unit directions
  have hunit : ∀ w : H1, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) u w‖ ≤ M := by
    intro w hw
    obtain ⟨L, hL, hLb⟩ :=
      actualSchurQnRealType_directional_bound38 R hR n hthr u w hu hw
    have hline : HasDerivAt (fun t : ℝ => u + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
    have hd' : HasFDerivAt (actualSchurQnRealRemainder38 (4 * R) n)
        (fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) u) (u + (0 : ℝ) • w) := by
      rw [zero_smul, add_zero]; exact hdiff.hasFDerivAt
    have hcomp := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => u + t • w) (0 : ℝ) hd' hline
    have hfun : (actualSchurQnRealRemainder38 (4 * R) n ∘ fun t : ℝ => u + t • w) =
        (fun t : ℝ => actualSchurQn38 (4 * R) n
          (u + (t : ℂ) • w, actualH1Conj38 (u + (t : ℂ) • w)) -
          (u + (t : ℂ) • w : H1) n) := by
      funext t
      simp only [Function.comp, actualSchurQnRealRemainder38, Complex.coe_smul]
    rw [hfun] at hcomp
    rw [hcomp.unique hL]
    exact hLb
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 (fun w => ?_)
  by_cases hw0 : w = 0
  · simp [hw0]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let w' : H1 := (‖w‖⁻¹ : ℝ) • w
  have hw' : ‖w'‖ ≤ 1 := by
    simp only [w', norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [inv_mul_cancel₀ hwpos.ne']
  have hw'eq : w = ‖w‖ • w' := by
    simp only [w', smul_smul, mul_inv_cancel₀ hwpos.ne', one_smul]
  have h := hunit w' hw'
  rw [hw'eq, ContinuousLinearMap.map_smul, norm_smul, Real.norm_eq_abs, abs_norm]
  calc ‖w‖ * ‖(fderiv ℝ (actualSchurQnRealRemainder38 (4 * R) n) u) w'‖ ≤ ‖w‖ * M :=
        mul_le_mul_of_nonneg_left h hwpos.le
    _ = M * ‖w‖ := by ring
    _ = M * ‖‖w‖ • w'‖ := by rw [← hw'eq]

end NlsGge.Schur
