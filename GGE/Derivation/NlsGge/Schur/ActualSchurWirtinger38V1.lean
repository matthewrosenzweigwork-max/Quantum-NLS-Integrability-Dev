import NlsGge.Schur.ActualSchurQnRealDerivative38V1

/-!
# NEW-F04.08: Wirtinger derivative on the real-type subspace

Source: `paper/v2.tex` lines 1180-1181 ("The derivative is the Wirtinger
derivative, equivalently the derivative of the complexified expression with
respect to `(u₁)_n`, keeping `u₂` fixed").  For the real map
`Rem(v) = q_n(v, v̄) - v_n` on the H¹ carrier and every direction `w`,
`½ (dRem(u)[w] - i · dRem(u)[i w]) = Dq_n(u, ū)[(w, 0)] - w_n`.
With `w = δ_n` this identifies the Wirtinger derivative `∂q_n/∂u_n - 1` with the
complexified derivative in `(u₁)_n` at fixed `u₂`.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

local notation "H1" => WeightedHilbert (sobolevModeWeight (1 : ℝ))

theorem actualH1Conj38_complex_smul (c : ℂ) (x : H1) :
    actualH1Conj38 (c • x) = star c • actualH1Conj38 x := by
  apply Subtype.ext
  funext k
  change star (c * (x : ℤ → ℂ) (-k)) = star c * star ((x : ℤ → ℂ) (-k))
  rw [star_mul', mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem actualSchurQnRealRemainder38_wirtinger
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (u : H1) (hu : ‖u‖ < R) (w : H1) :
    (1 / 2 : ℂ) * (fderiv ℝ (actualSchurQnRealRemainder38 R n) u w -
        Complex.I * fderiv ℝ (actualSchurQnRealRemainder38 R n) u (Complex.I • w)) =
      fderiv ℂ (actualSchurQn38 R n) (u, actualH1Conj38 u) (w, 0) - w n := by
  have hq := (actualSchurQn38_differentiableAt R hR n hthr (u, actualH1Conj38 u) hu
    (by rw [actualH1Conj38_norm]; exact hu)).hasFDerivAt
  set L := fderiv ℂ (actualSchurQn38 R n) (u, actualH1Conj38 u) with hL
  have hqR := hq.restrictScalars ℝ
  have hqR' : HasFDerivAt (actualSchurQn38 R n) (L.restrictScalars ℝ)
      (actualRealTypeEmbedding38 u) := hqR
  have hι := actualRealTypeEmbedding38.hasFDerivAt (x := u)
  have h1 := HasFDerivAt.comp (g := actualSchurQn38 R n)
    (f := fun v : H1 => actualRealTypeEmbedding38 v) u hqR' hι
  have h2 := ((actualH1CoordinateCLM38 n).restrictScalars ℝ).hasFDerivAt (x := u)
  have h := h1.sub h2
  have h' := h.congr_of_eventuallyEq (f₁ := actualSchurQnRealRemainder38 R n)
    (Filter.Eventually.of_forall fun v => by
      simp only [Pi.sub_apply, Function.comp, actualSchurQnRealRemainder38,
        actualRealTypeEmbedding38_apply, ContinuousLinearMap.coe_restrictScalars',
        actualH1CoordinateCLM38_apply])
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', actualRealTypeEmbedding38_apply,
    actualH1CoordinateCLM38_apply]
  rw [actualH1Conj38_complex_smul]
  have hsplit1 : ((w, actualH1Conj38 w) : ActualSchurEffectiveH1PairV3_30) =
      (w, 0) + (0, actualH1Conj38 w) := by simp
  have hsplit2 : ((Complex.I • w, star Complex.I • actualH1Conj38 w) :
      ActualSchurEffectiveH1PairV3_30) =
      Complex.I • ((w, 0) : ActualSchurEffectiveH1PairV3_30) +
        star Complex.I • ((0, actualH1Conj38 w) : ActualSchurEffectiveH1PairV3_30) := by
    simp
  rw [hsplit1, hsplit2, map_add, map_add, map_smul, map_smul]
  have hIw : (Complex.I • w : H1) n = Complex.I * w n := rfl
  rw [hIw, Complex.star_def, Complex.conj_I, smul_eq_mul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

end NlsGge.Schur
