import NlsGge.Schur.ActualSchurCenterContraction38V1

/-!
# Spectral derivative of every actual resonant Schur entry (F:eq:lambda, entrywise)

Source: `paper/v2.tex` lines 1107-1113.  Each of the four actual entries
`λ ↦ ⟪e_i, A_n(λ) e_j⟫` has derivative `⟪e_i, -(G̃_n G_n) e_j⟫`, of size at most
`C R^4/n^2` on the original spectral disk.  In particular `b_n` is
`C R^4/n^2`-Lipschitz there (used for `|b_n|` in F03.08).
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem actualSchurEntry_hasDerivAt38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (i j : Bool × Sector n)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    HasDerivAt (fun w : ℂ => actualSchurCoefficientAfterDext31 n i j (w, p))
      (actualSchurEntryFunctional31 n i j
        (-(actualSchurGreenDerivativeProductV3_31 n z p hz))) z := by
  let E : Type := ParityPair n →L[ℂ] ParityPair n
  let nr : NormedRing E := ContinuousLinearMap.toNormedRing
  letI : NormedRing E := nr
  let un : NonUnitalNormedRing E := nr.toNonUnitalNormedRing
  letI : NonUnitalNormedRing E := un
  letI : NormedAddCommGroup E := un.toNormedAddCommGroup
  let na : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
  letI : NormedAlgebra ℂ E := na
  let alg : Algebra ℂ E := na.toAlgebra
  letI : Algebra ℂ E := alg
  let ns : NormedSpace ℂ E := NormedAlgebra.toNormedSpace E
  letI : NormedSpace ℂ E := ns
  letI : Module ℂ E := ns.toModule
  letI : DistribMulAction ℂ E := ns.toModule.toDistribMulAction
  letI : DistribSMul ℂ E := DistribMulAction.toDistribSMul
  have hL := actualSchurEffective_hasFDerivAt_actualResolvent38V1
    R hR n hn hlarge p z hz hp₁ hp₂
  let ent : E →L[ℂ] ℂ := actualSchurEntryFunctional31 n i j
  have hE : HasFDerivAt (fun X : E => ent X) ent
      (actualSchurEffectiveSpectralLineV3_32 n p z) := ent.hasFDerivAt
  have h2 := (hE.comp z hL).hasDerivAt
  convert h2 using 1
  · funext w
    rfl
  · rw [ContinuousLinearMap.comp_apply, actualSchurToSpanSingleton_one38V1]

/-- Every actual resonant entry is `C R^4/n^2`-Lipschitz on the original
spectral disk (convex), with the checked Green-product constant. -/
theorem actualSchurEntry_lipschitz38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (i j : Bool × Sector n)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (w w' : ℂ) (hw : w ∈ spectralDisk n) (hw' : w' ∈ spectralDisk n) :
    ‖actualSchurCoefficientAfterDext31 n i j (w, p) -
        actualSchurCoefficientAfterDext31 n i j (w', p)‖ ≤
      freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2 *
        ‖w - w'‖ := by
  classical
  have hconv : Convex ℝ (spectralDisk n) := by
    have h : spectralDisk n = Metric.closedBall (spectralCenter n) 1 := by
      ext x
      simp [spectralDisk, Metric.mem_closedBall, dist_eq_norm]
    rw [h]
    exact convex_closedBall _ _
  let f' : ℂ → ℂ := fun x =>
    if hx : x ∈ spectralDisk n then
      actualSchurEntryFunctional31 n i j
        (-(actualSchurGreenDerivativeProductV3_31 n x p hx))
    else 0
  have hderiv : ∀ x ∈ spectralDisk n,
      HasDerivWithinAt (fun v : ℂ => actualSchurCoefficientAfterDext31 n i j (v, p))
        (f' x) (spectralDisk n) x := by
    intro x hx
    simp only [f', dif_pos hx]
    exact (actualSchurEntry_hasDerivAt38V1 R hR n hn hlarge i j p x hx
      hp₁ hp₂).hasDerivWithinAt
  have hbound : ∀ x ∈ spectralDisk n,
      ‖f' x‖ ≤ freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2 := by
    intro x hx
    simp only [f', dif_pos hx]
    refine le_trans (actualSchurEntryFunctional31_apply_norm_le38V1 n _ _ _) ?_
    rw [ContinuousLinearMap.opNorm_neg]
    exact actualSchurGreenDerivativeProduct_boundV3_31 R hR n hn hlarge x p hx hp₁ hp₂
  exact hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hw' hw

end NlsGge.Schur
