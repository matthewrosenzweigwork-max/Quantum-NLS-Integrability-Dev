import NlsGge.Schur.ActualSchurEffectiveDerivativeActual38V1
import NlsGge.Schur.ActualSchurAlphaBoundAfterDextV6_32
import NlsGge.Schur.ActualSchurGreenProductBoundV3_31
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The moving gap center (NEW-F03.05, existence/uniqueness/displacement part)

Source: `paper/v2.tex` lines 1118-1127 (F:eq:center).  For the actual
diagonal Schur coefficient `α_n(λ) = ⟪e₊, A_n(λ) e₊⟫` of the actual
Dext-defined effective operator, after increasing the absolute constant in
`|n| ≥ C R^3`, the scalar equation `σ = nπ + α_n(σ)` has a unique solution in
the closed disk `|λ - nπ| ≤ 1/2`.  The proof is the source contraction
argument: the map sends the disk into the disk of radius `1/8` and its
derivative `-⟪e₊, G̃_n G_n e₊⟫` has norm at most `1/4`.

Holomorphic dependence on the potential pair and reality for real-type
potentials are NOT proved in this file.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace NNReal
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The actual diagonal Schur coefficient `α_n(λ)` for a fixed independent
complex H¹ pair `p = (u₁, u₂)`. -/
def actualSchurAlpha38 (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30)
    (w : ℂ) : ℂ :=
  actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (true, resonantIndex n) (w, p)

/-- Absolute constant `C` of the source threshold `|n| ≥ C R^3`, assembled
from the checked free-resolvent, multiplier and inverse constants. -/
def actualSchurCenterThresholdConstant38 : ℝ :=
  4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant +
    8 * (2 * freeResolventSchurUniformConstant *
      freeResolventComplementaryInverseUniformConstant22 *
      physicalH1MultiplierConstant) +
    4 * (freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2) + 1

theorem actualSchurCenterThresholdConstant38_consequences
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|) :
    1 ≤ |(n : ℝ)| ∧
    4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)| ∧
    2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 3 / |(n : ℝ)| ≤ 1 / 8 ∧
    freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2 ≤
      1 / 4 := by
  have hCpos : 0 < freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hIpos : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hMpos : 0 < physicalH1MultiplierConstant :=
    physicalH1MultiplierConstant_pos
  set a := 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant
    with ha
  set b := 2 * freeResolventSchurUniformConstant *
      freeResolventComplementaryInverseUniformConstant22 *
      physicalH1MultiplierConstant with hb
  set c := freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2 with hc
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hK : actualSchurCenterThresholdConstant38 = a + 8 * b + 4 * c + 1 := rfl
  rw [hK] at hthr
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hR23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have hR34 : R ^ 4 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  set N := |(n : ℝ)| with hN
  have hN1 : 1 ≤ N := by nlinarith
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  refine ⟨hN1, ?_, ?_, ?_⟩
  · nlinarith
  · rw [div_le_iff₀ hNpos]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have hsq : (a + 8 * b + 4 * c + 1) ^ 2 * R ^ 6 ≤ N ^ 2 := by
      have h0 : 0 ≤ (a + 8 * b + 4 * c + 1) * R ^ 3 := by positivity
      have := pow_le_pow_left₀ h0 hthr 2
      nlinarith [this]
    have hK1 : 1 ≤ a + 8 * b + 4 * c + 1 := by linarith
    have hKsq : 4 * c ≤ (a + 8 * b + 4 * c + 1) ^ 2 := by nlinarith
    have : 4 * c * R ^ 4 ≤ (a + 8 * b + 4 * c + 1) ^ 2 * R ^ 6 := by
      have h1 : 4 * c * R ^ 4 ≤ 4 * c * R ^ 6 :=
        mul_le_mul_of_nonneg_left hR34 (by positivity)
      have h2 : 4 * c * R ^ 6 ≤ (a + 8 * b + 4 * c + 1) ^ 2 * R ^ 6 :=
        mul_le_mul_of_nonneg_right hKsq (by positivity)
      linarith
    nlinarith

/-- An actual matrix entry is bounded by the operator norm. -/
theorem actualSchurEntryFunctional31_apply_norm_le38V1 (n : ℤ)
    (i j : Bool × Sector n) (T : ParityPair n →L[ℂ] ParityPair n) :
    ‖actualSchurEntryFunctional31 n i j T‖ ≤ ‖T‖ := by
  have hi : ‖parityPairVector n i‖ = 1 := by
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
    simp
  have hj : ‖parityPairVector n j‖ = 1 := by
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
    simp
  change ‖inner ℂ (parityPairVector n i) (T (parityPairVector n j))‖ ≤ ‖T‖
  calc
    _ ≤ ‖parityPairVector n i‖ * ‖T (parityPairVector n j)‖ :=
      parityPair_inner_norm_le_prerequisite n _ _
    _ ≤ 1 * (‖T‖ * 1) := by
      rw [hi]
      gcongr
      simpa [hj] using T.le_opNorm (parityPairVector n j)
    _ = ‖T‖ := by ring

theorem actualSchurToSpanSingleton_one38V1 (n : ℤ)
    (x : ParityPair n →L[ℂ] ParityPair n) :
    ContinuousLinearMap.toSpanSingleton ℂ x 1 = x := by
  ext y
  rw [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smul_apply,
    one_smul]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Spectral derivative of the actual diagonal coefficient (F:eq:lambda, the
`(+,+)` entry): `α_n'(z) = -⟪e₊, G̃_n G_n e₊⟫`. -/
theorem actualSchurAlpha38_hasDerivAt
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    HasDerivAt (actualSchurAlpha38 n p)
      (actualSchurEntryFunctional31 n (true, resonantIndex n)
        (true, resonantIndex n)
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
  let ent : E →L[ℂ] ℂ := actualSchurEntryFunctional31 n
    (true, resonantIndex n) (true, resonantIndex n)
  have hE : HasFDerivAt (fun X : E => ent X) ent
      (actualSchurEffectiveSpectralLineV3_32 n p z) := ent.hasFDerivAt
  have h2 := (hE.comp z hL).hasDerivAt
  convert h2 using 1
  · funext w
    rfl
  · rw [ContinuousLinearMap.comp_apply, actualSchurToSpanSingleton_one38V1]

/-- The derivative of the actual diagonal coefficient has the source size
`C R^4/n^2` on the original spectral disk. -/
theorem actualSchurAlpha38_deriv_bound
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurEntryFunctional31 n (true, resonantIndex n)
        (true, resonantIndex n)
        (-(actualSchurGreenDerivativeProductV3_31 n z p hz))‖ ≤
      freeResolventComplementaryInverseUniformConstant22 ^ 2 *
        freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2 := by
  refine le_trans (actualSchurEntryFunctional31_apply_norm_le38V1 n _ _ _) ?_
  rw [ContinuousLinearMap.opNorm_neg]
  exact actualSchurGreenDerivativeProduct_boundV3_31 R hR n hn hlarge z p hz hp₁ hp₂

theorem closedBall_half_subset_spectralDisk38 (n : ℤ) :
    Metric.closedBall (spectralCenter n) (1 / 2) ⊆ spectralDisk n := by
  intro w hw
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  change ‖w - spectralCenter n‖ ≤ 1
  linarith

/-- The center map `λ ↦ nπ + α_n(λ)` sends the closed half disk into the
closed disk of radius `1/8`, and is `1/4`-Lipschitz on the half disk. -/
theorem actualSchurCenterMap38_mapsTo_and_lipschitz
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    (∀ w ∈ Metric.closedBall (spectralCenter n) (1 / 2),
      ‖(spectralCenter n + actualSchurAlpha38 n p w) - spectralCenter n‖ ≤
        1 / 8) ∧
    (∀ w ∈ Metric.closedBall (spectralCenter n) (1 / 2),
      ∀ w' ∈ Metric.closedBall (spectralCenter n) (1 / 2),
      ‖actualSchurAlpha38 n p w - actualSchurAlpha38 n p w'‖ ≤
        1 / 4 * ‖w - w'‖) := by
  obtain ⟨hn, hlarge, h18, h14⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  have hsub := closedBall_half_subset_spectralDisk38 n
  constructor
  · intro w hw
    rw [add_sub_cancel_left]
    exact le_trans (actualSchurAlpha_boundAfterDextV6_32 R hR n hn hlarge w p
      (hsub hw) hp₁ hp₂) h18
  · intro w hw w' hw'
    classical
    let f' : ℂ → ℂ := fun x =>
      if hx : x ∈ spectralDisk n then
        actualSchurEntryFunctional31 n (true, resonantIndex n)
          (true, resonantIndex n)
          (-(actualSchurGreenDerivativeProductV3_31 n x p hx))
      else 0
    have hderiv : ∀ x ∈ Metric.closedBall (spectralCenter n) (1 / 2),
        HasDerivWithinAt (actualSchurAlpha38 n p) (f' x)
          (Metric.closedBall (spectralCenter n) (1 / 2)) x := by
      intro x hx
      have hxD := hsub hx
      have h := actualSchurAlpha38_hasDerivAt R hR n hn hlarge p x hxD hp₁ hp₂
      simp only [f', dif_pos hxD]
      exact h.hasDerivWithinAt
    have hbound : ∀ x ∈ Metric.closedBall (spectralCenter n) (1 / 2),
        ‖f' x‖ ≤ 1 / 4 := by
      intro x hx
      have hxD := hsub hx
      simp only [f', dif_pos hxD]
      exact le_trans (actualSchurAlpha38_deriv_bound R hR n hn hlarge p x hxD
        hp₁ hp₂) h14
    exact (convex_closedBall (spectralCenter n) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound hw' hw

/-- F:eq:center: for `|n| ≥ C R^3` and an independent complex H¹ pair in the
radius-`R` balls, the actual center equation `σ = nπ + α_n(σ)` has exactly one
solution in the closed disk `|σ - nπ| ≤ 1/2`. -/
theorem actualSchurCenter_existsUnique38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ∃! σ : ℂ, σ ∈ Metric.closedBall (spectralCenter n) (1 / 2) ∧
      σ = spectralCenter n + actualSchurAlpha38 n p σ := by
  obtain ⟨hmaps, hlip⟩ :=
    actualSchurCenterMap38_mapsTo_and_lipschitz R hR n hthr p hp₁ hp₂
  let s : Set ℂ := Metric.closedBall (spectralCenter n) (1 / 2)
  let T : ℂ → ℂ := fun w => spectralCenter n + actualSchurAlpha38 n p w
  have hsf : Set.MapsTo T s s := by
    intro w hw
    have h := hmaps w hw
    change dist (T w) (spectralCenter n) ≤ 1 / 2
    rw [dist_eq_norm]
    exact le_trans h (by norm_num)
  have hsc : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hK : (1 / 4 : ℝ≥0) < 1 := by
    rw [show (1 / 4 : ℝ≥0) = (4 : ℝ≥0)⁻¹ by simp]
    exact inv_lt_one_of_one_lt₀ (by norm_num)
  have hcontr : ContractingWith (1 / 4 : ℝ≥0) (hsf.restrict T s s) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    change dist (T x) (T y) ≤ ((1 / 4 : ℝ≥0) : ℝ) * dist (x : ℂ) (y : ℂ)
    rw [dist_eq_norm, dist_eq_norm]
    have h := hlip x x.2 y y.2
    have he : T x - T y =
        actualSchurAlpha38 n p x - actualSchurAlpha38 n p y := by
      simp only [T]
      ring
    rw [he]
    simpa using h
  have hc : spectralCenter n ∈ s := Metric.mem_closedBall_self (by norm_num)
  obtain ⟨σ, hσs, hσfix, -, -⟩ :=
    hcontr.exists_fixedPoint' hsc hsf hc (edist_ne_top _ _)
  refine ⟨σ, ⟨hσs, hσfix.symm⟩, ?_⟩
  rintro τ ⟨hτs, hτ⟩
  have h := hlip τ hτs σ hσs
  have hστ : τ - σ = actualSchurAlpha38 n p τ - actualSchurAlpha38 n p σ := by
    have hσ' : σ = spectralCenter n + actualSchurAlpha38 n p σ := hσfix.symm
    calc
      τ - σ = (spectralCenter n + actualSchurAlpha38 n p τ) -
          (spectralCenter n + actualSchurAlpha38 n p σ) := by
        rw [← hτ, ← hσ']
      _ = _ := by ring
  rw [← hστ] at h
  have h0 : ‖τ - σ‖ = 0 := by
    have hn0 := norm_nonneg (τ - σ)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- The source displacement estimate for the center: any solution of the
center equation in the half disk satisfies `|σ - nπ| ≤ C R^3/|n|`. -/
theorem actualSchurCenter_displacement38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) (σ : ℂ)
    (hσ : σ ∈ Metric.closedBall (spectralCenter n) (1 / 2))
    (hfix : σ = spectralCenter n + actualSchurAlpha38 n p σ) :
    ‖σ - spectralCenter n‖ ≤
      2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 3 / |(n : ℝ)| := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  have hσ' : σ - spectralCenter n = actualSchurAlpha38 n p σ := by
    conv_lhs => rw [hfix]
    ring
  rw [hσ']
  exact actualSchurAlpha_boundAfterDextV6_32 R hR n hn hlarge σ p
    (closedBall_half_subset_spectralDisk38 n hσ) hp₁ hp₂

end NlsGge.Schur
