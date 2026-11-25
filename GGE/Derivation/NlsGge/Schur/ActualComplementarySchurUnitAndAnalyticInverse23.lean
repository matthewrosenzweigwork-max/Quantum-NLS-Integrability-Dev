import NlsGge.Schur.FreeResolventComplementaryInverseOnRangeActual
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

/-- Component exchange on the genuine paired parity Hilbert space. -/
def actualParityPairBlockSwap23 (n : ℤ) :
    ParityPair n →L[ℂ] ParityPair n := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => scalarParity n)
  let s : (Bool → scalarParity n) →L[ℂ] (Bool → scalarParity n) :=
    ContinuousLinearMap.pi (fun b : Bool =>
      if b then ContinuousLinearMap.proj false else ContinuousLinearMap.proj true)
  exact e.symm.toContinuousLinearMap.comp (s.comp e.toContinuousLinearMap)

@[simp] theorem actualParityPairBlockSwap23_apply
    (n : ℤ) (x : ParityPair n) (b : Bool) :
    actualParityPairBlockSwap23 n x b = x (!b) := by
  cases b <;> simp [actualParityPairBlockSwap23]

/-- Swapping the two actual independent fields conjugates their concrete
parity-pair potential by component exchange. -/
theorem actualParityPairPotential_blockSwap23
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) :
    (actualParityPairBlockSwap23 n).comp
        ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
          (actualParityPairBlockSwap23 n)) =
      coveredH1ParityPairPotential u₂ u₁ hu₂ hu₁ n := by
  apply ContinuousLinearMap.ext
  intro x
  ext b
  cases b <;> simp [coveredH1ParityPairPotential_apply_true,
    coveredH1ParityPairPotential_apply_false]

/-- In a complete endomorphism normed ring, square smallness makes the actual
linear factor invertible. The commuting factorization is needed because no
bound on `‖A‖` is assumed. -/
theorem continuousLinearMap_one_sub_isUnit_of_square_norm_lt_one23
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E)
    (hA2 : ‖A * A‖ < 1) : IsUnit (1 - A) := by
  have hunitSquare : IsUnit (1 - A * A) :=
    IsUnit.one_sub_of_norm_lt_one hA2
  have hcomm : Commute (1 - A) (1 + A) := by
    change (1 - A) * (1 + A) = (1 + A) * (1 - A)
    noncomm_ring
  have hfactor : (1 - A) * (1 + A) = 1 - A * A := by
    noncomm_ring
  have hunitProduct : IsUnit ((1 - A) * (1 + A)) := by
    rw [hfactor]
    exact hunitSquare
  exact ((Commute.isUnit_mul_iff hcomm).mp hunitProduct).1

/-- The square-smallness estimate for the actual opposite Schur factor gives
uniform invertibility of `1 - Q V D`. Both independent fields and the full
spectral disk remain in the statement. -/
theorem actualFreeResolventOppositeFactor_one_sub_isUnit23
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR : 1 ≤ R)
    (hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    IsUnit (1 - freeResolventComplementaryPotentialOppositeFactor22
      u₁ u₂ hu₁ hu₂ n z hz) := by
  let A : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryPotentialOppositeFactor22 u₁ u₂ hu₁ hu₂ n z hz
  have hA2 : ‖A * A‖ ≤ (1 / 2 : ℝ) := by
    change ‖(freeResolventComplementaryPotentialOppositeFactor22
      u₁ u₂ hu₁ hu₂ n z hz) *
        (freeResolventComplementaryPotentialOppositeFactor22
          u₁ u₂ hu₁ hu₂ n z hz)‖ ≤ (1 / 2 : ℝ)
    exact freeResolventComplementaryPotentialOpposite_square_norm_le_half_actual22
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
  have hsmall : ‖A * A‖ < 1 := by linarith
  exact continuousLinearMap_one_sub_isUnit_of_square_norm_lt_one23 A hsmall

/-- On the actual square-small operator set, the totalized ring inverse of
`1 - A` is analytic. The concrete potential family supplies membership in
this set through its checked square estimate. -/
theorem analyticOnNhd_ringInverse_one_sub_of_square_le_half23
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] :
    AnalyticOnNhd ℂ
      (fun A : E →L[ℂ] E => Ring.inverse (1 - A))
      {A : E →L[ℂ] E | ‖A * A‖ ≤ (1 / 2 : ℝ)} := by
  have hf : AnalyticOnNhd ℂ (fun A : E →L[ℂ] E => (1 : E →L[ℂ] E) - A)
      {A : E →L[ℂ] E | ‖A * A‖ ≤ (1 / 2 : ℝ)} :=
    analyticOnNhd_const.sub analyticOnNhd_id
  have hmaps : Set.MapsTo
      (fun A : E →L[ℂ] E => (1 : E →L[ℂ] E) - A)
      {A : E →L[ℂ] E | ‖A * A‖ ≤ (1 / 2 : ℝ)}
      {T : E →L[ℂ] E | IsUnit T} := by
    intro A hA
    change ‖A * A‖ ≤ (1 / 2 : ℝ) at hA
    apply continuousLinearMap_one_sub_isUnit_of_square_norm_lt_one23
    linarith
  simpa only [Function.comp_def] using
    (analyticOnNhd_inverse.comp hf hmaps)

end NlsGge.Schur
