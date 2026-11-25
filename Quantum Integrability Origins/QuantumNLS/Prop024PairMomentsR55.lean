import QuantumNLS.Prop024WeylConventionR55
import QuantumNLS.Prop023FinalPhys

/-! Round 55: derive the source expected-number bound from the exact
PROP-022 beta estimate and flow bound, then pass the PROP-022 vacuum data
through the frozen PROP-023 physical moment theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ENNReal

namespace QuantumNLS.Prop024PairMomentsR55

open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors
open Prop022PositiveDataR126 Prop022FockPropagatorR122
open Ext006NumberPhase Ext006PhysQuasifree Ext006PhysFockCoord
open Ext006KernelHilbertSchmidt
open Prop024WeylConventionR55

variable {L : ℝ} [Fact (0 < L)]

/-- The PROP-022 beta estimate and the source variational-flow bound imply
the number hypothesis of PROP-023; its frozen theorem then yields the
exponential and polynomial moments on the source interval. -/
theorem pairInput_moments
    (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ)
    (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n)
    (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P)
    (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP)
    (hSBound :
      let B := positiveExtension K
      let hB := positiveExtension_bound K M A hK
      let hsa := positiveExtension_selfAdjoint K hsK
      let Phi := Prop022ClassicalFlowR126.classicalFlow B M A hA.le hB hsa
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let S := fun t s : ℝ => fderiv ℝ (Phi (t - s)) (u s)
      ∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P) :
    let Q := 1 +
      (Prop022FactorialMajorantR115.pairMajorant A * T * M * P)^2
      let B := positiveExtension K
      let hB := positiveExtension_bound K M A hK
      let hsa := positiveExtension_selfAdjoint K hsK
      let V := fun t s : ℝ => propagator B M A (by linarith) hA.le hB hsa u₀ s t
    ∀ t, |t| ≤ T → exponentialMoment Q (V t 0 vac) ≤
        ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
      ∀ j : ℕ, 1 ≤ j →
        ∃ hx : V t 0 vac ∈ (polynomialRoot (L := L) j).domain,
          ‖polynomialRoot j ⟨V t 0 vac, hx⟩‖ ≤
            Real.rpow (32 * Q * j) ((j : ℝ) / 2) := by
  let B := positiveExtension K
  let hB := positiveExtension_bound K M A hK
  let hsa := positiveExtension_selfAdjoint K hsK
  let V := fun t s : ℝ => propagator B M A (by linarith) hA.le hB hsa u₀ s t
  let Q : ℝ := 1 +
    (Prop022FactorialMajorantR115.pairMajorant A * T * M * P)^2
  have hC : 0 ≤ Prop022FactorialMajorantR115.pairMajorant A :=
    Prop022FactorialMajorantR115.pairMajorant_nonneg A hA.le
  have hM0 : 0 ≤ M := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact le_add_of_nonneg_right (sq_nonneg _)
  change ∀ t, |t| ≤ T → exponentialMoment Q (V t 0 vac) ≤
    ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
      ∀ j : ℕ, 1 ≤ j →
        ∃ hx : V t 0 vac ∈ (polynomialRoot (L := L) j).domain,
          ‖polynomialRoot j ⟨V t 0 vac, hx⟩‖ ≤
            Real.rpow (32 * Q * j) ((j : ℝ) / 2)
  have hVac := pairInput_vacuum_data K M A hM hA hK hsK u₀ T P hP hPair
  change ∀ t, PhysicalQuasifreeSource (V t 0 vac) ∧ ‖V t 0 vac‖ = 1 ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (V t 0 vac) =
        TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
          (Prop022VariationalR123.betaBlock B M A hA.le hB hsa u₀ t 0) at hVac
  have hBetaAll :
      (∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
          ‖fderiv ℝ
            (Prop022ClassicalFlowR126.classicalFlow
              (positiveExtension K) M A hA.le
              (positiveExtension_bound K M A hK)
              (positiveExtension_selfAdjoint K hsK) (r - q))
            (Prop022ActualProfileR117.profile
              (positiveExtension K) M A hA.le
              (positiveExtension_bound K M A hK)
              (positiveExtension_selfAdjoint K hsK) u₀ q)‖ ≤ P) →
        ∀ t, |t| ≤ T →
          TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
              (Prop022VariationalR123.betaBlock B M A hA.le hB hsa u₀ t 0) ≠ ⊤ ∧
            Real.sqrt ((TraceClass.hsSq
              (Ext006KernelHilbertSchmidt.physicalBasis L)
              (Prop022VariationalR123.betaBlock B M A hA.le hB hsa u₀ t 0)).toReal) ≤
              |t| * Prop022FactorialMajorantR115.pairMajorant A * M * P := by
    dsimp [Prop022PairInput] at hPair
    rcases hPair with ⟨_, _, _, _, hBetaAll, _, _, _, _, _, _⟩
    exact hBetaAll
  have hBeta := hBetaAll hSBound
  intro t ht
  obtain ⟨hQF, hnorm, hVacNum⟩ := hVac t
  rcases hBeta t ht with ⟨hHSne, hHSsqrt⟩
  let hs := TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
    (Prop022VariationalR123.betaBlock B M A hA.le hB hsa u₀ t 0)
  have hHSrepr : hs = ENNReal.ofReal (Real.sqrt hs.toReal ^ 2) := by
    calc
      hs = ENNReal.ofReal hs.toReal := (ENNReal.ofReal_toReal hHSne).symm
      _ = ENNReal.ofReal (Real.sqrt hs.toReal ^ 2) := by
        congr 1
        exact (Real.sq_sqrt ENNReal.toReal_nonneg).symm
  have hscale : 0 ≤ Prop022FactorialMajorantR115.pairMajorant A * M * P :=
    mul_nonneg (mul_nonneg hC hM0) hP0
  have hroot : Real.sqrt hs.toReal ≤ T *
      (Prop022FactorialMajorantR115.pairMajorant A * M * P) := by
    calc
      Real.sqrt hs.toReal ≤ |t| * Prop022FactorialMajorantR115.pairMajorant A * M * P := hHSsqrt
      _ ≤ T * (Prop022FactorialMajorantR115.pairMajorant A * M * P) := by
        have htT : |t| ≤ T := ht
        nlinarith [mul_le_mul_of_nonneg_right htT hscale]
  have hrootSq : (Real.sqrt hs.toReal)^2 ≤
      (T * (Prop022FactorialMajorantR115.pairMajorant A * M * P))^2 := by
    nlinarith [Real.sqrt_nonneg hs.toReal, hroot]
  have hNumber : numberExpectation (fun n => (n : ℝ≥0∞)) (V t 0 vac) ≤
      ENNReal.ofReal (Q - 1) := by
    calc
      numberExpectation (fun n => (n : ℝ≥0∞)) (V t 0 vac) = hs := hVacNum
      _ = ENNReal.ofReal (Real.sqrt hs.toReal ^ 2) := hHSrepr
      _ ≤ ENNReal.ofReal (Q - 1) := ENNReal.ofReal_le_ofReal (by
        dsimp [Q]
        nlinarith [hrootSq])
  exact Prop023FinalPhys.prop023 (V t 0 vac) hnorm hQF hQ hNumber

end QuantumNLS.Prop024PairMomentsR55

#print axioms QuantumNLS.Prop024PairMomentsR55.pairInput_moments

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024PairMomentsR55." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024PairMomentsR55." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R55 PROP-022/023 moment bridge audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
