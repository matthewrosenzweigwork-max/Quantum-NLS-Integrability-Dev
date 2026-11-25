import QuantumNLS.Prop022FactorialMajorantR115

/-! Actual summable factorial contraction coefficients and their physical
quadratic form, with the report one-half normalization. Identification with
Fréchet derivatives of the full classical series remains a separate gate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022FactorialCoefficientsR115
open Prop022TensorCompressionR115 Prop022FactorialMajorantR115
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext005PhysicalNumberFormR114 Ext005PhysicalSymmetryR114 Ext005PhysicalHalfPairR114
open Ext005PairSector Ext005QuadraticEnergyR108 Ext005MomentEnergyR108 Ext005Moments
variable {L : ℝ} [Fact (0 < L)]

/-- Literal report hypothesis, for positive ranks only; B_0 is unused. -/
def FactorialBound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) : Prop :=
  ∀ m, 1 ≤ m → ‖B m‖ ≤ M * A ^ m / Real.sqrt ((2*m).factorial : ℝ)

lemma mixed_dominated (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) (r : ℕ) :
    ‖mixedTerm B u r‖ ≤ M * weight 2 A (r+1) := by
  calc
    _ ≤ ((r+1 : ℕ) : ℝ)^2 * ‖B (r+1)‖ := mixedTerm_norm B u hu r
    _ ≤ ((r+1 : ℕ) : ℝ)^2 * (M * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (hB (r+1) (by omega)) (sq_nonneg _)
    _ = _ := by unfold weight; ring

lemma pair_dominated (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) (r : ℕ) :
    ‖Prop022TensorCompressionR115.pairTerm B u r‖ ≤ M * pairWeight A r := by
  calc
    _ ≤ (((r+2 : ℕ) : ℝ) * ((r+1 : ℕ) : ℝ)) * ‖B (r+2)‖ := pairTerm_norm B u hu r
    _ ≤ (((r+2 : ℕ) : ℝ) * ((r+1 : ℕ) : ℝ)) *
        (M * A^(r+2) / Real.sqrt ((2*(r+2)).factorial : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (hB (r+2) (by omega)) (by positivity)
    _ = _ := by unfold pairWeight; ring

lemma mixed_summable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) : Summable (mixedTerm B u) := by
  apply Summable.of_norm_bounded (f := mixedTerm B u) ((number_summable A hA).mul_left M)
  intro r
  exact mixed_dominated B M A hB u hu r

lemma pair_summable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) : Summable (Prop022TensorCompressionR115.pairTerm B u) :=
  Summable.of_norm_bounded ((Prop022FactorialMajorantR115.pair_summable A hA).mul_left M)
    (pair_dominated B M A hB u hu)

def numberCoefficient (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    HN L 1 →L[ℂ] HN L 1 := ∑' r, mixedTerm B u r

def pairCoefficient (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : HN L 2 :=
  ∑' r, Prop022TensorCompressionR115.pairTerm B u r

lemma numberCoefficient_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖numberCoefficient B u‖ ≤ M * numberMajorant A := by
  have hd := mixed_dominated B M A hB u hu
  have hm := (number_summable A hA).mul_left M
  have hs : Summable (fun r => ‖mixedTerm B u r‖) :=
    Summable.of_nonneg_of_le (fun r => ContinuousLinearMap.opNorm_nonneg (mixedTerm B u r)) hd hm
  calc
    _ ≤ ∑' r, ‖mixedTerm B u r‖ := norm_tsum_le_tsum_norm (f := mixedTerm B u) hs
    _ ≤ ∑' r, M * weight 2 A (r+1) := hs.tsum_le_tsum hd hm
    _ = _ := by rw [tsum_mul_left]; rfl

lemma pairCoefficient_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖pairCoefficient B u‖ ≤ M * pairMajorant A := by
  have hd := pair_dominated B M A hB u hu
  have hm := (Prop022FactorialMajorantR115.pair_summable A hA).mul_left M
  have hs : Summable (fun r => ‖Prop022TensorCompressionR115.pairTerm B u r‖) :=
    Summable.of_nonneg_of_le (fun r => norm_nonneg _) hd hm
  calc
    _ ≤ ∑' r, ‖Prop022TensorCompressionR115.pairTerm B u r‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' r, M * pairWeight A r := hs.tsum_le_tsum hd hm
    _ = _ := by rw [tsum_mul_left]; rfl

lemma numberCoefficient_adjoint (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (u : L2T L) :
    (numberCoefficient B u).adjoint = numberCoefficient B u := by
  let e : (HN L 1 →L[ℂ] HN L 1) ≃L⋆[ℂ] (HN L 1 →L[ℂ] HN L 1) :=
    adjoint.toContinuousLinearEquiv
  change e (∑' r, mixedTerm B u r) = ∑' r, mixedTerm B u r
  rw [e.map_tsum]
  exact tsum_congr (mixedTerm_adjoint B hB u)

/-- Physical quadratic form for the literal summed contractions. -/
def factorialQuadratic (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :=
  quadraticContinuous (numberCoefficient B u) (pairCoefficient B u)

lemma factorialQuadratic_identity (B : ∀ m, HN L m →L[ℂ] HN L m)
    (u : L2T L) (x : momentDomain (L := L) 1) :
    factorialQuadratic B u (momentRoot 1 x) (momentRoot 1 x) =
      numberForm (numberCoefficient B u) x.val +
        (1/2 : ℂ) * pairHamiltonian (pairCoefficient B u) x :=
  quadraticContinuous_operatorDomain _ _ x

lemma factorialQuadratic_bound (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (u : L2T L) (hu : ‖u‖ = 1) (x : momentDomain (L := L) 1) :
    ‖factorialQuadratic B u (momentRoot 1 x) (momentRoot 1 x)‖ ≤
      M * (numberMajorant A + pairMajorant A) * energy 1 x.val := by
  have ha := numberCoefficient_bound B M A hA hB u hu
  have hb := pairCoefficient_bound B M A hA hB u hu
  calc
    _ ≤ (‖numberCoefficient B u‖ + ‖pairCoefficient B u‖) * energy 1 x.val := by
      rw [factorialQuadratic, quadraticContinuous_operatorDomain]
      exact quadraticForm_bound _ _ x
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (add_le_add ha hb) (energy_nonneg 1 x.val)
      nlinarith only [hh]

lemma factorialQuadratic_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) (u : L2T L) (x y : Fock L) :
    starRingEnd ℂ (factorialQuadratic B u x y) = factorialQuadratic B u y x :=
  quadraticContinuous_symmetric _ (numberCoefficient_adjoint B hB u) _ x y

end QuantumNLS.Prop022FactorialCoefficientsR115
#print axioms QuantumNLS.Prop022FactorialCoefficientsR115.numberCoefficient_bound
#print axioms QuantumNLS.Prop022FactorialCoefficientsR115.pairCoefficient_bound
#print axioms QuantumNLS.Prop022FactorialCoefficientsR115.factorialQuadratic_identity
#print axioms QuantumNLS.Prop022FactorialCoefficientsR115.factorialQuadratic_bound
#print axioms QuantumNLS.Prop022FactorialCoefficientsR115.factorialQuadratic_symmetric

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022FactorialCoefficientsR115." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022FactorialCoefficientsR115." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"R115 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
