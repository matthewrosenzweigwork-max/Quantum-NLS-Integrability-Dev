import QuantumNLS.Prop022FactorialCoefficientsR115
import QuantumNLS.Ext005PairCommutatorR108

/-! Identify actual sector operator commutators with the previously bounded
weight-difference series. Both series converge on the j-th form domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022PhysicalCommutatorR115
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005PairSector Ext005QuadraticEnergyR108 Ext005MomentEnergyR108
open Ext005PairCommutatorR108 Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
variable {L : ℝ} [Fact (0 < L)]

def momentBlock (j n : ℕ) : HN L n →L[ℂ] HN L n :=
  (momentWeight j n : ℂ) • ContinuousLinearMap.id ℂ _

def annihilationCommutator (j : ℕ) (b : HN L 2) (n : ℕ) : HN L (2+n) →L[ℂ] HN L n :=
  annihilation b n ∘L momentBlock j (2+n) - momentBlock j n ∘L annihilation b n

def creationCommutator (j : ℕ) (b : HN L 2) (n : ℕ) : HN L n →L[ℂ] HN L (2+n) :=
  creation b n ∘L momentBlock j n - momentBlock j (2+n) ∘L creation b n

lemma number_commutes (j n : ℕ) (a : HN L 1 →L[ℂ] HN L 1) :
    numberBlock a n ∘L momentBlock j n = momentBlock j n ∘L numberBlock a n := by
  ext x
  simp [momentBlock]

lemma annihilationCommutator_eq (j : ℕ) (b : HN L 2) (n : ℕ) :
    annihilationCommutator j b n =
      ((momentWeight j (2+n) - momentWeight j n : ℝ) : ℂ) • annihilation b n := by
  ext x
  simp [annihilationCommutator, momentBlock, sub_smul]

lemma creationCommutator_eq (j : ℕ) (b : HN L 2) (n : ℕ) :
    creationCommutator j b n =
      ((momentWeight j n - momentWeight j (2+n) : ℝ) : ℂ) • creation b n := by
  ext x
  simp [creationCommutator, momentBlock, sub_smul]

lemma annihilation_matrix (j : ℕ) (b : HN L 2) (x : Fock L) (n : ℕ) :
    ⟪x n, annihilationCommutator j b n (x (2+n))⟫_ℂ = -differenceTerm j b x n := by
  rw [annihilationCommutator_eq]
  simp only [smul_apply, inner_smul_right, Complex.ofReal_sub, differenceTerm]
  have hw : momentWeight j (2+n) = momentWeight j (n+2) :=
    congrArg (momentWeight j) (Nat.add_comm 2 n)
  rw [hw]
  ring

lemma creation_matrix (j : ℕ) (b : HN L 2) (x : Fock L) (n : ℕ) :
    ⟪x (2+n), creationCommutator j b n (x n)⟫_ℂ = star (differenceTerm j b x n) := by
  rw [creationCommutator_eq]
  simp only [smul_apply, inner_smul_right, creation, adjoint_inner_right, differenceTerm]
  have hw : momentWeight j (2+n) = momentWeight j (n+2) :=
    congrArg (momentWeight j) (Nat.add_comm 2 n)
  change ((momentWeight j n - momentWeight j (2+n) : ℝ) : ℂ) *
    ⟪annihilation b n (x (2+n)), x n⟫_ℂ =
      starRingEnd ℂ (((momentWeight j n - momentWeight j (n+2) : ℝ) : ℂ) *
        ⟪x n, annihilation b n (x (2+n))⟫_ℂ)
  rw [map_mul, Complex.conj_ofReal, hw, inner_conj_symm]

lemma annihilation_summable (j : ℕ) (hj : 1 ≤ j) (b : HN L 2)
    (x : momentDomain (L := L) j) :
    Summable (fun n => ⟪x.val n, annihilationCommutator j b n (x.val (2+n))⟫_ℂ) := by
  simpa only [annihilation_matrix] using (difference_series_bound j hj b x).1.neg

lemma creation_summable (j : ℕ) (hj : 1 ≤ j) (b : HN L 2)
    (x : momentDomain (L := L) j) :
    Summable (fun n => ⟪x.val (2+n), creationCommutator j b n (x.val n)⟫_ℂ) := by
  simpa only [creation_matrix] using (difference_series_bound j hj b x).1.star

/-- i[Q_pair,(Num+1)^j] evaluated from the actual sector operator commutators. -/
def physicalCommutator (j : ℕ) (b : HN L 2) (x : Fock L) : ℂ :=
  (Complex.I/2) * ((∑' n, ⟪x n, annihilationCommutator j b n (x (2+n))⟫_ℂ) +
    ∑' n, ⟪x (2+n), creationCommutator j b n (x n)⟫_ℂ)

lemma physicalCommutator_identity (j : ℕ) (b : HN L 2) (x : Fock L) :
    physicalCommutator j b x = diagonalCommutator j b x := by
  simp only [physicalCommutator, annihilation_matrix, creation_matrix, tsum_neg,
    tsum_star, diagonalCommutator]
  ring

lemma physicalCommutator_bound (j : ℕ) (hj : 1 ≤ j) (b : HN L 2)
    (x : momentDomain (L := L) j) :
    ‖physicalCommutator j b x.val‖ ≤ differenceConstant j * ‖b‖ * energy j x.val := by
  rw [physicalCommutator_identity]
  exact diagonalCommutator_bound j hj b x

lemma factorialCommutator_bound (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (u : PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (j : ℕ) (hj : 1 ≤ j)
    (x : momentDomain (L := L) j) :
    ‖physicalCommutator j (pairCoefficient B u) x.val‖ ≤
      differenceConstant j * (M * pairMajorant A) * energy j x.val := by
  exact (physicalCommutator_bound j hj (pairCoefficient B u) x).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pairCoefficient_bound B M A hA hB u hu)
        (differenceConstant_nonneg j)) (energy_nonneg j x.val))

end QuantumNLS.Prop022PhysicalCommutatorR115
#print axioms QuantumNLS.Prop022PhysicalCommutatorR115.number_commutes
#print axioms QuantumNLS.Prop022PhysicalCommutatorR115.physicalCommutator_identity
#print axioms QuantumNLS.Prop022PhysicalCommutatorR115.factorialCommutator_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022PhysicalCommutatorR115." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022PhysicalCommutatorR115." then
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
