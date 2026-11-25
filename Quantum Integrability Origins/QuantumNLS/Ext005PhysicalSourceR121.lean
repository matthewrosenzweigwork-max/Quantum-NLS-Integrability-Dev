import QuantumNLS.Ext005PhysicalTimeR121
import QuantumNLS.Ext005FiniteContractR39b

/-! Construct the literal physical SourceOn with B=A, and prove all extra
bounds required by reversal. No source record or source inequality is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap Set Filter MeasureTheory
namespace QuantumNLS.Ext005PhysicalSourceR121
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentDomainR33b Ext005OperatorFormR113 Ext005PhysicalStaticR121
open Ext005PhysicalTimeR121 Ext005SameComparisonR121 Ext005FormEmbeddingR114
open Ext005SourceIntervalR32b Ext005ReversalR39b
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022ActualProfileR117
open Ext005PairCommutatorR108
variable {L : ℝ} [Fact (0 < L)]

def formMajorant (M A : ℝ) : ℝ := |M * (numberMajorant A + pairMajorant A)|
def commutatorMajorant (j : ℕ) (M A : ℝ) : ℝ := |differenceConstant j * (M * pairMajorant A)|
def sourceC (j : ℕ) (M A : ℝ) : ℝ :=
  2 + formMajorant M A + commutatorMajorant j M A + |derivativeMajorant M A|

lemma sourceC_margin (j : ℕ) (M A : ℝ) : formMajorant M A + 1 ≤ sourceC j M A := by
  unfold sourceC commutatorMajorant
  linarith [abs_nonneg (differenceConstant j * (M * pairMajorant A)), abs_nonneg (derivativeMajorant M A)]

lemma sourceC_positive (j : ℕ) (M A : ℝ) : 0 < sourceC j M A := by
  unfold sourceC formMajorant commutatorMajorant
  positivity

lemma lower_of_absolute (E H C q : ℝ) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (hC : H + 1 ≤ C) (hq : |q| ≤ H * E) : C⁻¹ * E - C * E ≤ q := by
  have h1 : 1 ≤ C := by linarith
  have hi : C⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hmul := mul_le_mul_of_nonneg_right (show C⁻¹ + H ≤ C by linarith) hE
  have hlow := (abs_le.mp hq).1
  nlinarith only [hmul, hlow]

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "a" => (fun t => numberCoefficient B (profile B M A hA hB hs u₀ t))
local notation "b" => (fun t => pairCoefficient B (profile B M A hA hB hs u₀ t))

lemma actual_form_bound (j : ℕ) (hj : 1 ≤ j) (t : ℝ)
    (u : FormDomain (momentPositive (L := L) j)) :
    |(physicalForm j hj (a t) (b t) u u).re| ≤ formMajorant M A * ‖u‖ ^ 2 := by
  apply (Complex.abs_re_le_norm _).trans
  apply (physicalForm_bound j hj (a t) (b t) u).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hp := (profile_spec B M A hA hB hs u₀).2.2.1 t
  have h1 := numberCoefficient_bound B M A hA hB _ hp
  have h2 := pairCoefficient_bound B M A hA hB _ hp
  exact (show ‖a t‖ + ‖b t‖ ≤ M * (numberMajorant A + pairMajorant A) by
    nlinarith only [h1, h2]).trans (le_abs_self _)

lemma actual_commutator_bound (j : ℕ) (hj : 1 ≤ j) (t : ℝ)
    (u : FormDomain (momentPositive (L := L) j))
    (hu : Ext005OperatorFormR113.inclusion (momentPositive j) u ∈ (momentPositive j).op.domain)
    (v : FormDomain (momentPositive (L := L) j))
    (hv : Ext005OperatorFormR113.inclusion (momentPositive j) v =
      (momentPositive j).op ⟨Ext005OperatorFormR113.inclusion (momentPositive j) u, hu⟩) :
    |(Complex.I * (physicalForm j hj (a t) (b t) v u - physicalForm j hj (a t) (b t) u v)).re| ≤
      commutatorMajorant j M A * ‖u‖ ^ 2 := by
  apply (physicalForm_commutator_bound j hj (a t) (b t) u hu v hv).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left
    (pairCoefficient_bound B M A hA hB _ ((profile_spec B M A hA hB hs u₀).2.2.1 t))
    (differenceConstant_nonneg j)).trans (le_abs_self _)

/-- SourceOn for the actual time-dependent physical quadratic Hamiltonian,
with A and B both literally the maximal (Num+1)^j multiplier. -/
def physicalSource (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) :
    SourceOn (momentPositive (L := L) j) l r where
  B := sameB (momentPositive j)
  domain := sameDomain (momentPositive j)
  commute := stronglyCommute_self _
  hamiltonian t := physicalForm j hj (a t) (b t)
  C := sourceC j M A
  constant_pos := sourceC_positive j M A
  symmetric t _ := physicalForm_symmetric j hj (a t)
    (numberCoefficient_adjoint B hs _) (b t)
  upper t _ u := by
    apply (le_abs_self _).trans ((actual_form_bound B M A hA hB hs u₀ j hj t u).trans _)
    exact mul_le_mul_of_nonneg_right (by linarith [sourceC_margin j M A]) (sq_nonneg _)
  lower t _ u := by
    rw [same_comparison_energy]
    exact lower_of_absolute _ _ _ _ (sq_nonneg _) (abs_nonneg _)
      (sourceC_margin j M A) (actual_form_bound B M A hA hB hs u₀ j hj t u)
  commutator t _ u hu v hv := by
    apply (le_abs_self _).trans ((actual_commutator_bound B M A hA hB hs u₀ j hj t u hu v hv).trans _)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold sourceC formMajorant commutatorMajorant
    linarith [abs_nonneg (M * (numberMajorant A + pairMajorant A)), abs_nonneg (derivativeMajorant M A)]
  diagonalDerivative := diagonalDerivative B M A hA hB hs u₀ j hj
  derivative u t _ := (actual_derivative B M A hM hA hB hs u₀ j hj u t).hasDerivWithinAt
  derivative_bound u t _ := by
    apply (actual_derivative_bound B M A hM hA hB hs u₀ j hj u t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    unfold sourceC formMajorant commutatorMajorant
    linarith [le_abs_self (derivativeMajorant M A), abs_nonneg (M * (numberMajorant A + pairMajorant A)),
      abs_nonneg (differenceConstant j * (M * pairMajorant A))]

lemma physicalSource_B (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) :
    (physicalSource B M A hM hA hB hs u₀ j hj l r).B.op = (momentPositive (L := L) j).op := rfl

lemma physicalSource_hamiltonian (j : ℕ) (hj : 1 ≤ j) (l r t : ℝ) :
    (physicalSource B M A hM hA hB hs u₀ j hj l r).hamiltonian t =
      physicalForm j hj (a t) (b t) := rfl

/-- Both reversed lower coercivity and the absolute commutator are proved. -/
def physicalReversal (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) :
    ReversalBounds (momentPositive (L := L) j) l r
      (physicalSource B M A hM hA hB hs u₀ j hj l r) := by
  let S := physicalSource B M A hM hA hB hs u₀ j hj l r
  let K := finiteBound (momentPositive j) l r S + sourceC j M A
  have hf := finiteBound_nonneg (momentPositive j) l r S
  have hC := sourceC_positive j M A
  have hKC : sourceC j M A ≤ K := by dsimp [K]; linarith
  refine { K := K, positive := by dsimp [K]; linarith
           diagonal_constant := by dsimp [K]; linarith
           derivative_constant := hKC
           reflected_lower := ?_, absolute_commutator := ?_ }
  · intro t _ u
    change K⁻¹ * ‖u‖ ^ 2 - K * comparisonEnergy (momentPositive j)
      (sameB (momentPositive j)) (sameDomain (momentPositive j)) u ≤ _
    rw [same_comparison_energy]
    apply lower_of_absolute _ _ _ _ (sq_nonneg _) (abs_nonneg _)
      ((sourceC_margin j M A).trans hKC)
    change |-(physicalForm j hj (a t) (b t) u u).re| ≤ formMajorant M A * ‖u‖ ^ 2
    rw [abs_neg]
    exact actual_form_bound B M A hA hB hs u₀ j hj t u
  · intro t ht u hu v hv
    have hc := actual_commutator_bound B M A hA hB hs u₀ j hj t u hu v hv
    apply hc.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hmajor : commutatorMajorant j M A ≤ sourceC j M A := by
      unfold sourceC formMajorant commutatorMajorant
      linarith [abs_nonneg (M * (numberMajorant A + pairMajorant A)), abs_nonneg (derivativeMajorant M A)]
    exact hmajor.trans hKC

end QuantumNLS.Ext005PhysicalSourceR121
#print axioms QuantumNLS.Ext005PhysicalSourceR121.physicalSource
#print axioms QuantumNLS.Ext005PhysicalSourceR121.physicalReversal

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalSourceR121." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalSourceR121." then
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
  Lean.logInfo m!"R121 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
