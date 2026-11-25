import QuantumNLS.Ext005ComparisonIdentityR114
import QuantumNLS.Ext005AlgebraicFormR114

/-! The source A,B,H(t) hypotheses on [0,1). H(t) is initially an
algebraic sesquilinear form. Its continuity is a conclusion. The form-order
inequalities are read on Q(A), hence include Q(A) subset Q(B+1). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005SourceHypothesesR114
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
open Ext005AlgebraicFormR114 Ext005ComplexRieszR113
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded two-sided resolvent of the actual partial operator T. -/
def Resolves (T : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ x : H, ∃ hx : R x ∈ T.domain, T ⟨R x, hx⟩ - z • R x = x) ∧
    ∀ u : T.domain, R (T u - z • (u : H)) = (u : H)

/-- Strong commutation, in the nonreal-resolvent convention for
self-adjoint operators. No commuting action is inferred from form order. -/
def StronglyCommute (A B : H →ₗ.[ℂ] H) : Prop :=
  ∀ z w : ℂ, z.im ≠ 0 → w.im ≠ 0 → ∀ R S : H →L[ℂ] H,
    Resolves A z R → Resolves B w S → R.comp S = S.comp R

/-- Literal source form hypotheses, with the domain convention explicit.
The commutator is evaluated wherever B acts within Q(A). Uniqueness below
needs only a subset of these hypotheses; existence is not asserted here. -/
structure SourceHypotheses (A : PositiveOperator H) where
  B : NonnegativeOperator H
  domain : FormContained A (plusOne B)
  commute : StronglyCommute A.op B.op
  hamiltonian : ℝ → RawForm (FormDomain A)
  C : ℝ
  constant_pos : 0 < C
  symmetric : ∀ t ∈ Ico (0 : ℝ) 1, Hermitian (hamiltonian t)
  upper : ∀ t ∈ Ico (0 : ℝ) 1, ∀ u : FormDomain A,
    (hamiltonian t u u).re ≤ C * ‖u‖ ^ 2
  lower : ∀ t ∈ Ico (0 : ℝ) 1, ∀ u : FormDomain A,
    C⁻¹ * ‖u‖ ^ 2 - C * comparisonEnergy A B domain u ≤ (hamiltonian t u u).re
  commutator : ∀ t ∈ Ico (0 : ℝ) 1, ∀ u : FormDomain A,
    ∀ hu : inclusion A u ∈ B.op.domain, ∀ v : FormDomain A,
    inclusion A v = B.op ⟨inclusion A u, hu⟩ →
      (Complex.I * (hamiltonian t v u - hamiltonian t u v)).re ≤ C * ‖u‖ ^ 2
  diagonalDerivative : ℝ → FormDomain A → ℝ
  derivative : ∀ u t, t ∈ Ico (0 : ℝ) 1 →
    HasDerivWithinAt (fun s => (hamiltonian s u u).re)
      (diagonalDerivative t u) (Ico 0 1) t
  derivative_bound : ∀ u t, t ∈ Ico (0 : ℝ) 1 →
    |diagonalDerivative t u| ≤ C * ‖u‖ ^ 2

variable (A : PositiveOperator H) (S : SourceHypotheses A)

/-- A derived finite bound. The B contribution comes from the closed graph
theorem, not from the incorrect implication B <= A. -/
def finiteBound : ℝ := S.C * (1 + ‖comparison A (plusOne S.B) S.domain‖ ^ 2)

lemma finiteBound_nonneg : 0 ≤ finiteBound A S := by
  have hC := S.constant_pos.le
  dsimp [finiteBound]
  positivity

lemma source_diagonal_bound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) (u : FormDomain A) :
    |(S.hamiltonian t u u).re| ≤ finiteBound A S * ‖u‖ ^ 2 := by
  have hC := S.constant_pos.le
  have hE : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have hN : 0 ≤ ‖comparison A (plusOne S.B) S.domain‖ ^ 2 := sq_nonneg _
  have hB := comparisonEnergy_bound A S.B S.domain u
  have hCB := mul_le_mul_of_nonneg_left hB hC
  have hi : 0 ≤ S.C⁻¹ * ‖u‖ ^ 2 := mul_nonneg (inv_nonneg.mpr hC) hE
  have hCN : 0 ≤ S.C * ‖comparison A (plusOne S.B) S.domain‖ ^ 2 * ‖u‖ ^ 2 := by positivity
  have hCE : 0 ≤ S.C * ‖u‖ ^ 2 := mul_nonneg hC hE
  dsimp [finiteBound]
  apply abs_le.mpr
  constructor <;> nlinarith [S.upper t ht u, S.lower t ht u]

/-- Continuous forms constructed from the source inequalities, with zero
extension outside the source interval. No b(t) is supplied as input. -/
def sourceForm (t : ℝ) : Form (FormDomain A) := by
  classical
  exact if ht : t ∈ Ico (0 : ℝ) 1 then
    continuousForm (S.hamiltonian t) (finiteBound A S) (finiteBound_nonneg A S)
      (S.symmetric t ht) (source_diagonal_bound A S t ht)
    else 0

lemma sourceForm_apply (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) (u v : FormDomain A) :
    sourceForm A S t u v = S.hamiltonian t u v := by
  simp only [sourceForm, dite_eq_left ht, continuousForm_apply]

lemma sourceForm_symmetric (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) (u v : FormDomain A) :
    starRingEnd ℂ (sourceForm A S t u v) = sourceForm A S t v u := by
  rw [sourceForm_apply A S t ht, sourceForm_apply A S t ht]
  exact S.symmetric t ht u v

lemma sourceForm_derivative (u : FormDomain A) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => (sourceForm A S s u u).re)
      (S.diagonalDerivative t u) (Ico 0 1) t := by
  apply (S.derivative u t ht).congr_of_mem _ ht
  intro s hs
  rw [sourceForm_apply A S s hs]

end QuantumNLS.Ext005SourceHypothesesR114
#print axioms QuantumNLS.Ext005SourceHypothesesR114.source_diagonal_bound
#print axioms QuantumNLS.Ext005SourceHypothesesR114.sourceForm_apply

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SourceHypothesesR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SourceHypothesesR114." then
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
  Lean.logInfo m!"R114 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
