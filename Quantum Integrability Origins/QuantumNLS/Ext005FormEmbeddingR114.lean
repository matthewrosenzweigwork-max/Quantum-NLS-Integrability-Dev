import QuantumNLS.Ext005ShiftR114
import Mathlib.Analysis.Normed.Operator.Banach

/-! Domain containment between the constructed closed energy spaces implies a
finite form bound by the closed graph theorem. No bound for B is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005FormEmbeddingR114
open Ext005OperatorFormR113 Ext005ShiftR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal form-domain containment, expressed through the actual embeddings
in H. This is needed for a quadratic-form inequality on all of Q(A). -/
def FormContained (A D : PositiveOperator H) : Prop :=
  ∀ u : FormDomain A, ∃ v : FormDomain D, inclusion D v = inclusion A u

variable (A D : PositiveOperator H) (h : FormContained A D)

def domainMap : FormDomain A →ₗ[ℂ] FormDomain D where
  toFun u := Classical.choose (h u)
  map_add' u v := by
    apply inclusion_injective D
    change inclusion D (Classical.choose (h (u + v))) =
      inclusion D (Classical.choose (h u) + Classical.choose (h v))
    rw [Classical.choose_spec (h (u + v)), map_add, map_add,
      Classical.choose_spec (h u), Classical.choose_spec (h v)]
  map_smul' c u := by
    apply inclusion_injective D
    change inclusion D (Classical.choose (h (c • u))) =
      inclusion D (c • Classical.choose (h u))
    rw [Classical.choose_spec (h (c • u)), map_smul, map_smul,
      Classical.choose_spec (h u)]

@[simp] lemma domainMap_pair (u : FormDomain A) :
    inclusion D (domainMap A D h u) = inclusion A u := Classical.choose_spec (h u)

lemma domainMap_continuous : Continuous (domainMap A D h) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro u x y hx hy
  apply inclusion_injective D
  have hy' := ((inclusion D).continuous.tendsto y).comp hy
  have hx' := ((inclusion A).continuous.tendsto x).comp hx
  change Tendsto (fun n => inclusion D (domainMap A D h (u n))) atTop (𝓝 (inclusion D y)) at hy'
  simp only [domainMap_pair] at hy'
  exact (tendsto_nhds_unique hy' hx').trans (domainMap_pair A D h x).symm

/-- Constructed continuous inclusion between the two form domains. -/
def comparison : FormDomain A →L[ℂ] FormDomain D :=
  ⟨domainMap A D h, domainMap_continuous A D h⟩

@[simp] lemma comparison_pair (u : FormDomain A) :
    inclusion D (comparison A D h u) = inclusion A u := domainMap_pair A D h u

/-- The nonnegative B form on Q(A), with B+1 energy coordinates. -/
def comparisonEnergy (B : NonnegativeOperator H) (hB : FormContained A (plusOne B))
    (u : FormDomain A) : ℝ :=
  ‖comparison A (plusOne B) hB u‖ ^ 2 - ‖inclusion A u‖ ^ 2

lemma comparisonEnergy_nonneg (B : NonnegativeOperator H)
    (hB : FormContained A (plusOne B)) (u : FormDomain A) :
    0 ≤ comparisonEnergy A B hB u := by
  have hb := inclusion_norm_le (plusOne B) (comparison A (plusOne B) hB u)
  rw [comparison_pair] at hb
  dsimp [comparisonEnergy]
  nlinarith [norm_nonneg (inclusion A u), norm_nonneg (comparison A (plusOne B) hB u)]

/-- The crucial finite Q(A)-form bound is derived from domain containment
and closedness; no numerical B bound or continuous H(t) is assumed. -/
lemma comparisonEnergy_bound (B : NonnegativeOperator H)
    (hB : FormContained A (plusOne B)) (u : FormDomain A) :
    comparisonEnergy A B hB u ≤ ‖comparison A (plusOne B) hB‖ ^ 2 * ‖u‖ ^ 2 := by
  have hb := (comparison A (plusOne B) hB).le_opNorm u
  dsimp [comparisonEnergy]
  nlinarith [sq_nonneg ‖inclusion A u‖,
    norm_nonneg (comparison A (plusOne B) hB u),
    norm_nonneg (comparison A (plusOne B) hB), norm_nonneg u]

end QuantumNLS.Ext005FormEmbeddingR114
#print axioms QuantumNLS.Ext005FormEmbeddingR114.domainMap_continuous
#print axioms QuantumNLS.Ext005FormEmbeddingR114.comparisonEnergy_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005FormEmbeddingR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005FormEmbeddingR114." then
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
