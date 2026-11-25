import QuantumNLS.Ext005CommutatorCoreR35b

/-! The invariant operator-core bridge implies commutation of the actual
bounded B-form representative and the Gram operator, and hence B-energy
cutoff contraction. This does not assert that the bridge is yet derived
from the source's nonreal-resolvent strong-commutation convention. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005CoreCommutationR35b
open Ext005GramResolventR112 Ext005ComplexGramR34b Ext005PositiveCutoffR35b
open Ext005ComparisonFormR35b Ext005CommutatorCoreR35b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ Q := InnerProductSpace.rclikeToReal ℂ Q
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- Commutation with any one strictly positive-epsilon cutoff already
implies commutation with the Gram operator. -/
lemma gram_commutes_of_cutoff (i : Q →L[ℂ] H) (e : ℝ) (he : 0 < e)
    (T : Q →L[ℂ] Q) (hc : Commute T (cutoffC i e he)) :
    Commute T (gramC i) := by
  have hR (u : Q) : T (inverse (i.restrictScalars ℝ) e he u) =
      inverse (i.restrictScalars ℝ) e he (T u) := by
    have h := congrArg (fun f : Q →L[ℂ] Q => f u) hc.eq
    change T (cutoffC i e he u) = cutoffC i e he (T u) at h
    simp only [cutoffC_apply, cutoff_eq, map_sub, map_smul_of_tower] at h
    exact smul_right_injective (M := Q) he.ne' (sub_right_inj.mp h)
  have hpert (u : Q) : perturbed (i.restrictScalars ℝ) e (T u) =
      T (perturbed (i.restrictScalars ℝ) e u) := by
    have h := congrArg (perturbed (i.restrictScalars ℝ) e)
      (hR (perturbed (i.restrictScalars ℝ) e u))
    simpa only [inverse_perturbed, perturbed_inverse] using h
  ext u
  change T (gramC i u) = gramC i (T u)
  simp only [gramC_apply]
  have h := hpert u
  simp only [perturbed, add_apply, smul_apply, id_apply, map_add, map_smul_of_tower] at h
  exact (add_right_cancel h).symm

variable (A : PositiveOperator H) (B : NonnegativeOperator H)
  (hB : FormContained A (plusOne B))
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- The two actual B-domain assertions in cutoffOperatorCore supply the
commutation on a dense set; continuity supplies equality everywhere. -/
theorem comparison_commutes_of_core (e : ℝ) (he : 0 < e)
    (hd : Dense (cutoffOperatorCore A B e he)) :
    Commute (comparisonOperator A B hB) (gramC (inclusion A)) := by
  apply gram_commutes_of_cutoff (inclusion A) e he
  ext u
  change comparisonOperator A B hB (cutoffC (inclusion A) e he u) =
    cutoffC (inclusion A) e he (comparisonOperator A B hB u)
  refine hd.induction (P := fun w =>
    comparisonOperator A B hB (cutoffC (inclusion A) e he w) =
      cutoffC (inclusion A) e he (comparisonOperator A B hB w))
    ?_ (isClosed_eq (by fun_prop) (by fun_prop)) u
  intro w hw
  rcases hw with ⟨v, hu, hp, hv, hpv⟩
  simp only [cutoffC_apply]
  rw [comparisonOperator_action A B hB _ _ hp hpv,
    comparisonOperator_action A B hB _ _ hu hv]
  simp only [gramC_apply]
  change gram ((inclusion A).restrictScalars ℝ)
      (cutoff ((inclusion A).restrictScalars ℝ) e he v) =
    cutoff ((inclusion A).restrictScalars ℝ) e he
      (gram ((inclusion A).restrictScalars ℝ) v)
  exact gram_inverse ((inclusion A).restrictScalars ℝ) e he
    (gram ((inclusion A).restrictScalars ℝ) v)

/-- Once the invariant core is dense for one epsilon, contraction holds for
EVERY epsilon. This is derived from positivity and operator identities. -/
theorem comparison_cutoff_contraction_of_core (e₀ : ℝ) (he₀ : 0 < e₀)
    (hd : Dense (cutoffOperatorCore A B e₀ he₀))
    (e : ℝ) (he : 0 < e) (u : FormDomain A) :
    comparisonEnergy A B hB (cutoff ((inclusion A).restrictScalars ℝ) e he u) ≤
      comparisonEnergy A B hB u := by
  exact comparisonEnergy_cutoff_le A B hB
    (comparison_commutes_of_core A B hB e₀ he₀ hd) e he u

end QuantumNLS.Ext005CoreCommutationR35b
#print axioms QuantumNLS.Ext005CoreCommutationR35b.comparison_cutoff_contraction_of_core

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005CoreCommutationR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005CoreCommutationR35b." then
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
  Lean.logInfo m!"R35b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
