import QuantumNLS.Ext005PositiveCutoffR35b
import QuantumNLS.Ext005ComparisonEnergyR34b

/-! The bounded representation of the actual comparison B form on Q(A).
All identities use the completed Q(B+1) embedding. No bounded action of B
on Q(A), nor source energy estimate, is supplied as a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005ComparisonFormR35b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
open Ext005GramResolventR112 Ext005PositiveCutoffR35b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (B : NonnegativeOperator H)
  (hB : FormContained A (plusOne B))
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

def comparisonOperator : FormDomain A →L[ℂ] FormDomain A :=
  let K := comparison A (plusOne B) hB
  K.adjoint.comp K - gramC (inclusion A)

lemma comparisonOperator_pair (u v : FormDomain A) :
    ⟪comparisonOperator A B hB u, v⟫_ℂ =
      ⟪comparison A (plusOne B) hB u, comparison A (plusOne B) hB v⟫_ℂ -
        ⟪inclusion A u, inclusion A v⟫_ℂ := by
  change ⟪(comparison A (plusOne B) hB).adjoint
    (comparison A (plusOne B) hB u) - (inclusion A).adjoint (inclusion A u), v⟫_ℂ = _
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

lemma comparisonOperator_diagonal (u : FormDomain A) :
    (⟪u, comparisonOperator A B hB u⟫_ℂ).re = comparisonEnergy A B hB u := by
  calc
    _ = (⟪comparisonOperator A B hB u, u⟫_ℂ).re :=
      inner_re_symm (𝕜 := ℂ) u (comparisonOperator A B hB u)
    _ = _ := by
      rw [comparisonOperator_pair]
      simp only [Complex.sub_re, comparisonEnergy]
      exact congrArg₂ (fun x y : ℝ => x - y)
        (norm_sq_eq_re_inner (𝕜 := ℂ) (comparison A (plusOne B) hB u)).symm
        (norm_sq_eq_re_inner (𝕜 := ℂ) (inclusion A u)).symm

lemma comparisonOperator_nonneg : 0 ≤ comparisonOperator A B hB := by
  apply nonneg_iff_isPositive.mpr
  constructor
  · intro u v
    change ⟪comparisonOperator A B hB u, v⟫_ℂ = ⟪u, comparisonOperator A B hB v⟫_ℂ
    rw [comparisonOperator_pair, ← inner_conj_symm u, comparisonOperator_pair,
      map_sub, inner_conj_symm, inner_conj_symm]
  · intro u
    change 0 ≤ (⟪comparisonOperator A B hB u, u⟫_ℂ).re
    calc
      0 ≤ comparisonEnergy A B hB u := comparisonEnergy_nonneg A B hB u
      _ = (⟪u, comparisonOperator A B hB u⟫_ℂ).re :=
        (comparisonOperator_diagonal A B hB u).symm
      _ = _ := inner_re_symm (𝕜 := ℂ) u (comparisonOperator A B hB u)

/-- On the actual B operator domain, the completed B form equals its
operator pairing against every Q(A) vector. -/
lemma comparisonOperator_on_domain (u v : FormDomain A)
    (hu : inclusion A u ∈ B.op.domain) :
    ⟪comparisonOperator A B hB u, v⟫_ℂ =
      ⟪B.op ⟨inclusion A u, hu⟩, inclusion A v⟫_ℂ := by
  let x : Core (plusOne B) := ⟨inclusion A u, hu⟩
  have hx : comparison A (plusOne B) hB u = (x : FormDomain (plusOne B)) := by
    apply inclusion_injective (plusOne B)
    rw [comparison_pair, inclusion_coe]
    rfl
  rw [comparisonOperator_pair, hx]
  have hp := inclusion_pair (plusOne B) (comparison A (plusOne B) hB v) x
  rw [comparison_pair] at hp
  have hp' := congrArg (starRingEnd ℂ) hp
  simp only [inner_conj_symm] at hp'
  rw [← hp']
  change ⟪B.op ⟨inclusion A u, hu⟩ + (1 : ℂ) • inclusion A u, inclusion A v⟫_ℂ -
    ⟪inclusion A u, inclusion A v⟫_ℂ = _
  rw [one_smul, inner_add_left, add_sub_cancel_right]

/-- The source's actual within-Q(A) B action is represented by J u = G v.
This is an identity, not a bound on the desired evolution. -/
lemma comparisonOperator_action (u v : FormDomain A)
    (hu : inclusion A u ∈ B.op.domain)
    (hv : inclusion A v = B.op ⟨inclusion A u, hu⟩) :
    comparisonOperator A B hB u = gramC (inclusion A) v := by
  apply ext_inner_right ℂ
  intro w
  rw [comparisonOperator_on_domain A B hB u w hu, ← hv]
  exact ((inclusion A).adjoint_inner_left w (inclusion A v)).symm

/-- Actual B-energy contraction, provided the bounded form representative
commutes with the embedding Gram operator. Source-to-commutation is not
asserted by this theorem. -/
theorem comparisonEnergy_cutoff_le (hc : Commute (comparisonOperator A B hB)
    (gramC (inclusion A))) (e : ℝ) (he : 0 < e) (u : FormDomain A) :
    comparisonEnergy A B hB (cutoff ((inclusion A).restrictScalars ℝ) e he u) ≤
      comparisonEnergy A B hB u := by
  have h := positive_energy_contraction (inclusion A) e he
    (comparisonOperator A B hB) (comparisonOperator_nonneg A B hB) hc u
  simpa only [comparisonOperator_diagonal, cutoffC_apply] using h

end QuantumNLS.Ext005ComparisonFormR35b
#print axioms QuantumNLS.Ext005ComparisonFormR35b.comparisonOperator_action
#print axioms QuantumNLS.Ext005ComparisonFormR35b.comparisonEnergy_cutoff_le

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ComparisonFormR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ComparisonFormR35b." then
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
