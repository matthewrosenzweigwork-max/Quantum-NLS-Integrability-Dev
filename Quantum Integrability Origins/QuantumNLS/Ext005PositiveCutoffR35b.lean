import QuantumNLS.Ext005ComplexGramR34b
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Positive comparison forms under the actual Gram cutoff.
The commutation hypothesis is algebraic, not a supplied energy inequality.
Its derivation from the source unbounded-resolvent convention is separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005PositiveCutoffR35b
open Ext005GramResolventR112 Ext005ComplexGramR34b
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ Q := InnerProductSpace.rclikeToReal ℂ Q
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (i : Q →L[ℂ] H) (e : ℝ) (he : 0 < e)

def gramC : Q →L[ℂ] Q := i.adjoint.comp i

def cutoffC : Q →L[ℂ] Q := (inverseC i e he).comp (gramC i)

lemma gramC_apply (u : Q) : gramC i u = gram (i.restrictScalars ℝ) u :=
  (gram_complex i u).symm

lemma cutoffC_apply (u : Q) : cutoffC i e he u = cutoff (i.restrictScalars ℝ) e he u := by
  change inverse (i.restrictScalars ℝ) e he (gramC i u) = _
  rw [gramC_apply]
  rfl

lemma inverse_commutes (T : Q →L[ℂ] Q) (hT : Commute T (gramC i)) :
    Commute T (inverseC i e he) := by
  ext u
  change T (inverse (i.restrictScalars ℝ) e he u) =
    inverse (i.restrictScalars ℝ) e he (T u)
  apply_fun perturbed (i.restrictScalars ℝ) e
  · have hc (v : Q) : gram (i.restrictScalars ℝ) (T v) =
        T (gram (i.restrictScalars ℝ) v) := by
      simpa only [← gramC_apply, mul_apply_eq_comp] using
        (congrArg (fun f : Q →L[ℂ] Q => f v) hT.eq).symm
    rw [perturbed_inverse]
    calc
      _ = T (perturbed (i.restrictScalars ℝ) e
          (inverse (i.restrictScalars ℝ) e he u)) := by
        simp only [perturbed, add_apply, id_apply, smul_apply, hc, map_add,
          map_smul_of_tower]
      _ = T u := congrArg T (perturbed_inverse (i.restrictScalars ℝ) e he u)
  · intro x y h
    simpa only [inverse_perturbed] using congrArg (inverse (i.restrictScalars ℝ) e he) h

lemma cutoff_commutes (T : Q →L[ℂ] Q) (hT : Commute T (gramC i)) :
    Commute T (cutoffC i e he) := by
  exact (inverse_commutes i e he T hT).mul_right hT

lemma gramC_nonneg : 0 ≤ gramC i := by
  exact nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self i)

/-- Algebraic positivity supplies the missing sign in the cutoff-energy
expansion, without postulating contraction in the comparison norm. -/
theorem positive_energy_contraction (T : Q →L[ℂ] Q) (hpos : 0 ≤ T)
    (hcomm : Commute T (gramC i)) (u : Q) :
    (⟪cutoffC i e he u, T (cutoffC i e he u)⟫_ℂ).re ≤ (⟪u, T u⟫_ℂ).re := by
  let P := cutoffC i e he
  let R := inverseC i e he
  have hp : u = P u + e • R u := by
    rw [show P u = cutoff (i.restrictScalars ℝ) e he u from cutoffC_apply i e he u,
      cutoff_eq]
    change u = u - e • R u + e • R u
    abel
  have hg := (hcomm.mul_nonneg hpos (gramC_nonneg i))
  have hcross : 0 ≤ (⟪P u, T (R u)⟫_ℂ).re := by
    have h := (nonneg_iff_isPositive.mp hg).re_inner_nonneg_right (R u)
    change 0 ≤ (⟪R u, T (gramC i (R u))⟫_ℂ).re at h
    have hPR : P u = gramC i (R u) := by
      rw [show P u = cutoff (i.restrictScalars ℝ) e he u from cutoffC_apply i e he u,
        gramC_apply]
      exact (gram_inverse (i.restrictScalars ℝ) e he u).symm
    rw [hPR]
    have hs := (nonneg_iff_isPositive.mp (gramC_nonneg i)).isSymmetric (R u) (T (R u))
    change ⟪gramC i (R u), T (R u)⟫_ℂ = ⟪R u, gramC i (T (R u))⟫_ℂ at hs
    rw [hs]
    have hc := congrArg (fun f : Q →L[ℂ] Q => f (R u)) hcomm.eq
    change T (gramC i (R u)) = gramC i (T (R u)) at hc
    rw [← hc]
    exact h
  have hsym := (nonneg_iff_isPositive.mp hpos).isSymmetric
  have hswap : (⟪R u, T (P u)⟫_ℂ).re = (⟪P u, T (R u)⟫_ℂ).re := by
    have hs := hsym (R u) (P u)
    change ⟪T (R u), P u⟫_ℂ = ⟪R u, T (P u)⟫_ℂ at hs
    rw [← hs]
    exact inner_re_symm (𝕜 := ℂ) (T (R u)) (P u)
  have hself := (nonneg_iff_isPositive.mp hpos).re_inner_nonneg_right (R u)
  have hexpand : (⟪u, T u⟫_ℂ).re = (⟪P u, T (P u)⟫_ℂ).re +
      2 * e * (⟪P u, T (R u)⟫_ℂ).re + e^2 * (⟪R u, T (R u)⟫_ℂ).re := by
    conv_lhs => rw [hp]
    simp only [map_add, map_smul_of_tower, inner_add_left, inner_add_right,
      inner_smul_left_eq_smul, inner_smul_right_eq_smul, Complex.add_re, Complex.smul_re]
    rw [hswap]
    ring
  change (⟪P u, T (P u)⟫_ℂ).re ≤ _
  change 0 ≤ (⟪R u, T (R u)⟫_ℂ).re at hself
  linarith [mul_nonneg he.le hcross, mul_nonneg (sq_nonneg e) hself]

end QuantumNLS.Ext005PositiveCutoffR35b
#print axioms QuantumNLS.Ext005PositiveCutoffR35b.positive_energy_contraction

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PositiveCutoffR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PositiveCutoffR35b." then
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
