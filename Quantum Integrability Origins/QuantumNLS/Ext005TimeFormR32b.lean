import QuantumNLS.Ext005TimeFormR113

/-! Operator-norm time regularity on arbitrary finite closed intervals,
derived from the source scalar derivative bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005TimeFormR32b
open Ext005TimeFormR113
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- The literal scalar derivative bound gives an operator-norm Lipschitz bound. -/
theorem time_norm_sub_le (L : ℝ → Q →L[ℂ] Q) (d : ℝ → Q → ℝ)
    (a b C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ t ∈ Icc a b, (L t).IsSymmetric)
    (hd : ∀ u t, t ∈ Icc a b →
      HasDerivWithinAt (fun s => (⟪u, L s u⟫_ℂ).re) (d t u) (Icc a b) t)
    (hdb : ∀ u t, t ∈ Icc a b → |d t u| ≤ C * ‖u‖ ^ 2)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖L t - L s‖ ≤ C * ‖t - s‖ := by
  apply symmetric_norm_le (L t - L s) ((hsym t ht).sub (hsym s hs))
    (C * ‖t - s‖) (mul_nonneg hC (norm_nonneg _))
  intro u
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => hd u z hz) (fun z hz => by simpa only [Real.norm_eq_abs] using hdb u z hz)
    (convex_Icc a b) hs ht
  have htr := congrArg Complex.re (hsym t ht u u)
  have hsr := congrArg Complex.re (hsym s hs u u)
  simp only [ContinuousLinearMap.coe_coe] at htr hsr
  rw [sub_apply, inner_sub_left, Complex.sub_re, htr, hsr]
  simpa only [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using h

lemma time_lipschitz (L : ℝ → Q →L[ℂ] Q) (d : ℝ → Q → ℝ)
    (a b C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ t ∈ Icc a b, (L t).IsSymmetric)
    (hd : ∀ u t, t ∈ Icc a b →
      HasDerivWithinAt (fun s => (⟪u, L s u⟫_ℂ).re) (d t u) (Icc a b) t)
    (hdb : ∀ u t, t ∈ Icc a b → |d t u| ≤ C * ‖u‖ ^ 2) :
    LipschitzOnWith (Real.toNNReal C) L (Icc a b) := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro s hs t ht
  simpa only [Real.coe_toNNReal C hC] using time_norm_sub_le L d a b C hC hsym hd hdb t s ht hs

end QuantumNLS.Ext005TimeFormR32b
#print axioms QuantumNLS.Ext005TimeFormR32b.time_lipschitz

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005TimeFormR32b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005TimeFormR32b." then
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
  Lean.logInfo m!"R32b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
