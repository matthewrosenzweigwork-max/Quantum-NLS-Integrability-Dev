import QuantumNLS.Ext005ComplexForceR113
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Calculus.MeanValue

/-! Derive operator-norm regularity and bounds from the scalar time-derivative
estimate on symmetric forms. Bounded representability of each form is explicit;
no coefficient measurability or uniform operator-norm bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005TimeFormR113
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

lemma symmetric_norm_le (T : Q →L[ℂ] Q) (hs : T.IsSymmetric) (M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ u : Q, |(⟪T u, u⟫_ℂ).re| ≤ M * ‖u‖ ^ 2) : ‖T‖ ≤ M := by
  rw [T.norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro u
  by_cases hu : u = 0
  · simpa [rayleighQuotient, reApplyInnerSelf_apply, hu] using hM
  · rw [rayleighQuotient, reApplyInnerSelf_apply, abs_div, abs_of_nonneg (sq_nonneg ‖u‖)]
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hu))).mpr (hq u)

/-- The literal scalar derivative bound gives an operator-norm Lipschitz bound. -/
theorem time_norm_sub_le (L : ℝ → Q →L[ℂ] Q) (d : ℝ → Q → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ t ∈ Ico (0 : ℝ) 1, (L t).IsSymmetric)
    (hd : ∀ u t, t ∈ Ico (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => (⟪u, L s u⟫_ℂ).re) (d t u) (Ico 0 1) t)
    (hdb : ∀ u t, t ∈ Ico (0 : ℝ) 1 → |d t u| ≤ C * ‖u‖ ^ 2)
    (s t : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    ‖L t - L s‖ ≤ C * ‖t - s‖ := by
  apply symmetric_norm_le (L t - L s) ((hsym t ht).sub (hsym s hs))
    (C * ‖t - s‖) (mul_nonneg hC (norm_nonneg _))
  intro u
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => hd u z hz) (fun z hz => by simpa only [Real.norm_eq_abs] using hdb u z hz)
    (convex_Ico (0 : ℝ) 1) hs ht
  have htr := congrArg Complex.re (hsym t ht u u)
  have hsr := congrArg Complex.re (hsym s hs u u)
  simp only [ContinuousLinearMap.coe_coe] at htr hsr
  rw [sub_apply, inner_sub_left, Complex.sub_re, htr, hsr]
  simpa only [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using h

lemma time_lipschitz (L : ℝ → Q →L[ℂ] Q) (d : ℝ → Q → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ t ∈ Ico (0 : ℝ) 1, (L t).IsSymmetric)
    (hd : ∀ u t, t ∈ Ico (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => (⟪u, L s u⟫_ℂ).re) (d t u) (Ico 0 1) t)
    (hdb : ∀ u t, t ∈ Ico (0 : ℝ) 1 → |d t u| ≤ C * ‖u‖ ^ 2) :
    LipschitzOnWith (Real.toNNReal C) L (Ico (0 : ℝ) 1) := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro s hs t ht
  simpa only [Real.coe_toNNReal C hC] using time_norm_sub_le L d C hC hsym hd hdb t s ht hs

/-- Both coefficient hypotheses needed by the intrinsic D3 theorem are conclusions. -/
theorem time_coefficient_hypotheses (L : ℝ → Q →L[ℂ] Q) (d : ℝ → Q → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hsym : ∀ t ∈ Ico (0 : ℝ) 1, (L t).IsSymmetric)
    (hd : ∀ u t, t ∈ Ico (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => (⟪u, L s u⟫_ℂ).re) (d t u) (Ico 0 1) t)
    (hdb : ∀ u t, t ∈ Ico (0 : ℝ) 1 → |d t u| ≤ C * ‖u‖ ^ 2) :
    AEStronglyMeasurable L (volume.restrict (Ico (0 : ℝ) 1)) ∧
      ∀ T ∈ Ioo (0 : ℝ) 1, ∃ M : ℝ, 0 ≤ M ∧
        ∀ᵐ t, t ∈ Icc 0 T → ‖L t‖ ≤ M := by
  constructor
  · exact (time_lipschitz L d C hC hsym hd hdb).continuousOn.aestronglyMeasurable measurableSet_Ico
  · intro T hT
    refine ⟨‖L 0‖ + C, add_nonneg (norm_nonneg _) hC, Filter.Eventually.of_forall ?_⟩
    intro t ht
    have htI : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_lt hT.2⟩
    have h := time_norm_sub_le L d C hC hsym hd hdb 0 t (by simp) htI
    have hnorm : ‖t - 0‖ ≤ 1 := by rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact htI.2.le
    calc
      ‖L t‖ ≤ ‖L t - L 0‖ + ‖L 0‖ := norm_le_norm_sub_add _ _
      _ ≤ C * ‖t - 0‖ + ‖L 0‖ := by linarith
      _ ≤ ‖L 0‖ + C := by nlinarith

end QuantumNLS.Ext005TimeFormR113
#print axioms QuantumNLS.Ext005TimeFormR113.time_norm_sub_le
#print axioms QuantumNLS.Ext005TimeFormR113.time_coefficient_hypotheses

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005TimeFormR113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005TimeFormR113." then
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
  Lean.logInfo m!"R113 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
