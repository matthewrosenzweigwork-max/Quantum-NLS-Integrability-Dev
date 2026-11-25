import QuantumNLS.Prop022CutoffEvolutionR119
import QuantumNLS.Ext005MomentLimitR109

/-! Quantitative tails in the actual physical number-moment scale.
The bound gains one inverse cutoff from two extra number weights. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped InnerProductSpace Topology
open ContinuousLinearMap
namespace QuantumNLS.Prop022MomentTailR120
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentEnergyR108 Ext005FormCutoffR109 Ext005FormScaleR109
variable {L : ℝ} [Fact (0 < L)]

lemma rootWeight_add_two (j n : ℕ) :
    Real.sqrt (momentWeight (j+2) n) =
      ((n : ℝ)+1) * Real.sqrt (momentWeight j n) := by
  rw [momentWeight, pow_add, Real.sqrt_mul (pow_nonneg (by positivity) j),
    Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (n : ℝ)+1)]
  exact mul_comm _ _

lemma rootCutoff_apply (j N : ℕ) (x : Fock L) (n : ℕ) :
    rootCutoff j N x n =
      if n < N then (Real.sqrt (momentWeight j n) : ℂ) • x n else 0 := by
  simp only [rootCutoff, sum_apply, lp.coeFn_sum, Finset.sum_apply,
    smul_apply, lp.coeFn_smul, Pi.smul_apply]
  by_cases hn : n < N
  · rw [ite_eq_left hn, Finset.sum_eq_single n]
    · rw [projection_same]
    · intro i _ hni
      rw [projection_other L i n (Ne.symm hni), smul_zero]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr hn))
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro i hi
    rw [projection_other L i n (by have := Finset.mem_range.mp hi; omega), smul_zero]

lemma tail_mem (j N : ℕ) (x : momentDomain (L := L) (j+2)) :
    x.val - cutoff N x.val ∈ momentDomain (L := L) j :=
  Submodule.sub_mem _ (domain_mono (by omega) x.property) (cutoff_mem j N x.val)

/-- A quantitative form tail estimate on the maximal physical domain. -/
theorem root_tail_bound (j N : ℕ) (x : momentDomain (L := L) (j+2)) :
    ‖momentRoot j ⟨x.val-cutoff N x.val, tail_mem j N x⟩‖ ≤
      ((N : ℝ)+1)⁻¹ * ‖momentRoot (j+2) x‖ := by
  have hp : 0 < (N : ℝ)+1 := by positivity
  calc
    _ ≤ ‖((((N : ℝ)+1)⁻¹ : ℝ) : ℂ) • momentRoot (j+2) x‖ := by
      apply lp.norm_mono (by norm_num)
      intro n
      change ‖(Real.sqrt (momentWeight j n) : ℂ) • (x.val n-cutoff N x.val n)‖ ≤
        ‖((((N : ℝ)+1)⁻¹ : ℝ) : ℂ) • ((Real.sqrt (momentWeight (j+2) n) : ℂ) • x.val n)‖
      rw [cutoff_apply]
      by_cases hn : n < N
      · simp only [ite_eq_left hn, sub_self, smul_zero, norm_zero]
        exact norm_nonneg _
      · simp only [ite_eq_right hn, sub_zero, norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (inv_nonneg.mpr hp.le)]
        rw [rootWeight_add_two]
        have hNn : (N : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast (by omega : N+1 ≤ n+1)
        have hc : Real.sqrt (momentWeight j n) ≤
            ((N : ℝ)+1)⁻¹ * (((n : ℝ)+1) * Real.sqrt (momentWeight j n)) := by
          rw [← div_eq_inv_mul, le_div_iff₀ hp]
          nlinarith [mul_le_mul_of_nonneg_right hNn (Real.sqrt_nonneg (momentWeight j n))]
        nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (x.val n))]
    _ = _ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hp.le)]

lemma rootCutoff_on_domain (j N : ℕ) (x : momentDomain (L := L) j) :
    rootCutoff j N x.val = momentRoot j ⟨cutoff N x.val, cutoff_mem j N x.val⟩ := by
  rw [rootCutoff_eq, root_cutoff]

/-- The same estimate as an error of the bounded coordinate truncations. -/
theorem root_truncation_error (j N : ℕ) (x : momentDomain (L := L) (j+2)) :
    ‖momentRoot j ⟨x.val, domain_mono (by omega) x.property⟩ - rootCutoff j N x.val‖ ≤
      ((N : ℝ)+1)⁻¹ * ‖momentRoot (j+2) x‖ := by
  rw [rootCutoff_on_domain j N ⟨x.val, domain_mono (by omega) x.property⟩]
  have hh : momentRoot j ⟨x.val-cutoff N x.val, tail_mem j N x⟩ =
      momentRoot j ⟨x.val, domain_mono (by omega) x.property⟩ -
        momentRoot j ⟨cutoff N x.val, cutoff_mem j N x.val⟩ :=
    (momentRoot j).map_sub
      (⟨x.val, domain_mono (by omega) x.property⟩ : momentDomain (L := L) j)
      ⟨cutoff N x.val, cutoff_mem j N x.val⟩
  exact (congrArg norm hh.symm).le.trans (root_tail_bound j N x)

end QuantumNLS.Prop022MomentTailR120
#print axioms QuantumNLS.Prop022MomentTailR120.root_tail_bound
#print axioms QuantumNLS.Prop022MomentTailR120.root_truncation_error

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022MomentTailR120." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022MomentTailR120." then
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
  Lean.logInfo m!"R120 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
