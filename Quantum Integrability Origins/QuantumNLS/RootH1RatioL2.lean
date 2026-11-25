import QuantumNLS.RootH1RatioOperator
import QuantumNLS.RootPlacementBound

/-! Sharp L² bound for the actual periodic derivative inverse. The finite
Lebesgue measures supply the repaired ROOT-03 measure hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent
  QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioKernel
  QuantumNLS.HaarKernelFactorization
namespace QuantumNLS.RootH1RatioL2
variable {L : ℝ} [hLf : Fact (0 < L)]

lemma normalized_reverse (c L x t : ℝ) :
    normalized c L x t = normalized c L (L-t) (L-x) := by
  unfold normalized wrapExp
  by_cases h : t < x
  · rw [ite_eq_left h, ite_eq_left (show L-x < L-t by linarith)]
    congr 2
    ring
  · rw [ite_eq_right h, ite_eq_right (show ¬ L-x < L-t by linarith)]
    congr 2
    ring

lemma norm_kernel_row {Y : ℝ} (hY : 0 < Y) {x : ℝ} (hx : x ∈ Icc 0 L) :
    (∫ t in (0:ℝ)..L, ‖Rk (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) x t‖) = 1/Y := by
  rw [← integral_normalized hY hLf.out hx]
  apply intervalIntegral.integral_congr_ae
  have hn : ∀ᵐ t : ℝ, t ≠ x := by simp [ae_iff]
  filter_upwards [hn] with t ht _
  exact norm_Rk hY hLf.out ht

lemma norm_kernel_col {Y : ℝ} (hY : 0 < Y) {t : ℝ} (ht : t ∈ Icc 0 L) :
    (∫ x in (0:ℝ)..L, ‖Rk (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) x t‖) = 1/Y := by
  have he : (∫ x in (0:ℝ)..L, ‖Rk (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) x t‖) =
      ∫ x in (0:ℝ)..L, normalized Y L (L-t) (L-x) := by
    apply intervalIntegral.integral_congr_ae
    have hn : ∀ᵐ x : ℝ, t ≠ x := by simp [ae_iff]
    filter_upwards [hn] with x hx _
    rw [norm_Rk hY hLf.out hx, normalized_reverse]
  rw [he, intervalIntegral.integral_comp_sub_left]
  simp only [sub_self, sub_zero]
  exact integral_normalized hY hLf.out ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma integral_rep (f : ℝ → ℝ) :
    (∫ x : AddCircle L, f (rep1 L x)) = ∫ t in (0:ℝ)..L, f t := by
  have hh := AddCircle.intervalIntegral_preimage L 0 (fun x => f (rep1 L x))
  simp only [zero_add] at hh
  rw [← hh]
  apply intervalIntegral.integral_congr_ae
  have hn : ∀ᵐ t : ℝ, t ≠ L := by simp [ae_iff]
  filter_upwards [hn] with t ht hmem
  rw [uIoc_of_le hLf.out.le] at hmem
  rw [rep1_coe L ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht⟩]

lemma resolvent_norm {Y : ℝ} (hY : 0 < Y) : ‖resolvent (L := L) Y‖ ≤ 1/Y := by
  apply QuantumNLS.RootPlacementBound.norm_operator_le_schur
    (R1ker L (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I)) (1/Y) (by positivity)
  · intro x
    change (∫ t : AddCircle L, ‖Rk _ _ (rep1 L x) (rep1 L t)‖) ≤ _
    rw [integral_rep (fun a => ‖Rk (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) (rep1 L x) a‖)]
    exact (norm_kernel_row hY ⟨(rep1_bounds L x).1, (rep1_bounds L x).2.le⟩).le
  · intro t
    change (∫ x : AddCircle L, ‖Rk _ _ (rep1 L x) (rep1 L t)‖) ≤ _
    rw [integral_rep (fun a => ‖Rk (Real.exp (-Y*L)) ((Y:ℂ)*Complex.I) a (rep1 L t)‖)]
    exact (norm_kernel_col hY ⟨(rep1_bounds L t).1, (rep1_bounds L t).2.le⟩).le

lemma resolvent_apply_norm {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    ‖resolvent Y u‖ ≤ ‖u‖/Y := by
  calc
    _ ≤ ‖resolvent (L := L) Y‖*‖u‖ := (RootH1RatioOperator.resolvent Y).le_opNorm u
    _ ≤ (1/Y)*‖u‖ := mul_le_mul_of_nonneg_right (resolvent_norm hY) (norm_nonneg _)
    _ = _ := by ring

#print axioms normalized_reverse
#print axioms norm_kernel_row
#print axioms norm_kernel_col
#print axioms integral_rep
#print axioms resolvent_norm
#print axioms resolvent_apply_norm
end QuantumNLS.RootH1RatioL2

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioL2." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioL2." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
