import QuantumNLS.GridStrongSum
import QuantumNLS.TraceClass

/-! Scalar and Hilbert-space estimates used by the SOURCE proof of
R-36C23346(c). These estimates do not assume norm convergence of the kernels.
The energy compactness and evolving-marginal bindings remain separate tasks. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.LinearTailSourceEstimates
open GridStrongSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The finite-rank compression inequality in the printed proof, at each
vector. This even holds for an arbitrary bounded Q; projection properties
are needed later to interpret its remainder as a trace tail. -/
theorem compression_sq (T Q : H →L[ℂ] H) (v : H) :
    ‖T v‖ ^ 2 ≤ 2 * ‖T (Q v)‖ ^ 2 + 2 * ‖T‖ ^ 2 * ‖v - Q v‖ ^ 2 := by
  have he : T v = T (Q v) + T (v - Q v) := by rw [← map_add, add_sub_cancel]
  have htri : ‖T v‖ ≤ ‖T (Q v)‖ + ‖T (v - Q v)‖ := by rw [he]; exact norm_add_le _ _
  have hop := T.le_opNorm (v - Q v)
  have hsq : ‖T v‖ ^ 2 ≤ (‖T (Q v)‖ + ‖T (v - Q v)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hsq2 : ‖T (v - Q v)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖v - Q v‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hop 2
  nlinarith [sq_nonneg (‖T (Q v)‖ - ‖T (v - Q v)‖)]

/-- Cauchy-Schwarz for an overlapping pair of selfadjoint placements.
The right side depends on T applied to the state, so compact strong
convergence suffices; operator-norm convergence is unnecessary. -/
theorem commutator_expectation (T J : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hJ : IsSelfAdjoint J) (v : H) :
    ‖⟪v, (T * J - J * T) v⟫_ℂ‖ ≤ 2 * ‖T v‖ * ‖J‖ * ‖v‖ := by
  have ht : ⟪v, T (J v)⟫_ℂ = ⟪T v, J v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    rw [show ContinuousLinearMap.adjoint T = T from hT]
  have hj : ⟪v, J (T v)⟫_ℂ = ⟪J v, T v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    rw [show ContinuousLinearMap.adjoint J = J from hJ]
  change ‖⟪v, T (J v) - J (T v)⟫_ℂ‖ ≤ _
  rw [inner_sub_right]
  rw [ht, hj]
  calc
    ‖⟪T v, J v⟫_ℂ - ⟪J v, T v⟫_ℂ‖ ≤ ‖⟪T v, J v⟫_ℂ‖ + ‖⟪J v, T v⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ ‖T v‖ * ‖J v‖ + ‖J v‖ * ‖T v‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ 2 * ‖T v‖ * ‖J‖ * ‖v‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (J.le_opNorm v) (norm_nonneg (T v))]

variable (L : ℝ) [Fact (0 < L)]

/-- The exact factorial majorant makes the source's rank-weighted series
summable, with r=n+1. -/
theorem summable_majorant (κ : ℝ) (hκ : 0 ≤ κ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * κ ^ n * Bd L (n + 1)) := by
  let A := Real.exp 1 * (L / Real.pi) * max κ 1
  have hs : Summable (fun n : ℕ =>
      (2 * Real.pi ^ 2 / 3) * (A ^ (n + 1) / ((n + 1).factorial : ℝ))) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial A)).mul_left _
  apply Summable.of_nonneg_of_le (fun n => by
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hκ _)) (Bd_nonneg L _)) _ hs
  intro n
  have h := summand_key L 1 0 κ hκ n
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one, Nat.factorial_one, Nat.cast_one,
    one_mul] at h
  have hfac : (0 : ℝ) < (n + 1).factorial := by positivity
  unfold Bd
  calc
    ((n : ℝ) + 1) * κ ^ n *
        (2 * Real.pi ^ 2 / (3 * ((n + 1).factorial : ℝ)) * (L / Real.pi) ^ (n + 1)) =
      (2 * Real.pi ^ 2 / 3) *
        ((((n : ℝ) + 1) * κ ^ n * (L / Real.pi) ^ (n + 1)) / ((n + 1).factorial : ℝ)) := by ring
    _ ≤ (2 * Real.pi ^ 2 / 3) * (A ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right h hfac.le

/-- Dominated convergence with the exact factorial bound, giving precisely
the source error series once e_{r,E} has been constructed and shown to vanish.
This theorem is a reusable implication; it does not postulate that construction. -/
theorem error_series_tendsto (κ : ℝ) (hκ : 0 ≤ κ)
    (e : ℕ → ℕ → ℝ)
    (he : ∀ n R, 0 ≤ e n R)
    (hb : ∀ n R, e n R ≤ Bd L (n + 1))
    (hlim : ∀ n, Tendsto (e n) atTop (𝓝 0)) :
    (∀ R, Summable (fun n : ℕ => ((n : ℝ) + 1) * κ ^ n * e n R)) ∧
      Tendsto (fun R => ∑' n : ℕ, ((n : ℝ) + 1) * κ ^ n * e n R) atTop (𝓝 0) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * κ ^ n := fun n => by positivity
  have hdom : ∀ R n : ℕ, ‖((n : ℝ) + 1) * κ ^ n * e n R‖ ≤
      ((n : ℝ) + 1) * κ ^ n * Bd L (n + 1) := by
    intro R n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg n) (he n R))]
    exact mul_le_mul_of_nonneg_left (hb n R) (hnonneg n)
  refine ⟨fun R => Summable.of_norm_bounded (summable_majorant L κ hκ) (hdom R), ?_⟩
  have hp : ∀ n : ℕ, Tendsto (fun R => ((n : ℝ) + 1) * κ ^ n * e n R) atTop (𝓝 (0 : ℝ)) := by
    intro n
    simpa only [mul_zero] using (hlim n).const_mul (((n : ℝ) + 1) * κ ^ n)
  have hd := tendsto_tsum_of_dominated_convergence
    (summable_majorant L κ hκ) hp (Filter.Eventually.of_forall hdom)
  simpa only [tsum_zero] using hd

/-- Integrating a uniform derivative bound over the source time window.
The mean value inequality supplies the same integral estimate for either
sign of time. -/
theorem integrated_norm_bound {F : ℝ → ℝ} {B s : ℝ} (hB : 0 ≤ B)
    (hs : |s| ≤ 1)
    (hF : ∀ q ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ F q)
    (hd : ∀ q ∈ Set.Icc (-1 : ℝ) 1, ‖deriv F q‖ ≤ B) :
    ‖F s - F 0‖ ≤ B := by
  have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hss : s ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hs
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hF hd (convex_Icc _ _) h0 hss
  refine h.trans ?_
  apply mul_le_of_le_one_right hB
  simpa only [sub_zero, Real.norm_eq_abs] using hs

/-- Trace-norm duality after time integration. This is the final analytic
implication of the source route, with every required finite dual test and
its derivative estimate explicit. It does not assert those derivative
estimates for the physical evolution. -/
theorem traceNorm_bound_of_time_derivative {ι : Type*} (b : HilbertBasis ι ℂ H)
    (C : ℝ → H →L[ℂ] H) {B s : ℝ} (hB : 0 ≤ B) (hs : |s| ≤ 1)
    (hF : ∀ X : H →L[ℂ] H, ‖X‖ ≤ 1 → ∀ a : Finset ι,
      ∀ q ∈ Set.Icc (-1 : ℝ) 1,
        DifferentiableAt ℝ (fun t => (∑ i ∈ a, ⟪X (b i), C t (b i)⟫_ℂ).re) q)
    (hd : ∀ X : H →L[ℂ] H, ‖X‖ ≤ 1 → ∀ a : Finset ι,
      ∀ q ∈ Set.Icc (-1 : ℝ) 1,
        ‖deriv (fun t => (∑ i ∈ a, ⟪X (b i), C t (b i)⟫_ℂ).re) q‖ ≤ B) :
    TraceClass.traceNorm (C s - C 0) ≤ ENNReal.ofReal B := by
  apply TraceClass.traceNorm_le_of_forall b
  intro X hX a
  have h := integrated_norm_bound hB hs (hF X hX a) (hd X hX a)
  have hr := (le_abs_self
    ((∑ i ∈ a, ⟪X (b i), C s (b i)⟫_ℂ).re -
      (∑ i ∈ a, ⟪X (b i), C 0 (b i)⟫_ℂ).re)).trans (by simpa only [Real.norm_eq_abs] using h)
  simp only [sub_apply, inner_sub_right, Finset.sum_sub_distrib]
  change ((∑ i ∈ a, ⟪X (b i), C s (b i)⟫_ℂ) -
    (∑ i ∈ a, ⟪X (b i), C 0 (b i)⟫_ℂ)).re ≤ B
  rw [Complex.sub_re]
  exact hr

end QuantumNLS.LinearTailSourceEstimates

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.LinearTailSourceEstimates.compression_sq
#print axioms QuantumNLS.LinearTailSourceEstimates.commutator_expectation
#print axioms QuantumNLS.LinearTailSourceEstimates.summable_majorant
#print axioms QuantumNLS.LinearTailSourceEstimates.error_series_tendsto
#print axioms QuantumNLS.LinearTailSourceEstimates.integrated_norm_bound
#print axioms QuantumNLS.LinearTailSourceEstimates.traceNorm_bound_of_time_derivative

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.LinearTailSourceEstimates." then
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
