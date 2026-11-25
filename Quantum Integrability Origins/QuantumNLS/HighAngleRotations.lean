import QuantumNLS.CountRotations
import QuantumNLS.HaarNonlinearTail
import QuantumNLS.MarginalPureState
import QuantumNLS.TraceNormTopology

/-! The full product-torus limiting step for R-F1423202, on the actual
count-rotation unitary. Finite support is removed by dominated convergence
in Bethe coefficients, followed by continuity of reduced densities. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.HighAngleRotations
open CountRotations BetheLabels BetheCoefficientTransform
open TensorCarrier PhysicalTensor HaarSpectralTail HaarNonlinearAbstract

/-- Finite truncation of the entire product of circles; omitted angles are zero. -/
def truncate (a : Finset ℤ) (θ : AngleTorus) : AngleTorus :=
  fun n => if n ∈ a then θ n else 1

lemma phase_truncate {N : ℕ} (θ : AngleTorus) (m : MArr N) :
    ∀ᶠ a : Finset ℤ in atTop, countPhase (truncate a θ) m = countPhase θ m := by
  classical
  filter_upwards [eventually_ge_atTop m.val.support] with a ha
  unfold countPhase Finsupp.prod
  apply Finset.prod_congr rfl
  intro n hn
  simp only [truncate, ite_eq_left (ha hn)]

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The literal count rotation is diagonal on every vector, not just the basis. -/
lemma rotation_coeff (b : BetheBasis L N) (θ : AngleTorus) (ψ : HN L N) (m : MArr N) :
    ⟪b m, quantumRotation b θ ψ⟫_ℂ =
      (countPhase θ m : ℂ) * ⟪b m, ψ⟫_ℂ := by
  exact HilbertDiagOp.eig_coeff b
    (quantumRotation b θ).toContinuousLinearEquiv.toContinuousLinearMap
    (fun m => (countPhase θ m : ℂ)) (quantumRotation_basis b θ) m ψ

/-- Strong convergence of finite-support angle truncations, uniformly bounded
by the unitarity of the literal count rotations. -/
theorem rotation_truncate_tendsto (b : BetheBasis L N) (θ : AngleTorus) (ψ : HN L N) :
    Tendsto (fun a : Finset ℤ => quantumRotation b (truncate a θ) ψ) atTop
      (𝓝 (quantumRotation b θ ψ)) := by
  classical
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := tendsto_tsum_of_dominated_convergence
    ((DiagonalMultiplier.summable_sq (b.repr ψ)).mul_left 4)
    (f := fun (a : Finset ℤ) m => ‖((countPhase (truncate a θ) m : ℂ) -
      (countPhase θ m : ℂ)) * b.repr ψ m‖ ^ 2)
    (g := fun _ => (0 : ℝ))
    (fun m => by
      apply tendsto_const_nhds.congr'
      filter_upwards [phase_truncate θ m] with a ha
      simp only [ha, sub_self, zero_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
    (Eventually.of_forall fun a m => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hh : ‖(countPhase (truncate a θ) m : ℂ) - (countPhase θ m : ℂ)‖ ≤ 2 := by
        calc
          _ ≤ ‖(countPhase (truncate a θ) m : ℂ)‖ + ‖(countPhase θ m : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by simp only [Circle.norm_coe]; norm_num
      exact mul_le_mul_of_nonneg_right
        (by nlinarith [norm_nonneg ((countPhase (truncate a θ) m : ℂ) - (countPhase θ m : ℂ))])
        (sq_nonneg _))
  have he (a : Finset ℤ) :
      ‖quantumRotation b (truncate a θ) ψ - quantumRotation b θ ψ‖ ^ 2 =
        ∑' m, ‖((countPhase (truncate a θ) m : ℂ) - (countPhase θ m : ℂ)) * b.repr ψ m‖ ^ 2 := by
    rw [← b.repr.norm_map, DiagonalMultiplier.norm_sq_eq_tsum]
    apply tsum_congr
    intro m
    rw [map_sub]
    change ‖b.repr (quantumRotation b (truncate a θ) ψ) m - b.repr (quantumRotation b θ ψ) m‖ ^ 2 = _
    simp only [HilbertBasis.repr_apply_apply, rotation_coeff]
    rw [sub_mul]
  have hsq : Tendsto (fun a : Finset ℤ =>
      ‖quantumRotation b (truncate a θ) ψ - quantumRotation b θ ψ‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he, tsum_zero] using hs
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

/-- Finite truncations retain the high-angle support condition. -/
lemma truncate_tail (θ : AngleTorus) (R : ℕ) (hθ : ∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = 1)
    (a : Finset ℤ) : ∀ n : ℤ, |n| ≤ (R : ℤ) → truncate a θ n = 1 := by
  classical
  intro n hn
  simp only [truncate]
  split_ifs
  · exact hθ n hn
  · rfl

/-- Marginals are continuous in the underlying vector, even in trace norm;
the operator-norm consequence below suffices for closed trace-norm balls. -/
lemma marginal_tendsto {α : Type*} {l : Filter α} (k : ℕ) (hk : k ≤ N)
    {v : α → HN L N} {w : HN L N} (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun a => reducedDensityN N k hk (v a).val) l
      (𝓝 (reducedDensityN N k hk w.val)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn : Tendsto (fun a => ‖v a - w‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hb : Tendsto (fun a => ‖v a - w‖ * (‖v a‖ + ‖w‖)) l (𝓝 0) := by
    simpa only [zero_mul] using hn.mul (hv.norm.add_const ‖w‖)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun a => ?_) hb
  have h := (TraceClass.norm_le_traceNorm _).trans
    (MarginalPureState.traceNorm_reducedDensityN_sub_le N k hk (v a).val w.val)
  have hp : 0 ≤ ‖v a - w‖ * (‖v a‖ + ‖w‖) := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hp).mp h

/-- A finite-support bound, once proved with constants independent of the
truncation, passes to the literal full product-torus action. -/
theorem finite_to_full (b : BetheBasis L N) (θ : AngleTorus) (ψ : HN L N)
    (k : ℕ) (hk : k ≤ N) (c : ℝ) (hc : 0 ≤ c)
    (hfinite : ∀ a : Finset ℤ,
      TraceClass.traceNorm (reducedDensityN N k hk (quantumRotation b (truncate a θ) ψ).val -
        reducedDensityN N k hk ψ.val) ≤ ENNReal.ofReal c) :
    TraceClass.traceNorm (reducedDensityN N k hk (quantumRotation b θ ψ).val -
      reducedDensityN N k hk ψ.val) ≤ ENNReal.ofReal c := by
  apply TraceNormTopology.traceNorm_le_of_tendsto hc
    ((marginal_tendsto k hk (rotation_truncate_tendsto b θ ψ)).sub_const _)
  exact Eventually.of_forall hfinite

end QuantumNLS.HighAngleRotations

-- Author audits: every own declaration and its generated/transitive constants.
#print axioms QuantumNLS.HighAngleRotations.truncate
#print axioms QuantumNLS.HighAngleRotations.phase_truncate
#print axioms QuantumNLS.HighAngleRotations.rotation_coeff
#print axioms QuantumNLS.HighAngleRotations.rotation_truncate_tendsto
#print axioms QuantumNLS.HighAngleRotations.truncate_tail
#print axioms QuantumNLS.HighAngleRotations.marginal_tendsto
#print axioms QuantumNLS.HighAngleRotations.finite_to_full

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.HighAngleRotations." then
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
