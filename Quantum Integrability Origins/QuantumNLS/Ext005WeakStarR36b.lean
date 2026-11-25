import QuantumNLS.Ext005LimitRegularityR35b
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Function.Holder

/-! Banach--Alaoglu extraction without a separability assumption.
The weak-* L-infinity embedding is the actual integral pairing with L1.
Pointwise Hilbert limits are extracted on a common nontrivial subfilter.
Identification of the L1-dual limit with that pointwise curve is separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ENNReal
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005WeakStarR36b
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

/-- Actual weak-* compactness of a bounded sequence of dual functionals.
The extracted filter refines the supplied filter and is nontrivial. -/
theorem bounded_dual_subfilter (f : Filter ι) [NeBot f]
    (u : ι → StrongDual ℝ E) (M : ℝ) (hb : ∀ n, ‖u n‖ ≤ M) :
    ∃ L : Filter ι, NeBot L ∧ L ≤ f ∧ ∃ v : StrongDual ℝ E,
      ‖v‖ ≤ M ∧ ∀ x : E, Tendsto (fun n => u n x) L (𝓝 (v x)) := by
  let U : ι → WeakDual ℝ E := fun n => StrongDual.toWeakDual (u n)
  have hc := WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) M
  obtain ⟨v, hv, hcl⟩ := hc.exists_mapClusterPt (u := U)
    (Filter.le_principal_iff.mpr (by
      change ∀ᶠ n in f, U n ∈ _
      exact Eventually.of_forall fun n => by
        simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
          U, StrongDual.toStrongDual_toWeakDual] using hb n))
  let L := f ⊓ Filter.comap U (𝓝 v)
  have hL : NeBot L := by
    apply Filter.neBot_inf_comap_iff_map.mpr
    change NeBot (𝓝 v ⊓ Filter.map U f) at hcl
    rwa [inf_comm]
  refine ⟨L, hL, inf_le_left, WeakDual.toStrongDual v, ?_, ?_⟩
  · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hv
  · intro x
    have ht : Tendsto U L (𝓝 v) := Filter.tendsto_iff_comap.mpr inf_le_right
    exact ((WeakDual.eval_continuous x).tendsto v).comp ht

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable {T : Type*}

/-- Tychonoff plus Riesz extracts pointwise weak Q limits at every index,
with the same uniform norm bound. No subsequence or separability is assumed. -/
theorem bounded_pointwise_subfilter (f : Filter ι) [NeBot f]
    (u : ι → T → Q) (M : ℝ) (hb : ∀ n t, ‖u n t‖ ≤ M) :
    ∃ L : Filter ι, NeBot L ∧ L ≤ f ∧ ∃ v : T → Q,
      (∀ t, ‖v t‖ ≤ M) ∧ ∀ t z, Tendsto (fun n => ⟪z, u n t⟫_ℝ) L (𝓝 ⟪z, v t⟫_ℝ) := by
  let U : ι → T → WeakDual ℝ Q := fun n t =>
    StrongDual.toWeakDual (toDual ℝ Q (u n t))
  let K : Set (T → WeakDual ℝ Q) := {v | ∀ t,
    WeakDual.toStrongDual (v t) ∈ Metric.closedBall (0 : StrongDual ℝ Q) M}
  have hK : IsCompact K := isCompact_pi_infinite (fun _ : T =>
    WeakDual.isCompact_closedBall (0 : StrongDual ℝ Q) M)
  obtain ⟨v, hv, hcl⟩ := hK.exists_mapClusterPt (u := U)
    (Filter.le_principal_iff.mpr (by
      change ∀ᶠ n in f, U n ∈ K
      exact Eventually.of_forall fun n t => by
        simpa only [Metric.mem_closedBall, dist_zero_right, U,
          StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hb n t))
  let L := f ⊓ Filter.comap U (𝓝 v)
  have hL : NeBot L := by
    apply Filter.neBot_inf_comap_iff_map.mpr
    change NeBot (𝓝 v ⊓ Filter.map U f) at hcl
    rwa [inf_comm]
  let w : T → Q := fun t => (toDual ℝ Q).symm (WeakDual.toStrongDual (v t))
  refine ⟨L, hL, inf_le_left, w, ?_, ?_⟩
  · intro t
    simpa only [w, LinearIsometryEquiv.norm_map, Metric.mem_closedBall, dist_zero_right] using hv t
  · intro t z
    have ht : Tendsto U L (𝓝 v) := Filter.tendsto_iff_comap.mpr inf_le_right
    have hc := ((WeakDual.eval_continuous z).comp (continuous_apply t)).tendsto v |>.comp ht
    have he : ⟪z, w t⟫_ℝ = (v t) z := by
      rw [real_inner_comm]
      exact toDual_symm_apply
    rw [he]
    simpa only [U, Function.comp_def, StrongDual.toWeakDual_apply,
      toDual_apply_apply, real_inner_comm] using hc

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

def pairingOperator : Lp Q ∞ μ →L[ℝ] StrongDual ℝ (Lp Q 1 μ) :=
  (innerSL ℝ (E := Q)).lpPairing μ ∞ 1

/-- The actual bounded integral functional induced by an L-infinity path. -/
def linftyFunctional (u : Lp Q ∞ μ) : StrongDual ℝ (Lp Q 1 μ) :=
  pairingOperator μ u

omit [CompleteSpace Q] in
lemma linftyFunctional_apply (u : Lp Q ∞ μ) (v : Lp Q 1 μ) :
    linftyFunctional μ u v = ∫ t, ⟪u t, v t⟫_ℝ ∂μ :=
  (innerSL ℝ).lpPairing_eq_integral u v

omit [CompleteSpace Q] in
lemma linftyFunctional_norm_le (u : Lp Q ∞ μ) : ‖linftyFunctional μ u‖ ≤ ‖u‖ := by
  apply (linftyFunctional μ u).opNorm_le_bound (norm_nonneg u)
  intro x
  rw [linftyFunctional_apply]
  have he : L1.integral ((innerSL ℝ (E := Q)).holder 1 u x) =
      ∫ t, ⟪u t, x t⟫_ℝ ∂μ := by
    rw [L1.integral_eq_integral]
    exact integral_congr_ae ((innerSL ℝ (E := Q)).coeFn_holder u x)
  rw [← he]
  calc
    _ ≤ ‖(innerSL ℝ (E := Q)).holder 1 u x‖ := L1.norm_integral_le _
    _ ≤ ‖innerSL ℝ (E := Q)‖ * ‖u‖ * ‖x‖ :=
      (innerSL ℝ (E := Q)).norm_holder_apply_apply_le u x
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (norm_innerSL_le (𝕜 := ℝ) (E := Q))
        (mul_nonneg (norm_nonneg u) (norm_nonneg x))
      simpa only [mul_assoc, one_mul] using h

omit [CompleteSpace Q] in
/-- Weak-* extraction for genuinely bounded L-infinity functions through
their integral L1 pairing. Representation of the dual limit is not assumed. -/
theorem linfty_weakStar_subfilter (f : Filter ι) [NeBot f]
    (u : ι → Lp Q ∞ μ) (M : ℝ) (hb : ∀ n, ‖u n‖ ≤ M) :
    ∃ L : Filter ι, NeBot L ∧ L ≤ f ∧ ∃ v : StrongDual ℝ (Lp Q 1 μ),
      ‖v‖ ≤ M ∧
      ∀ x : Lp Q 1 μ, Tendsto (fun n => ∫ t, ⟪u n t, x t⟫_ℝ ∂μ) L (𝓝 (v x)) := by
  have hb' (n : ι) : ‖linftyFunctional μ (u n)‖ ≤ M :=
    (linftyFunctional_norm_le μ (u n)).trans (hb n)
  obtain ⟨L, hL, hLf, v, hv, ht⟩ := bounded_dual_subfilter f (fun n => linftyFunctional μ (u n)) _ hb'
  refine ⟨L, hL, hLf, v, hv, ?_⟩
  simpa only [linftyFunctional_apply] using ht

end QuantumNLS.Ext005WeakStarR36b
#print axioms QuantumNLS.Ext005WeakStarR36b.bounded_pointwise_subfilter
#print axioms QuantumNLS.Ext005WeakStarR36b.linfty_weakStar_subfilter

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakStarR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakStarR36b." then
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
  Lean.logInfo m!"R36b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
