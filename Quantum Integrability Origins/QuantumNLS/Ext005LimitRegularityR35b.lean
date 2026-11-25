import QuantumNLS.Ext005WeakLimitR34b
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-! Regularity and initial trace of bounded weak form limits.
This derives an ambient continuous representative from antidual continuity;
no ambient continuity of the limiting curve is assumed. Extraction of a
bounded weak limit is a separate obligation, not asserted here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005LimitRegularityR35b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005ConsistencyR33b
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace Q] in
lemma weak_norm_bound (v : ℕ → Q) (w : Q) (M : ℝ)
    (hb : ∀ n, ‖v n‖ ≤ M)
    (hw : ∀ z : Q, Tendsto (fun n => ⟪z, v n⟫_ℝ) atTop (𝓝 ⟪z, w⟫_ℝ)) :
    ‖w‖ ≤ M := by
  have h := le_of_tendsto (hw w) (Eventually.of_forall fun n =>
    (real_inner_le_norm w (v n)).trans (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg w)))
  rw [real_inner_self_eq_norm_sq] at h
  have hM : 0 ≤ M := (norm_nonneg (v 0)).trans (hb 0)
  nlinarith [norm_nonneg w]

/-- The interpolation bound that turns bounded form representatives and
antidual continuity into actual ambient norm continuity. -/
lemma embedding_interpolation (i : Q →L[ℝ] H) (u v : Q) :
    ‖i u - i v‖^2 ≤ (‖u‖ + ‖v‖) * ‖gram i u - gram i v‖ := by
  have h : ‖i u - i v‖^2 = ⟪gram i (u-v), u-v⟫_ℝ := by
    rw [gram_pair, map_sub, real_inner_self_eq_norm_sq]
  rw [h]
  calc
    _ ≤ ‖gram i (u-v)‖ * ‖u-v‖ := real_inner_le_norm _ _
    _ ≤ ‖gram i (u-v)‖ * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le u v) (norm_nonneg _)
    _ = _ := by rw [map_sub, mul_comm]

theorem embedded_continuous_of_gram (i : Q →L[ℝ] H) (U : Set ℝ)
    (w : ℝ → Q) (M : ℝ) (_hM : 0 ≤ M)
    (hb : ∀ t ∈ U, ‖w t‖ ≤ M)
    (hc : ContinuousOn (fun t => gram i (w t)) U) :
    ContinuousOn (fun t => i (w t)) U := by
  intro t ht
  change Tendsto (fun r => i (w r)) (𝓝[U] t) (𝓝 (i (w t)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hg : Tendsto (fun r => ‖gram i (w r) - gram i (w t)‖) (𝓝[U] t) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hc t ht).sub_const (gram i (w t))).norm
  have hsq : Tendsto (fun r => ‖i (w r) - i (w t)‖^2) (𝓝[U] t) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun r => sq_nonneg _) ?_
      (show Tendsto (fun r => 2*M * ‖gram i (w r)-gram i (w t)‖)
        (𝓝[U] t) (𝓝 0) by simpa using hg.const_mul (2*M))
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (embedding_interpolation i (w r) (w t)).trans
      (mul_le_mul_of_nonneg_right (by linarith [hb r hr, hb t ht]) (norm_nonneg _))
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn

/-- Bounds and antidual Lipschitz estimates survive pointwise weak
convergence. This is a derived estimate on the limit, not an assumption. -/
theorem weak_gram_lipschitz (i : Q →L[ℝ] H) (U : Set ℝ)
    (w : ℕ → ℝ → Q) (v : ℝ → Q) (K : ℝ)
    (hb : ∀ n, ∀ s ∈ U, ∀ t ∈ U,
      ‖gram i (w n t) - gram i (w n s)‖ ≤ K * ‖t-s‖)
    (hw : ∀ t ∈ U, ∀ z : Q,
      Tendsto (fun n => ⟪z, w n t⟫_ℝ) atTop (𝓝 ⟪z, v t⟫_ℝ)) :
    ∀ s ∈ U, ∀ t ∈ U, ‖gram i (v t) - gram i (v s)‖ ≤ K * ‖t-s‖ := by
  intro s hs t ht
  apply weak_norm_bound (fun n => gram i (w n t) - gram i (w n s))
    (gram i (v t) - gram i (v s)) (K * ‖t-s‖) (fun n => hb n s hs t ht)
  intro z
  have h := (hw t ht (gram i z)).sub (hw s hs (gram i z))
  simpa only [inner_sub_right, gram_symm] using h

/-- A bounded weak form limit with the inherited antidual time estimate
has actual form representatives at every time and is norm-continuous in H.
The pointwise weak limit is still an input, not an extracted sequence. -/
theorem bounded_weak_limit_continuous (i : Q →L[ℝ] H) (U : Set ℝ)
    (w : ℕ → ℝ → Q) (v : ℝ → Q) (M K : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hb : ∀ n, ∀ t ∈ U, ‖w n t‖ ≤ M)
    (hl : ∀ n, ∀ s ∈ U, ∀ t ∈ U,
      ‖gram i (w n t) - gram i (w n s)‖ ≤ K * ‖t-s‖)
    (hw : ∀ t ∈ U, ∀ z : Q,
      Tendsto (fun n => ⟪z, w n t⟫_ℝ) atTop (𝓝 ⟪z, v t⟫_ℝ)) :
    (∀ t ∈ U, ‖v t‖ ≤ M) ∧ ContinuousOn (fun t => i (v t)) U := by
  have hbv (t : ℝ) (ht : t ∈ U) : ‖v t‖ ≤ M :=
    weak_norm_bound (fun n => w n t) (v t) M (fun n => hb n t ht) (hw t ht)
  refine ⟨hbv, embedded_continuous_of_gram i U v M hM hbv ?_⟩
  have hgl := weak_gram_lipschitz i U w v K hl hw
  have hc : LipschitzOnWith ⟨K, hK⟩ (fun t => gram i (v t)) U := by
    exact lipschitzOnWith_iff_norm_sub_le.mpr (fun t ht s hs => hgl s hs t ht)
  exact hc.continuousOn

/-- For the actual regularized ODE, the time modulus of the smoothed
antidual path is independent of the inverse norm. The bound uses P_e u_e
only, so it applies to the forward Gronwall estimate. -/
theorem smoothed_antidual_time_bound (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e)
    (a b : ℝ) (u : ℝ → Q) (F : ℝ → Q →L[ℝ] Q) (N M : ℝ) (hN : 0 ≤ N)
    (hd : ∀ t ∈ Icc a b, HasDerivAt u
      (Ext005RegularizedR33b.generator i e he (F t) (u t)) t)
    (hF : ∀ t ∈ Icc a b, ‖F t‖ ≤ N)
    (hb : ∀ t ∈ Icc a b, ‖cutoff i e he (u t)‖ ≤ M) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ‖gram i (cutoff i e he (u t)) - gram i (cutoff i e he (u s))‖ ≤ N*M*‖t-s‖ := by
  let P := cutoff i e he
  let G := gram i
  have hcomm (v : Q) : G (P v) = P (G v) := gram_inverse i e he (gram i v)
  have hdiff (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun r => G (P (u r)))
        (G (P (Ext005RegularizedR33b.generator i e he (F t) (u t)))) (Icc a b) t :=
    (((G.comp P).hasFDerivAt).comp_hasDerivAt t (hd t ht)).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      ‖G (P (Ext005RegularizedR33b.generator i e he (F t) (u t)))‖ ≤ N*M := by
    rw [hcomm, generator_antidual]
    exact (cutoff_norm_le i e he _).trans ((cutoff_norm_le i e he _).trans
      (((F t).le_opNorm _).trans (mul_le_mul (hF t ht) (hb t ht) (norm_nonneg _) hN)))
  intro s hs t ht
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hdiff hbound (convex_Icc a b) hs ht

/-- The prescribed initial form vector passes to a weakly converging
smoothed sequence, using the constructed cutoff's strong convergence. -/
theorem weak_initial_trace (i : Q →L[ℝ] H) (hi : Function.Injective i)
    (u : ℕ → ℝ → Q) (w : ℝ → Q) (s : ℝ) (u₀ : Q)
    (hinit : ∀ n, u n s = u₀)
    (hw : ∀ z : Q, Tendsto (fun n => ⟪z, C i n (u n s)⟫_ℝ) atTop (𝓝 ⟪z, w s⟫_ℝ)) :
    w s = u₀ := by
  apply ext_inner_left ℝ
  intro z
  have ht := (tendsto_const_nhds.inner (C_tendsto i hi u₀) :
    Tendsto (fun n => ⟪z, C i n u₀⟫_ℝ) atTop (𝓝 ⟪z, u₀⟫_ℝ))
  have hh := hw z
  simp only [hinit] at hh
  exact tendsto_nhds_unique hh ht

end QuantumNLS.Ext005LimitRegularityR35b
#print axioms QuantumNLS.Ext005LimitRegularityR35b.embedded_continuous_of_gram
#print axioms QuantumNLS.Ext005LimitRegularityR35b.weak_initial_trace
#print axioms QuantumNLS.Ext005LimitRegularityR35b.bounded_weak_limit_continuous
#print axioms QuantumNLS.Ext005LimitRegularityR35b.smoothed_antidual_time_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005LimitRegularityR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005LimitRegularityR35b." then
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
