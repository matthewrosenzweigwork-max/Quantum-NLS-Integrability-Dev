import QuantumNLS.Ext005WeakEquationR37b

/-! Weak-equation identification from the actual twice-smoothed derivative.
Only the smoothed evolving vectors need a uniform form bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005SmoothedWeakR37b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005RegularizedR33b
open Ext005ConsistencyR33b Ext005WeakUniformR36b Ext005NetForceR36b
open Ext005WeakEquationR37b Ext005IntervalChainR111
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma gram_cutoff (i : Q →L[ℝ] H) (n : ℕ) (v : Q) :
    gram i (C i n v) = C i n (gram i v) :=
  gram_inverse i (epsilon n) (epsilon_pos n) (gram i v)

/-- The exact smoothed derivative contains TWO outer cutoffs. -/
lemma smoothed_derivative (i : Q →L[ℝ] H) (n : ℕ) (F : ℝ → Q →L[ℝ] Q)
    (u : ℝ → Q) (t : ℝ)
    (hd : HasDerivAt u (generator i (epsilon n) (epsilon_pos n) (F t) (u t)) t) :
    HasDerivAt (fun r => gram i (C i n (u r)))
      (C i n (C i n (F t (C i n (u t))))) t := by
  have h := ((gram i).comp (C i n)).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun r => gram i (C i n (u r)))
    (gram i (C i n (generator i (epsilon n) (epsilon_pos n) (F t) (u t)))) t at h
  rw [gram_cutoff, generator_antidual] at h
  exact h

/-- Remove both outer cutoffs uniformly in each scalar test. -/
theorem twice_force_uniform (i : Q →L[ℝ] H) (hi : Function.Injective i)
    (a b : ℝ) (F : ℝ → Q →L[ℝ] Q) (w : ℕ → ℝ → Q) (v : ℝ → Q)
    (L : Filter ℕ) (hL : L ≤ atTop) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hb : ∀ n, ∀ t ∈ Icc a b, ‖w n t‖ ≤ M)
    (hF : ContinuousOn F (Icc a b)) (hFb : ∀ t ∈ Icc a b, ‖F t‖ ≤ N)
    (hf : ∀ z : Q, TendstoUniformlyOn (fun n t => ⟪z, w n t⟫_ℝ)
      (fun t => ⟪z, v t⟫_ℝ) L (Icc a b)) (z : Q) :
    TendstoUniformlyOn (fun n t => ⟪z, C i n (C i n (F t (w n t)))⟫_ℝ)
      (fun t => ⟪z, F t (v t)⟫_ℝ) L (Icc a b) := by
  have hb' (n : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖C i n (F t (w n t))‖ ≤ N*M :=
    (cutoff_norm_le i (epsilon n) (epsilon_pos n) _).trans
      (((F t).le_opNorm _).trans (mul_le_mul (hFb t ht) (hb n t ht) (norm_nonneg _) hN))
  have hf' := fun q => outer_force_uniform i hi a b F w v L hL M N hM hb hF hFb hf q
  have h := outer_force_uniform i hi a b (fun _ => ContinuousLinearMap.id ℝ Q)
    (fun n t => C i n (F t (w n t))) (fun t => F t (v t)) L hL (N*M) 1
    (mul_nonneg hN hM) hb' continuousOn_const (fun _ _ => norm_id_le) hf' z
  simpa only [id_apply] using h

/-- The original weak equation follows from actual regularized ODEs,
energy bounds, the antidual time modulus and extracted pointwise weak
convergence. Neither the limit equation nor L1-dual representation is input. -/
theorem regularized_weak_limit (i : Q →L[ℝ] H) (hi : Function.Injective i)
    (a b : ℝ) (hab : a ≤ b) (F : ℝ → Q →L[ℝ] Q)
    (u : ℕ → ℝ → Q) (v : ℝ → Q) (L : Filter ℕ) [NeBot L] (hL : L ≤ atTop)
    (M N K : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hc : ∀ n, Continuous (u n))
    (hd : ∀ n t, t ∈ Icc a b → HasDerivAt (u n)
      (generator i (epsilon n) (epsilon_pos n) (F t) (u n t)) t)
    (hb : ∀ n, ∀ t ∈ Icc a b, ‖C i n (u n t)‖ ≤ M)
    (hv : ∀ t ∈ Icc a b, ‖v t‖ ≤ M)
    (hl : ∀ n, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ‖gram i (C i n (u n t)) - gram i (C i n (u n s))‖ ≤ K * ‖t-s‖)
    (hw : ∀ t ∈ Icc a b, ∀ z : Q,
      Tendsto (fun n => ⟪z, C i n (u n t)⟫_ℝ) L (𝓝 ⟪z, v t⟫_ℝ))
    (hF : ContinuousOn F (Icc a b)) (hFb : ∀ t ∈ Icc a b, ‖F t‖ ≤ N) :
    WeakDerivativeOn (Ioo a b) (fun t => gram i (v t)) (fun t => F t (v t)) := by
  let w := fun n t => C i n (u n t)
  have huc := fun n => (C i n).continuous.comp (hc n)
  have hgc (n : ℕ) : ContinuousOn (fun t => C i n (C i n (F t (w n t)))) (Icc a b) :=
    (C i n).continuous.comp_continuousOn
      ((C i n).continuous.comp_continuousOn (hF.clm_apply (huc n).continuousOn))
  have hu := fun z => uniform_weak_pair i hi a b w v L M K hM hK hb hv hl hw z
  apply weak_limit a b (fun n t => gram i (w n t))
    (fun n t => C i n (C i n (F t (w n t))))
    (fun t => gram i (v t)) (fun t => F t (v t)) L
    (fun n => ((gram i).continuous.comp (huc n)).continuousOn) hgc
  · intro z
    simpa only [← gram_symm] using hu (gram i z)
  · exact twice_force_uniform i hi a b F w v L hL M N hM hN hb hF hFb hu
  · intro n
    exact classical_weak a b hab _ _
      (((gram i).continuous.comp (huc n)).continuousOn) (hgc n)
      (fun t ht => smoothed_derivative i n F (u n) t (hd n t ht))

end QuantumNLS.Ext005SmoothedWeakR37b
#print axioms QuantumNLS.Ext005SmoothedWeakR37b.regularized_weak_limit

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SmoothedWeakR37b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SmoothedWeakR37b." then
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
  Lean.logInfo m!"R37b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
