import QuantumNLS.Ext005WeakUniformR36b

/-! Uniform weak convergence against continuous time-dependent form tests.
This supplies a net-compatible bridge toward distributional identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology UniformConvergence ENNReal
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005WeakTestsR36b
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- Evaluation on the diagonal is continuous in the two uniform-function
topologies, without countability of the index type. -/
lemma diagonal_continuous (T : Type*) :
    Continuous (fun F : T →ᵤ (T →ᵤ ℝ) =>
      UniformFun.ofFun (fun t => UniformFun.toFun (UniformFun.toFun F t) t)) := by
  have h : LipschitzWith 1 (fun F : T →ᵤ (T →ᵤ ℝ) =>
      UniformFun.ofFun (fun t => UniformFun.toFun (UniformFun.toFun F t) t)) := by
    intro F G
    simp only [ENNReal.coe_one, one_mul]
    apply UniformFun.edist_le.mpr
    intro t
    exact (UniformFun.edist_eval_le (f := UniformFun.toFun F t)
      (g := UniformFun.toFun G t) (x := t)).trans
      (UniformFun.edist_eval_le (f := F) (g := G) (x := t))
  exact h.continuous

/-- A continuous time-dependent test is allowed once weak convergence is
uniform for each fixed form vector and the form vectors are bounded. -/
theorem uniform_continuous_test (a b : ℝ) (w : ℕ → ℝ → Q) (v : ℝ → Q)
    (L : Filter ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ n, ∀ t ∈ Icc a b, ‖w n t‖ ≤ M)
    (hf : ∀ z : Q, TendstoUniformlyOn (fun n t => ⟪z, w n t⟫_ℝ)
      (fun t => ⟪z, v t⟫_ℝ) L (Icc a b))
    (q : ℝ → Q) (hq : ContinuousOn q (Icc a b)) :
    TendstoUniformlyOn (fun n t => ⟪q t, w n t⟫_ℝ)
      (fun t => ⟪q t, v t⟫_ℝ) L (Icc a b) := by
  let U := Icc a b
  let : CompactSpace U := isCompact_iff_compactSpace.mp isCompact_Icc
  let F : ℕ → Q → (U →ᵤ ℝ) := fun n z => UniformFun.ofFun (fun t => ⟪z, w n t⟫_ℝ)
  let V : Q → (U →ᵤ ℝ) := fun z => UniformFun.ofFun (fun t => ⟪z, v t⟫_ℝ)
  have hli (n : ℕ) : LipschitzWith ⟨M, hM⟩ (F n) := by
    apply UniformFun.lipschitzWith_ofFun_iff.mpr
    intro t
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro z y
    rw [← inner_sub_left]
    apply (norm_inner_le_norm _ _).trans
    change ‖z-y‖ * ‖w n t‖ ≤ M * ‖z-y‖
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hb n t t.property) (norm_nonneg _)
  have heq := (LipschitzWith.uniformEquicontinuous F _ hli).equicontinuous
  let J : ℕ → U → (U →ᵤ ℝ) := fun n t => F n (q t)
  have hq' : Continuous (fun t : U => q t) := hq.domRestrict
  have hJ : Equicontinuous J := by
    apply equicontinuous_iff_continuous.mpr
    exact (equicontinuous_iff_continuous.mp heq).comp hq'
  have ht : Tendsto J L (𝓝 (fun t : U => V (q t))) := tendsto_pi_nhds.mpr (fun t =>
    UniformFun.tendsto_iff_tendstoUniformly.mpr
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp (hf (q t))))
  have hu := (hJ.tendsto_uniformFun_iff_pi L (fun t : U => V (q t))).mpr ht
  have hd := (diagonal_continuous U).tendsto _ |>.comp hu
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hd)

end QuantumNLS.Ext005WeakTestsR36b
#print axioms QuantumNLS.Ext005WeakTestsR36b.uniform_continuous_test

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakTestsR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakTestsR36b." then
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
