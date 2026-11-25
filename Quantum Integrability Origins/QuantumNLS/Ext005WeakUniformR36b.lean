import QuantumNLS.Ext005WeakSubfilterR36b
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Upgrade the extracted pointwise weak convergence to uniform scalar
convergence on a finite interval. This works for arbitrary nontrivial
subfilters, without using sequential dominated convergence on a net. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology UniformConvergence
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005WeakUniformR36b
open Ext005GramResolventR112 Ext005GramConvergenceR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniform convergence of the antidual scalar pairings by the actual
uniform time modulus and compactness of the time interval. -/
theorem uniform_gram_pair (i : Q →L[ℝ] H) (a b : ℝ)
    (w : ℕ → ℝ → Q) (v : ℝ → Q) (L : Filter ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hl : ∀ n, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ‖gram i (w n t) - gram i (w n s)‖ ≤ K * ‖t-s‖)
    (hw : ∀ t ∈ Icc a b, ∀ z : Q,
      Tendsto (fun n => ⟪z, w n t⟫_ℝ) L (𝓝 ⟪z, v t⟫_ℝ)) (z : Q) :
    TendstoUniformlyOn (fun n t => ⟪z, gram i (w n t)⟫_ℝ)
      (fun t => ⟪z, gram i (v t)⟫_ℝ) L (Icc a b) := by
  let F : ℕ → Icc a b → ℝ := fun n t => ⟪z, gram i (w n t)⟫_ℝ
  let V : Icc a b → ℝ := fun t => ⟪z, gram i (v t)⟫_ℝ
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hli (n : ℕ) : LipschitzWith ⟨‖z‖ * K, mul_nonneg (norm_nonneg _) hK⟩ (F n) := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    change ‖⟪z, gram i (w n t)⟫_ℝ - ⟪z, gram i (w n s)⟫_ℝ‖ ≤ ‖z‖ * K * ‖(t:ℝ)-(s:ℝ)‖
    rw [← inner_sub_right]
    exact (norm_inner_le_norm _ _).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (hl n s s.property t t.property) (norm_nonneg z))
  have heq := (LipschitzWith.uniformEquicontinuous F _ hli).equicontinuous
  have ht : Tendsto F L (𝓝 V) := tendsto_pi_nhds.mpr (fun t => by
    simpa only [F, V, gram_symm] using hw t t.property (gram i z))
  have hu := (heq.tendsto_uniformFun_iff_pi L V).mpr ht
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

/-- Density of the Gram range upgrades uniform convergence of antidual
tests to uniform convergence for EVERY fixed form test vector. -/
theorem uniform_weak_pair (i : Q →L[ℝ] H) (hi : Function.Injective i)
    (a b : ℝ) (w : ℕ → ℝ → Q) (v : ℝ → Q) (L : Filter ℕ)
    (M K : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hb : ∀ n, ∀ t ∈ Icc a b, ‖w n t‖ ≤ M)
    (hv : ∀ t ∈ Icc a b, ‖v t‖ ≤ M)
    (hl : ∀ n, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ‖gram i (w n t) - gram i (w n s)‖ ≤ K * ‖t-s‖)
    (hw : ∀ t ∈ Icc a b, ∀ z : Q,
      Tendsto (fun n => ⟪z, w n t⟫_ℝ) L (𝓝 ⟪z, v t⟫_ℝ)) (z : Q) :
    TendstoUniformlyOn (fun n t => ⟪z, w n t⟫_ℝ) (fun t => ⟪z, v t⟫_ℝ) L (Icc a b) := by
  let U := Icc a b
  let F : ℕ → Q → (U →ᵤ ℝ) := fun n z => UniformFun.ofFun (fun t => ⟪z, w n t⟫_ℝ)
  let V : Q → (U →ᵤ ℝ) := fun z => UniformFun.ofFun (fun t => ⟪z, v t⟫_ℝ)
  have lip (u : U → Q) (hu : ∀ t, ‖u t‖ ≤ M) :
      LipschitzWith ⟨M, hM⟩ (fun z : Q => UniformFun.ofFun (fun t => ⟪z, u t⟫_ℝ)) := by
    apply UniformFun.lipschitzWith_ofFun_iff.mpr
    intro t
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro z y
    rw [← inner_sub_left]
    apply (norm_inner_le_norm _ _).trans
    change ‖z-y‖ * ‖u t‖ ≤ M * ‖z-y‖
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hu t) (norm_nonneg _)
  have hf (n : ℕ) : LipschitzWith ⟨M, hM⟩ (F n) := lip (fun t => w n t) (fun t => hb n t t.property)
  have hV : Continuous V := (lip (fun t => v t) (fun t => hv t t.property)).continuous
  have hF := (LipschitzWith.uniformEquicontinuous F _ hf).equicontinuous
  have hd (y : Q) (hy : y ∈ Set.range (gram i)) :
      Tendsto (fun n => F n y) L (𝓝 (V y)) := by
    obtain ⟨q, rfl⟩ := hy
    have ht := uniform_gram_pair i a b w v L K hK hl hw q
    simp_rw [← gram_symm] at ht
    exact UniformFun.tendsto_iff_tendstoUniformly.mpr
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp ht)
  have ht := (hF z).tendsto_of_mem_closure hV.continuousAt.continuousWithinAt hd (gram_dense i hi z)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp ht)

end QuantumNLS.Ext005WeakUniformR36b
#print axioms QuantumNLS.Ext005WeakUniformR36b.uniform_weak_pair

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakUniformR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakUniformR36b." then
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
