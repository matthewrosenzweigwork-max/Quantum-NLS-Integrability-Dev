import QuantumNLS.Ext005ComplexGramR34b
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Moving-vector quadratic chain rule using only norm continuity of the
coefficient and scalar diagonal derivatives, exactly as in SourceOn. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005QuadraticChainR34b
variable {Q : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

lemma quadratic_difference (L : Q →L[ℝ] Q) (hL : L.IsSymmetric) (u v : Q) :
    ⟪u, L u⟫_ℝ - ⟪v, L v⟫_ℝ = ⟪u - v, L (u + v)⟫_ℝ := by
  have h : ⟪u, L v⟫_ℝ = ⟪v, L u⟫_ℝ := by
    exact (hL u v).symm.trans (real_inner_comm v (L u))
  simp only [map_add, inner_sub_left, inner_add_right]
  linarith

/-- Norm differentiability of L is not required. Only its fixed-vector
quadratic form derivative and norm continuity at this time enter. -/
theorem quadratic_chain (L : ℝ → Q →L[ℝ] Q) (u : ℝ → Q)
    (S : Set ℝ) (t : ℝ) (u' : Q) (d : ℝ)
    (hL : ContinuousWithinAt L S t)
    (hsym : ∀ r ∈ S, (L r).IsSymmetric)
    (hu : HasDerivWithinAt u u' S t)
    (hd : HasDerivWithinAt (fun r => ⟪u t, L r (u t)⟫_ℝ) d S t) :
    HasDerivWithinAt (fun r => ⟪u r, L r (u r)⟫_ℝ)
      (d + 2 * ⟪u', L t (u t)⟫_ℝ) S t := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hu hd ⊢
  have huc : Tendsto u (𝓝[S \ {t}] t) (𝓝 (u t)) :=
    (hasDerivWithinAt_iff_tendsto_slope.mpr hu).continuousWithinAt.mono sdiff_subset
  have hLc : Tendsto L (𝓝[S \ {t}] t) (𝓝 (L t)) := hL.mono sdiff_subset
  have ha : Tendsto (fun r => L r (u r + u t)) (𝓝[S \ {t}] t)
      (𝓝 (L t (u t + u t))) :=
    isBoundedBilinearMap_apply.continuous.tendsto (L t, u t + u t) |>.comp
      (hLc.prodMk_nhds (huc.add tendsto_const_nhds))
  have h := (hu.inner ha).add hd
  have he : (fun r => ⟪slope u t r, L r (u r + u t)⟫_ℝ +
      slope (fun r => ⟪u t, L r (u t)⟫_ℝ) t r) =ᶠ[𝓝[S \ {t}] t]
      slope (fun r => ⟪u r, L r (u r)⟫_ℝ) t := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [slope_def_module, slope_def_module, slope_def_module, real_inner_smul_left,
      ← quadratic_difference _ (hsym r hr.1)]
    simp only [smul_eq_mul]
    ring
  have hlim : ⟪u', L t (u t + u t)⟫_ℝ + d = d + 2 * ⟪u', L t (u t)⟫_ℝ := by
    simp only [map_add, inner_add_right]
    ring
  rw [← hlim]
  exact h.congr' he

end QuantumNLS.Ext005QuadraticChainR34b
#print axioms QuantumNLS.Ext005QuadraticChainR34b.quadratic_chain

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005QuadraticChainR34b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005QuadraticChainR34b." then
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
  Lean.logInfo m!"R34b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
