import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Strong differentiation of a unitary acting on a moving Fock vector.
Only continuity and differentiation on individual vectors enter. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace QuantumNLS.Prop021StrongProductR131

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strong limits of isometries act jointly continuously on a convergent vector. -/
theorem tendsto_apply {ι : Type*} {l : Filter ι} {U : ι → E →ₗᵢ[ℝ] E}
    {U₀ : E →ₗᵢ[ℝ] E} (hU : ∀ x, Tendsto (fun t => U t x) l (𝓝 (U₀ x)))
    {v : ι → E} {v₀ : E} (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun t => U t (v t)) l (𝓝 (U₀ v₀)) := by
  have hv' : Tendsto (fun t => v t - v₀) l (𝓝 0) := by
    simpa only [sub_self] using hv.sub (tendsto_const_nhds (x := v₀))
  have hd : Tendsto (fun t => U t (v t) - U t v₀) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [← map_sub, LinearIsometry.norm_map] using
      (tendsto_zero_iff_norm_tendsto_zero.mp hv')
  simpa only [sub_add_cancel, zero_add] using hd.add (hU v₀)

/-- The strong product rule for the actual moving vector. The time derivative
of the operator is only taken at the fixed vector at the reference time. -/
theorem hasDerivAt_apply {U : ℝ → E →ₗᵢ[ℝ] E} {v : ℝ → E} {t : ℝ} {dv dU : E}
    (hU : ∀ x, ContinuousAt (fun r => U r x) t)
    (hdU : HasDerivAt (fun r => U r (v t)) dU t)
    (hv : HasDerivAt v dv t) :
    HasDerivAt (fun r => U r (v r)) (U t dv + dU) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h1 := tendsto_apply (fun x => (hU x).tendsto.mono_left nhdsWithin_le_nhds)
    hv.tendsto_slope
  have h2 := h1.add hdU.tendsto_slope
  convert h2 using 1
  funext r
  simp only [slope_def_module, map_smul, map_sub, ← smul_add]
  congr 1
  abel

end QuantumNLS.Prop021StrongProductR131

#print axioms QuantumNLS.Prop021StrongProductR131.hasDerivAt_apply

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021StrongProductR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
