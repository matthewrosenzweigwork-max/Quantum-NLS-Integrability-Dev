import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! C06: common-domain strong-limit lemma and the exact obstruction once
sector commutation has been established. The reducing-subspace theorem for
unbounded Borel spectral functions is NOT supplied by these algebraic lemmas;
that part of the full C06 contract remains OPEN. No closure premise for that
spectral calculus is assumed here. -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace QuantumNLS.Ext025BSectors
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Bounded projections pass through a vectorwise limit on the common
invariant domain. No bound or continuity on the possibly unbounded T is used. -/
theorem «FIN-EXT025-C06-strong-limit» (D : Submodule ℂ H) (P : H →L[ℂ] H)
    (hD : ∀ x : D, P x ∈ D) (Tj : ℕ → D → H) (T : D → H)
    (hj : ∀ j (x : D), Tj j ⟨P x, hD x⟩ = P (Tj j x))
    (hlim : ∀ x, Tendsto (fun j => Tj j x) atTop (𝓝 (T x))) (x : D) :
    T ⟨P x, hD x⟩ = P (T x) := by
  apply tendsto_nhds_unique (hlim ⟨P x, hD x⟩)
  simpa only [hj, Function.comp_def] using (P.continuous.tendsto (T x)).comp (hlim x)

/-- Exact number obstruction on the whole invariant domain, not only on
individual homogeneous inputs. P is a separating orthogonal sector family.
The vacuum part of number lowering is explicitly zero. -/
theorem «FIN-EXT025-C06-obstruction» (D : Submodule ℂ H)
    (P : ℕ → H →L[ℂ] H) (hD : ∀ n (x : D), P n x ∈ D)
    (hid : ∀ n (x : H), P n (P n x) = P n x)
    (horth : ∀ n (x : H), P (n+1) (P n x) = 0)
    (hsep : ∀ x : H, (∀ n, P n x = 0) → x = 0)
    (T : D →ₗ[ℂ] H)
    (hpres : ∀ n (x : D), T ⟨P n x, hD n x⟩ = P n (T x))
    (hv : ∀ x : D, T ⟨P 0 x, hD 0 x⟩ = 0)
    (hlow : ∀ n (x : D), P n (T ⟨P (n+1) x, hD (n+1) x⟩) =
      T ⟨P (n+1) x, hD (n+1) x⟩) : ∀ x, T x = 0 := by
  intro x
  apply hsep
  intro n
  cases n with
  | zero => rw [← hpres]; exact hv x
  | succ n =>
    have h1 := hpres (n+1) x
    have h2 := hlow n x
    rw [h1] at h2
    have h3 := congrArg (P (n+1)) h2
    rw [horth] at h3
    rw [hid] at h3
    exact h3.symm

end QuantumNLS.Ext025BSectors

#print axioms QuantumNLS.Ext025BSectors.«FIN-EXT025-C06-strong-limit»
#print axioms QuantumNLS.Ext025BSectors.«FIN-EXT025-C06-obstruction»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025BSectors." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025BSectors audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
