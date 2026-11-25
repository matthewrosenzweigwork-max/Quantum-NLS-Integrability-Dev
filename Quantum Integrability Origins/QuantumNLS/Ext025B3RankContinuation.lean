import QuantumNLS.Ext025B2Projections
import Mathlib.Topology.Connected.Clopen

/-! GP-17 corrected finite-rank continuation. One finite-dimensional range
at a base point is the explicit additional hypothesis. It cannot be deduced
from isolation of finitely many spectral values: the frozen identity-resolvent
counterexample already proves that failure. This module does not assert the
remaining argument-principle or general Riesz projection construction.
Author sol_ext_b, Round 3. -/
noncomputable section
set_option autoImplicit false
open Filter Topology Set
namespace QuantumNLS.Ext025B3RankContinuation
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace X]

/-- The property of having a specified finite rank is invariant under a
norm perturbation smaller than one between idempotents. -/
theorem finite_rank_iff (P Q : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) (hQ : ∀ v, Q (Q v) = Q v)
    (hPQ : ‖P-Q‖ < 1) (k : ℕ) :
    (FiniteDimensional ℂ (LinearMap.range P.toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range P.toLinearMap) = k) ↔
    (FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range Q.toLinearMap) = k) := by
  constructor
  · rintro ⟨hfin, hrank⟩
    let := hfin
    obtain ⟨hq, he⟩ := Ext025B2Projections.«FIN-EXT025-GP-17-rank-stability» P Q hP hQ hPQ
    exact ⟨hq, he.trans hrank⟩
  · rintro ⟨hfin, hrank⟩
    let := hfin
    obtain ⟨hp, he⟩ := Ext025B2Projections.«FIN-EXT025-GP-17-rank-stability» Q P hQ hP
      (by simpa only [norm_sub_rev] using hPQ)
    exact ⟨hp, he.trans hrank⟩

/-- Each finite-rank stratum of a continuous idempotent family is clopen. -/
theorem finite_rank_isClopen (P : X → E →L[ℂ] E) (hc : Continuous P)
    (hid : ∀ x v, P x (P x v) = P x v) (k : ℕ) :
    IsClopen {x | FiniteDimensional ℂ (LinearMap.range (P x).toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range (P x).toLinearMap) = k} := by
  let S := {x | FiniteDimensional ℂ (LinearMap.range (P x).toLinearMap) ∧
    Module.finrank ℂ (LinearMap.range (P x).toLinearMap) = k}
  have hnear (x : X) : ∀ᶠ y in 𝓝 x, (y ∈ S ↔ x ∈ S) := by
    have hn : ∀ᶠ y in 𝓝 x, ‖P y - P x‖ < 1 := by
      have ht : Tendsto (fun y => ‖P y - P x‖) (𝓝 x) (𝓝 0) := by
        simpa only [sub_self, norm_zero] using
          ((hc.continuousAt (x := x)).sub_const (P x)).norm
      exact ht.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [hn] with y hy
    exact finite_rank_iff (P y) (P x) (hid y) (hid x) hy k
  have ho : IsOpen S := isOpen_iff_mem_nhds.mpr (fun x hx =>
    (hnear x).mono (fun _ hy => hy.mpr hx))
  have hco : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr (fun x hx =>
    (hnear x).mono (fun _ hy => mt hy.mp hx))
  exact ⟨isOpen_compl_iff.mp hco, ho⟩

/-- Finite rank at ONE point propagates along any connected parameter space,
including every compact continuous path. No finite multiplicity is assumed
at any other point. -/
theorem «FIN-EXT025-GP-17-corrected-rank-continuation» [PreconnectedSpace X]
    (P : X → E →L[ℂ] E) (hc : Continuous P) (hid : ∀ x v, P x (P x v) = P x v)
    (x₀ : X) [FiniteDimensional ℂ (LinearMap.range (P x₀).toLinearMap)] (x : X) :
    FiniteDimensional ℂ (LinearMap.range (P x).toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range (P x).toLinearMap) =
        Module.finrank ℂ (LinearMap.range (P x₀).toLinearMap) := by
  have he := (finite_rank_isClopen P hc hid
    (Module.finrank ℂ (LinearMap.range (P x₀).toLinearMap))).eq_univ
      ⟨x₀, inferInstance, rfl⟩
  exact (Set.eq_univ_iff_forall.mp he) x

end QuantumNLS.Ext025B3RankContinuation

#print axioms QuantumNLS.Ext025B3RankContinuation.finite_rank_iff

#print axioms QuantumNLS.Ext025B3RankContinuation.finite_rank_isClopen

#print axioms QuantumNLS.Ext025B3RankContinuation.«FIN-EXT025-GP-17-corrected-rank-continuation»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B3RankContinuation." then
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
  Lean.logInfo m!"Ext025B3RankContinuation audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
