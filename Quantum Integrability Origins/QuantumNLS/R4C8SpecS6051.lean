import QuantumNLS.BetheConvexity
/-!
Trusted statement for R-4C8D7C9E `basis:lem:roots`, written by the integrator (not the prover) from
`source/chapters/foundations/periodic_basis.tex:22–31, 133–140`:
  𝔑_N = {n ∈ ℤ^N : n₁ ≥ ⋯ ≥ n_N},  ρ_j = (N+1−2j)/2,  I_j = n_j + ρ_j,
  (logbethe)  L q_j + 2 Σ_{k≠j} arctan((q_j − q_k)/c) = 2π I_j,   1 ≤ j ≤ N.
Claim: for every n ∈ 𝔑_N and c > 0 the system has a unique real solution q(n,c); its components are strictly decreasing;
c ↦ q(n,c) is smooth on c > 0; and |q(n,c)| ≤ 2π|I|/L (Euclidean norms). Indices are zero-based (j ↦ j+1).
L > 0 is the standing torus length.
-/
open Set
open scoped ContDiff

noncomputable def specI {N : ℕ} (n : Fin N → ℤ) (j : Fin N) : ℝ :=
  (n j : ℝ) + ((N : ℝ) + 1 - 2 * ((j : ℕ) + 1 : ℝ)) / 2

def specBethe {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop :=
  ∀ j : Fin N, L * q j + 2 * ∑ k ∈ Finset.univ.erase j, Real.arctan ((q j - q k) / c) = 2 * Real.pi * specI n j

def R4C8Spec : Prop :=
  ∀ (N : ℕ) (L : ℝ), 0 < L → ∀ n : Fin N → ℤ, Antitone n →
    ∃ Q : ℝ → (Fin N → ℝ), ContDiffOn ℝ ∞ Q (Ioi 0) ∧
      ∀ c : ℝ, 0 < c →
        specBethe L c n (Q c) ∧ (∀ q, specBethe L c n q → q = Q c) ∧ StrictAnti (Q c) ∧
        Real.sqrt (∑ j, (Q c j) ^ 2) ≤ 2 * Real.pi * Real.sqrt (∑ j, (specI n j) ^ 2) / L

theorem r4c8_spec_convex : R4C8Spec := by
  intro N L hL n hn
  obtain ⟨Q, hs, hc⟩ := QuantumNLS.BetheConvexity.source_roots_printed hL hn
  have hi : ∀ j : Fin N, specI n j = (n j : ℝ) + ((N : ℝ) - 1) / 2 - (j.val : ℝ) := by
    intro j; unfold specI; push_cast; ring
  refine ⟨Q, hs, fun c hc0 => ?_⟩
  obtain ⟨he, ho, hb, hu⟩ := hc c hc0
  refine ⟨?_, ?_, ho, ?_⟩
  · intro j; simpa only [specBethe, hi] using he j
  · intro q hq; exact hu q (fun j => by simpa only [hi] using hq j)
  · simpa only [hi] using hb

#print axioms r4c8_spec_convex

set_option maxHeartbeats 2000000 in
run_cmd do
  let env ← Lean.getEnv
  let forbidden : Array Lean.Name := #[``QuantumNLS.BetheAdmission.logMap_injective,
    ``QuantumNLS.BetheSmooth.eq_root, ``QuantumNLS.BetheSmooth.root_contDiffAt,
    ``QuantumNLS.BetheSmooth.root_contDiffOn, ``QuantumNLS.BetheSmooth.source_roots_spec,
    ``QuantumNLS.BetheRoots.roots_existsUnique, ``QuantumNLS.BetheRoots.sorted_roots_existsUnique]
  let mut pending := #[``r4c8_spec_convex]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if forbidden.contains n then throwError "forbidden proof dependency: {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then pending := pending ++ v.getUsedConstants
  unless seen.contains ``QuantumNLS.BetheConvexity.yangYang_strictConvex do
    throwError "strict convexity not reached"
  Lean.logInfo m!"coordinator dependency audit passed: {seen.size} constants; old uniqueness routes excluded; strict convexity reached"
