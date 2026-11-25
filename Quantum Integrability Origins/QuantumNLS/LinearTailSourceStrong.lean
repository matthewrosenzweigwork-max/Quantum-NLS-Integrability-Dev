import QuantumNLS.LinearTailGenerator
import QuantumNLS.HaarKernelTailMain

/-! Source-route bridge from the accepted R-3B18A493 strong tail to the
literal finite-support kernels in the generator. The operator norm need not
tend to zero. No energy compactness or marginal estimate is postulated. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology Finset
open scoped BigOperators
namespace QuantumNLS.LinearTailSourceStrong
open TensorCarrier PhysicalTensor KernelDefinition BethePhysicalTransfer
open LinearTailGenerator GridStrongSum
variable (L : ℝ) [Fact (0 < L)]

/-- The existing strong grid sum, chosen only where the weights are contractions. -/
def gridT (n : ℕ) (t : ℤ → ℂ) : Hn L n →L[ℂ] Hn L n := by
  classical
  exact if h : ∀ m, ‖t m‖ ≤ 1 then (strong_exists L n t h).choose else 0

theorem gridT_strong (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (v : Hn L n) :
    Tendsto (fun M => partialSum L n t M v) atTop (𝓝 (gridT L n t v)) := by
  simp only [gridT, dite_eq_left ht]
  exact (strong_exists L n t ht).choose_spec.1 v

theorem gridT_norm (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) :
    ‖gridT L n t‖ ≤ Bd L (n + 1) := by
  simp only [gridT, dite_eq_left ht]
  exact (strong_exists L n t ht).choose_spec.2.1

/-- Encode exactly a finite real weight list; no exhaustion changes its support. -/
def weights (s : Finset ℤ) (t : ℤ → ℝ) (m : ℤ) : ℂ := if m ∈ s then (t m : ℂ) else 0

theorem weights_norm (s : Finset ℤ) (t : ℤ → ℝ) (ht : ∀ m ∈ s, |t m| ≤ 1) :
    ∀ m, ‖weights s t m‖ ≤ 1 := by
  intro m
  by_cases hm : m ∈ s
  · simpa only [weights, ite_eq_left hm, Complex.norm_real, Real.norm_eq_abs] using ht m hm
  · simp [weights, hm]

/-- Symmetric partial sums of a finite support eventually equal the literal
finiteT, so the accepted strong-tail theorem applies to the exact generator. -/
theorem finiteT_strong (n : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) (v : Hn L n) :
    Tendsto (fun M => partialSum L n (weights s t) M v) atTop
      (𝓝 (finiteT L (n + 1) s t v)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (s.sup Int.natAbs)] with M hM
  have hsub : s ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
    intro m hm
    have hle : m.natAbs ≤ M := (Finset.le_sup (f := Int.natAbs) hm).trans hM
    have hle' : (m.natAbs : ℤ) ≤ M := by exact_mod_cast hle
    have habs : |m| ≤ (M : ℤ) := by simpa only [Int.natCast_natAbs] using hle'
    exact Finset.mem_Icc.mpr (abs_le.mp habs)
  dsimp only [partialSum]
  have hs : (∑ m ∈ s, weights s t m • physicalKernel L (n + 1) (GridEigen.gridPt L m) v) =
      ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        weights s t m • physicalKernel L (n + 1) (GridEigen.gridPt L m) v := by
    apply Finset.sum_subset hsub
    intro m _ hm
    simp [weights, hm]
  rw [← hs]
  simp only [finiteT, _root_.sum_apply, _root_.smul_apply]
  apply Finset.sum_congr rfl
  intro m hm
  simp [weights, hm]

/-- Equality with the accepted strong sum at every vector, not merely a
bound or a new abstract family of kernels. -/
theorem finiteT_eq_gridT (n : ℕ) (s : Finset ℤ) (t : ℤ → ℝ)
    (ht : ∀ m ∈ s, |t m| ≤ 1) :
    finiteT L (n + 1) s t = gridT L n (weights s t) := by
  apply ContinuousLinearMap.ext
  intro v
  exact tendsto_nhds_unique (finiteT_strong L n s t v)
    (gridT_strong L n _ (weights_norm s t ht) v)

/-- Exact factorial majorant for the literal finite kernel. -/
theorem finiteT_norm (n : ℕ) (s : Finset ℤ) (t : ℤ → ℝ)
    (ht : ∀ m ∈ s, |t m| ≤ 1) :
    ‖finiteT L (n + 1) s t‖ ≤ Bd L (n + 1) := by
  rw [finiteT_eq_gridT L n s t ht]
  exact gridT_norm L n _ (weights_norm s t ht)

/-- R-3B18A493 gives uniform strong high-label convergence for the literal
finiteT over every compact vector set, uniformly over all finite supports. -/
theorem finiteT_compact_tail (n : ℕ) (C : Set (Hn L n)) (hC : IsCompact C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ (s : Finset ℤ) (t : ℤ → ℝ),
      (∀ m ∈ s, |t m| ≤ 1) → (∀ m ∈ s, (R : ℤ) < |m|) →
      ∀ f ∈ C, ‖finiteT L (n + 1) s t f‖ ≤ ε := by
  obtain ⟨R₀, hR₀⟩ := HaarKernelTailMain.haar_kernel_tail_compact L n (gridT L n)
    (fun t ht v => gridT_strong L n t ht v) C hC ε hε
  refine ⟨R₀, fun R hR s t ht hs f hf => ?_⟩
  rw [finiteT_eq_gridT L n s t ht]
  apply hR₀ R hR (weights s t) (weights_norm s t ht) _ f hf
  intro m hm
  have hms : m ∉ s := fun h => (not_lt_of_ge hm) (hs m h)
  simp [weights, hms]

end QuantumNLS.LinearTailSourceStrong

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.LinearTailSourceStrong.gridT
#print axioms QuantumNLS.LinearTailSourceStrong.gridT_strong
#print axioms QuantumNLS.LinearTailSourceStrong.gridT_norm
#print axioms QuantumNLS.LinearTailSourceStrong.weights
#print axioms QuantumNLS.LinearTailSourceStrong.weights_norm
#print axioms QuantumNLS.LinearTailSourceStrong.finiteT_strong
#print axioms QuantumNLS.LinearTailSourceStrong.finiteT_eq_gridT
#print axioms QuantumNLS.LinearTailSourceStrong.finiteT_norm
#print axioms QuantumNLS.LinearTailSourceStrong.finiteT_compact_tail

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.LinearTailSourceStrong." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
