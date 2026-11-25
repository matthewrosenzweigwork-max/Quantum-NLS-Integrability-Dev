import QuantumNLS.BetheLabels

/-! integrator-authored trusted spec for DEF-006 (definitions.tex:37-41). Logarithmic labels: strictly
increasing I_j ∈ ℤ + (N−1)/2. Rapidities solve L q_j + 2 Σ_{k≠j} arctan((q_j−q_k)/c) = 2π I_j (for
c > 0 the solution exists and is unique, and is the accepted R-4C8D7C9E root vector after index
reversal). Corrected integers n_j = I_j − j + (N+1)/2 (one-based j) are integers and nondecreasing.
Their multiplicities form a finitely supported array of nonnegative integers with sum N; M_N is the set
of all such arrays, in bijection with the labels. -/

open QuantumNLS.BetheLabels QuantumNLS.BetheSmooth QuantumNLS.BetheConvexity

namespace QuantumNLS.DEF006Spec

def Spec : Prop :=
  ∀ (N : ℕ),
    -- corrected integers: literal formula, integer-valued, nondecreasing
    (∀ (ℓ : LogLabels N) (j : Fin N), (correctedInt ℓ j : ℝ) =
        ℓ.I j - ((j.val : ℝ) + 1) + ((N : ℝ) + 1) / 2) ∧
    (∀ ℓ : LogLabels N, Monotone (correctedInt ℓ)) ∧
    -- multiplicity arrays: m_n = #{j : n_j = n}, sum N; labels ≃ M_N
    (∀ (ℓ : LogLabels N) (k : ℤ), (labelsEquivArr ℓ).1 k =
        (Finset.univ.filter fun j => correctedInt ℓ j = k).card) ∧
    (∀ m : MArr N, (m.1.sum fun _ k => k) = N) ∧
    Function.Bijective (labelsEquivArr (N := N)) ∧
    -- rapidity equation: unique real solution for c > 0, equal to the accepted source roots reversed
    (∀ (L c : ℝ), 0 < L → 0 < c → ∀ ℓ : LogLabels N,
      (∃! q : Fin N → ℝ, ∀ j : Fin N, L * q j + 2 * ∑ k ∈ Finset.univ.erase j,
          Real.arctan ((q j - q k) / c) = 2 * Real.pi * ℓ.I j) ∧
      ∀ q : Fin N → ℝ, (∀ j : Fin N, L * q j + 2 * ∑ k ∈ Finset.univ.erase j,
          Real.arctan ((q j - q k) / c) = 2 * Real.pi * ℓ.I j) →
        ∀ i, q i = sourceRoots L (srcOf (correctedInt ℓ)) c (Fin.rev i))

theorem spec : Spec := by
  intro N
  obtain ⟨h1, h2, h3, -, -, -, h7⟩ := def006 N
  refine ⟨h1, h2, h3, fun m => m.2, h7, fun L c hL hc ℓ => ?_⟩
  obtain ⟨hu, hiff, -, hrev, -⟩ := bethe_labels_roots hL hc ℓ
  refine ⟨hu, fun q hq i => ?_⟩
  have hq' := (hiff q).1 hq
  rw [hrev (Fin.rev i), Fin.rev_rev, hq']

end QuantumNLS.DEF006Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF006Spec.spec
  IO.println s!"DEF006Spec.spec axioms: {ax}"
