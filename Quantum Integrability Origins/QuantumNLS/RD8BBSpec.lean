import QuantumNLS.FiniteCellFinal
/-! integrator-authored trusted spec for R-D8BB052C QG:prop:finite-cell-gauge (QUANTUM_GAUGE_COMPONENTS.tex:969–983), the
abstract printed proposition (Terra r127: no physical binding needed; a physical Bethe-basis instantiation is a separate
downstream application). For finite I ⊆ ℤ with r = |I| ≥ 2, 2 ≤ ℓ ≤ N and selected seeds: a unit scalar Q = q_N on every
complete array, fixed before any vector/target, with bounded W_ab, W_ab* = W_ba, support projections, telescoping/path
identities; and for every unit g, target w, δ, η ≥ 0 (explicit nonnegative tolerances — the source's convention, recorded),
action errors ≤ δ and summed residuals ≤ η², every tested pair with a_a, a_b ≥ 4/ℓ satisfies
‖(W_ab − ζ_ab)g‖, ‖(W_ab* − conj ζ_ab)g‖ ≤ 2√r ℓ^{r/2} η + √((16r+9)ℓ²δ² + 8/ℓ + (4ℓ+2)√(2η)). -/
namespace RD8BBSpec
open scoped Classical ComplexConjugate
open QuantumNLS QuantumNLS.FiniteCellFinal Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport
  FiniteCellPartition FiniteCellPaths FiniteCellGauge FiniteCellTransport FiniteCellEstimate FiniteCellInternal
  FiniteCellCoefficientLaw FiniteCellTotalVariation FiniteCellEvents FiniteCellResidues FiniteCellOmissions

theorem defs :
    (∀ (I : Finset ℤ) (ell : ℕ) (delta eta : ℝ), printedBound I ell delta eta =
      2 * Real.sqrt (I.card : ℝ) * (ell : ℝ) ^ ((I.card : ℝ) / 2) * eta +
        Real.sqrt ((16 * (I.card : ℝ) + 9) * (ell : ℝ) ^ 2 * delta ^ 2 + 8 / (ell : ℝ) +
          (4 * (ell : ℝ) + 2) * Real.sqrt (2 * eta))) ∧
    (∀ z w : ℂ, symbol z w = z * conj w / (‖z * w‖ : ℂ)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem spec {N : ℕ} (I : Finset ℤ) (ell : ℕ) (hI : 2 ≤ I.card) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : SelectedSeeds I N) :
    ∃ Q : Arr N → Phase, Q = q_N I ell c ∧
      (∀ m, ‖(Q m).1‖ = 1) ∧
      (∀ m, Q (root I (threshold N ell) ell m).1 = phaseOne) ∧
      (∀ a b, ‖W Q a b‖ ≤ 1) ∧
      (∀ a b, a ≠ b → (W Q a b).adjoint = W Q b a) ∧
      (∀ a b, (W Q a b).adjoint ∘L W Q a b = support a) ∧
      (∀ a b, a ≠ b → W Q a b ∘L (W Q a b).adjoint = support b) ∧
      (∀ m n p, (ratio Q m n).1 * (ratio Q n p).1 = (ratio Q m p).1) ∧
      (∀ m vertices, pathProduct Q m (vertices ++ [m]) = 1) ∧
      (∀ (g : H N) (w : ↥I → ℂ) (delta eta : ℝ)
        (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) (hg : ‖g‖ = 1),
        (∀ j : ↥I, ‖E N j.1 j.1 g - ((‖w j‖ ^ 2 : ℝ) : ℂ) • g‖ ≤ delta) →
        (∑ a : ↥(good I ell w), ∑ b : ↥((good I ell w).erase a.1),
          ‖seedTransfer (extendSeeds I c) a.1 b.1 (Finset.mem_erase.mp b.2).1.symm g -
            ((phases I w a.1).1 * conj (phases I w b.1).1) • g‖ ^ 2) ≤ eta ^ 2 →
        ∀ (a b : ↥I), a.1 ≠ b.1 → 4 / (ell : ℝ) ≤ ‖w a‖ ^ 2 → 4 / (ell : ℝ) ≤ ‖w b‖ ^ 2 →
          ‖W Q a.1 b.1 g - symbol (w a) (w b) • g‖ ≤ printedBound I ell delta eta ∧
          ‖(W Q a.1 b.1).adjoint g - conj (symbol (w a) (w b)) • g‖ ≤ printedBound I ell delta eta)  :=
  scalar_finite_cell_gauge I ell hI hell hN c

end RD8BBSpec
#print axioms RD8BBSpec.defs
#print axioms RD8BBSpec.spec
