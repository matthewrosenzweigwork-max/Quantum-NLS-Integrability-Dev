import QuantumNLS.FiniteDiagonalPhase

/-! integrator-authored trusted spec for R-BE514996 `intr:finite:thm:finite-diagonal-phase`
(intrinsic/finite.tex:18-115). QUALIFIED: the printed objects I_j, the log-Bethe system, A_σ, B and Z
are pinned here by their printed formulas (clause 0); the continuous symmetric periodic extension and
the normalized vector use the author's `finiteExt`/`psiUnit` (Terra R69 reviewed them as faithful).
Printed N = Lean N+1; zero-based indices. Analyticity is pointwise in the identified torus coordinate
(Terra R69 reading). -/

open MeasureTheory
open QuantumNLS.FiniteDiagonalPhase QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy

namespace QuantumNLS.RBE51Spec

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ) [Fact (0 < L)] (hc : 0 < c), ∀ n : Fin (N+1) → ℤ, Monotone n →
    -- clause 0: printed objects pinned
    (∀ j, printedLabel n j = (n j : ℝ) + ((j.val : ℝ) + 1) - (((N+1 : ℕ) : ℝ) + 1) / 2) ∧
    (∀ I q : Fin (N+1) → ℝ, LogBethe L c I q ↔ ∀ j, L * q j + 2 * ∑ k ∈ Finset.univ.erase j,
        Real.arctan ((q j - q k) / c) = 2 * Real.pi * I j) ∧
    (∀ (q : Fin (N+1) → ℝ) σ, finiteA c q σ = ∏ j : Fin (N+1), ∏ k ∈ Finset.univ.filter (fun k => j < k),
        (1 - Complex.I * (c : ℂ) / ((q (σ j) - q (σ k) : ℝ) : ℂ))) ∧
    (∀ (q x : Fin (N+1) → ℝ), finiteB c q x = ∑ σ : Equiv.Perm (Fin (N+1)), finiteA c q σ *
        Complex.exp (Complex.I * ((∑ j, q (σ j) * x j : ℝ) : ℂ))) ∧
    (∀ q : Fin (N+1) → ℝ, finiteZ L c q =
        ((N+1).factorial : ℝ) * ∫ x in BetheWavefunctions.chamber (N+1) L, ‖finiteB c q x‖ ^ 2) ∧
    -- main clauses
    (∃! q : Fin (N+1) → ℝ, LogBethe L c (printedLabel n) q) ∧
    (∀ q, LogBethe L c (printedLabel n) q → StrictMono q ∧ 0 < finiteZ L c q ∧
      ∃ Ψ : ContactOperator.SymL2 L (N+1),
        ((Ψ : ContactOperator.SymL2 L (N+1)) : L2TN L (N+1)) =ᵐ[torusPiMeasure L (N+1)]
          (fun x => ((Real.sqrt (finiteZ L c q))⁻¹ : ℂ) * finiteExt L c n x) ∧
        ‖Ψ‖ = 1 ∧
        (∃ h : Ψ ∈ (ContactOperator.Hop c hc.le).domain,
          ContactOperator.Hop c hc.le ⟨Ψ, h⟩ = ((∑ j, q j ^ 2 : ℝ) : ℂ) • Ψ) ∧
        (∀ x ∈ BetheWavefunctions.chamber (N+1) L,
          finiteExt L c n (fun i => (x i : AddCircle L)) = finiteB c q x) ∧
        finiteExt L c n 0 = ((N+1).factorial : ℂ)) ∧
    -- analytic dependence on (L, c)
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => BetheSmooth.roots p.1 n p.2) {p | 0 < p.1 ∧ 0 < p.2} ∧
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => finiteZ p.1 p.2 (BetheSmooth.roots p.1 n p.2))
      {p | 0 < p.1 ∧ 0 < p.2} ∧
    (∀ y : Fin (N+1) → ℝ,
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => psiUnit n p.1 p.2 y) {p | 0 < p.1 ∧ 0 < p.2})

theorem spec : Spec := by
  intro N L c _ hc n hn
  obtain ⟨hex, hmono, hrest, -⟩ := finite_diagonal_phase (N := N) (L := L) hc hn
  obtain ⟨ha1, ha2, -, -, ha5⟩ := finite_phase_analytic (M := N+1) hn
  refine ⟨fun j => by simp [printedLabel], fun I q => Iff.rfl, fun q σ => rfl, fun q x => rfl,
    fun q => rfl, hex, fun q hq => ?_, ha1, ha2, ha5⟩
  obtain ⟨-, ⟨-, -, hcham, -⟩, ⟨-, hZ⟩, ⟨Ψ, hae, hnorm, heig, -, -⟩, ⟨-, h0, -, -⟩⟩ := hrest q hq
  exact ⟨hmono q hq, hZ, Ψ, hae, hnorm, heig, hcham, h0⟩

end QuantumNLS.RBE51Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RBE51Spec.spec
  IO.println s!"RBE51Spec.spec axioms: {ax}"
