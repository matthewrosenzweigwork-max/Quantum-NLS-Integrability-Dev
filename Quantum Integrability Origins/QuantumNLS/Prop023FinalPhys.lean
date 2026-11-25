import QuantumNLS.Ext006PhysQuasifree
import QuantumNLS.Prop023FinalQF

/-! PROP-023 `Q7B:lem:moments` (fluctuations.tex:191) against the source's physical hypothesis.

The printed lemma takes a "normalized pure quasifree vacuum" `ξ`.  In the source (Lemma
`Q7B:lem:pair`, fluctuations.tex:95-111) this is `ξ = 𝕍(t,0) Ω`, where the unitary propagator
`𝕍(t,s)` of the quadratic Hamiltonian implements the symplectic isomorphism
`S(t,s) v = α v + β v̄`: the Heisenberg fields `𝕍* a_d 𝕍 = Σ_c α_{dc} a_c + β_{dc} a_c^*` (and the
adjoint relation) on the physical Fock space.  `Ext006PhysQuasifree.PhysicalQuasifreeSource x`
states exactly this with the repository's physical Fock space and creation/annihilation core, in
weak matrix-element form; `Ext006PhysQuasifree.physical_implies_pureQuasifree` proves it implies the
formal predicate (inverse pair `(α'†, -β'ᵀ)`, Bogoliubov relations from symplecticity of `S`,
transport to occupation coordinates), and `Prop023FinalQF.prop023`'s argument finishes.  (The
Hilbert-Schmidt property of `β` is part of the source's setting but is not used.) -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace QuantumNLS.Prop023FinalPhys
open Ext006NumberPhase Ext006PhysicalVacuum
variable {L : ℝ} [Fact (0 < L)]

/-- **PROP-023 `Q7B:lem:moments`**, hypothesis in the source's physical form. -/
theorem prop023 (x : Ext025B3PhysicalSectors.Fock L) (hx : ‖x‖ = 1)
    (hq : Ext006PhysQuasifree.PhysicalQuasifreeSource x) {Q : ℝ} (hQ : 1 ≤ Q)
    (hN : numberExpectation (fun n => (n : ℝ≥0∞)) x ≤ ENNReal.ofReal (Q - 1)) :
    exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1 / 4 : ℝ)) ∧
    ∀ j : ℕ, 1 ≤ j → ∃ hx' : x ∈ (polynomialRoot (L := L) j).domain,
      ‖polynomialRoot j ⟨x, hx'⟩‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ) / 2) :=
  Prop023FinalQF.prop023 x hx (Ext006PhysQuasifree.physical_implies_pureQuasifree hq) hQ hN

end QuantumNLS.Prop023FinalPhys
#print axioms QuantumNLS.Prop023FinalPhys.prop023
