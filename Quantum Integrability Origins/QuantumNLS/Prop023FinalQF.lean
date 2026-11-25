import QuantumNLS.Ext006QuasifreeWeak
import QuantumNLS.Prop023Number

/-! PROP-023 `Q7B:lem:moments` (fluctuations.tex:191) against the printed hypothesis.

The source never defines "pure quasifree" separately: Lemma `Q7B:lem:pair` (fluctuations.tex:95-111)
produces `ξ_t = V(t,0)Ω` with `V(t,s)` a unitary implementing the symplectic isomorphism
`S(t,s) v = α v + β v̄` (β Hilbert-Schmidt) and calls it "pure quasifree"; the proof of
Q7B:lem:moments then writes such a `ξ` through the squeezed-vacuum formula of [BD, Thm 4.2].
`Ext006QuasifreeWeak.PureQuasifree ξ` is exactly this: `ξ = V Ω`, `V` a unitary of the free
occupation Fock space implementing a Bogoliubov map `(α, β)` with the Bogoliubov relations
(`Ext006BogoliubovAlg.IsBogoliubov`), the implementation being stated in the weak matrix-element
form of `V a_d V^* = ∑_c α_{dc} a_c + β_{dc} a_c^*` (so no operator domains are assumed).
`Ext006QuasifreeWeak.quasifree_weak` proves from it the weak annihilation equation with the
symmetric kernel `K = α^{-1} β`, and `Prop023Number` finishes.  (The Hilbert-Schmidt property of `β`
is a hypothesis of the source's setting that this proof does not use; the theorem is stated
without it, hence for a larger class.) -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace QuantumNLS.Prop023FinalQF
open Ext006NumberPhase Ext006PhysicalVacuum
variable {L : ℝ} [Fact (0 < L)]

/-- A physical vector is a pure quasifree vacuum when its free-occupation coefficient function is
`V Ω` for a unitary `V` implementing a Bogoliubov map. -/
def PhysicalPureQuasifree (x : Ext025B3PhysicalSectors.Fock L) : Prop :=
  Ext006QuasifreeWeak.PureQuasifree (coefficient x)

/-- **PROP-023 `Q7B:lem:moments`** against the printed hypothesis: a normalized pure quasifree
vacuum `ξ` (`ξ = VΩ`, `V` implementing a Bogoliubov map) with `⟨ξ, Nξ⟩ ≤ Q - 1`, `Q ≥ 1`, satisfies
`⟨ξ, e^{N/(16Q)} ξ⟩ ≤ e^{1/4}` and `‖(N + j)^{j/2} ξ‖ ≤ (32 Q j)^{j/2}` for every `j ≥ 1`. -/
theorem prop023 (x : Ext025B3PhysicalSectors.Fock L) (hx : ‖x‖ = 1)
    (hq : PhysicalPureQuasifree x) {Q : ℝ} (hQ : 1 ≤ Q)
    (hN : numberExpectation (fun n => (n : ℝ≥0∞)) x ≤ ENNReal.ofReal (Q - 1)) :
    exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1 / 4 : ℝ)) ∧
    ∀ j : ℕ, 1 ≤ j → ∃ hx' : x ∈ (polynomialRoot (L := L) j).domain,
      ‖polynomialRoot j ⟨x, hx'⟩‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ) / 2) := by
  obtain ⟨K, hK, hv⟩ := Ext006QuasifreeWeak.quasifree_weak hq
  exact Prop023Number.prop023_weak_moments hK x hx hv hQ hN

end QuantumNLS.Prop023FinalQF
#print axioms QuantumNLS.Prop023FinalQF.prop023
