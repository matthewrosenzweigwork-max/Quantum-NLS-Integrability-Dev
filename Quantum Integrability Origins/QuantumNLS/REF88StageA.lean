import Mathlib
import QuantumNLS.REF88Chart
import QuantumNLS.REF88Reg015Input
import QuantumNLS.REF88Finite

/-!
# REF88StageA: INTERMEDIATE theorem of R-EF8C2837 (`thm:global-physical-dynamics`)

Source: `source-text/chapters/global/physical_cubic.tex:28-89` (statement; the parts proved here are
the rotation formula `eq:global-NLS-rotations` with the continuity of `ν_n` and the zero-coordinate
clause, the Sobolev homeomorphisms for every `s ≥ 0`, and the strongly continuous group on each
fixed-action torus).

Hypotheses of this INTERMEDIATE theorem (and nothing else):
* the printed chart hypotheses: `Φ` strongly symplectic (DEF-016, a diffeomorphism), exact moduli
  `|Φ(u)_n|² = I_n^{(κ)}(u)`; plus the continuity of `Φ` and of `Φ⁻¹` (part of "diffeomorphism";
  carried as explicit hypotheses `hcΦ`, `hcΨ` because of an instance-synthesis obstruction for the
  `complexToReal` structure of DEF-016, to be discharged from the analyticity/continuity conclusions of
  the accepted R-CA92819A);
* `hR : Reg015Input L κ hκ`: the EXACT printed REG-015 statement (named input; to be replaced by the
  accepted REG-015 theorem in the FINAL theorem);
* `hFR : FieldRotation hΦ κ`: the finite-action Hamiltonian-calculation output (printed paragraphs
  "Bounded contour energies near arbitrary mass" and the first half of "Physical rotations on finite
  action supports").  NOT proved in the REF88 modules built so far; it is the principal remaining
  obligation, NOT REG-015.

NOT covered (remaining): the quantum frequency formula `eq:global-absolute-frequency`, the `H¹` gap
identification and the identification of the frequency with the continuous limit of the finite-action
formulas for general `L²` input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open Filter

namespace QuantumNLS.REF88StageA

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.Fourier
open QuantumNLS.PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **INTERMEDIATE THEOREM (stage A).**  See the module header for the exact hypotheses.  Conclusions:
the rotation formula with the real frequencies `ν_n`, the zero-coordinate statement, uniqueness and
continuity of `ν_n` on `{a ∈ ℓ¹_+ : a_n > 0}`, the strongly continuous group on fixed-action tori,
the Sobolev homeomorphisms `H^s → h^s` for all real `s ≥ 0`, and the fact that every finite-action field
is in every `H^s`. -/
theorem stageA {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    (hΦ : IsStronglySymplectic Φ) (hcΦ : Continuous Φ) (hcΨ : Continuous (chartInv hΦ))
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (hFR : FieldRotation hΦ κ) :
    (∃ ν : ℤ → ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
            Φ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), (RootIndexedMasses.masses hκ u).1 n = 0 →
        Φ (flowMap hκ.le u t) n = 0) ∧
      (∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u)) ∧
      (∀ n : ℤ, ContinuousOn (ν n) {a : ActionTorus.PosL1 | 0 < a.1 n}) ∧
      (∀ a : ActionTorus.PosL1, ∀ z ∈ ActionTorus.actionTorus a, ∀ s t : ℝ,
        chartFlow hΦ hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hΦ hκ.le 0 z = z ∧
        chartFlow hΦ hκ.le (s + t) z = chartFlow hΦ hκ.le s (chartFlow hΦ hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hΦ hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hΦ hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hΦ hκ.le t z n -
          chartFlow hΦ hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0))) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, toK hs (e u) = Φ (H02.toL2 hs u)) ∧
    (∀ (u : L2T L), (∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) →
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u) :=
  ⟨physical_rotations_of_commutation hκ hΦ hcΦ hcΨ hmod
      (finiteCommutation_of_fieldRotation hκ hR hΦ hcΦ hcΨ hmod hFR),
    fun s hs => sobolev_homeomorphism hκ hR hΦ hcΦ hcΨ hmod s hs,
    fun u hu s hs => finite_action_mem_Hs hκ hR u hu s hs⟩

#print axioms stageA

end QuantumNLS.REF88StageA
