import QuantumNLS.IndexedMassProperness
/-! integrator-authored trusted spec for DEF-019 and DEF-018 (DEFINITIONS_LEDGER.md def:report-19, def:report-18).
DEF-019: for a ∈ ℓ¹_+(ℤ), T_a = {z ∈ ℓ²(ℤ) : |z_n|² = a_n} with the inherited ℓ² norm topology; the product of
circles acts continuously by coordinate rotations preserving T_a, fixing zero-action coordinates; T_a is compact
and nonempty.
DEF-018 (parametric in the DEF-014 data D): the indexed-mass map is proper iff the preimage of every compact
subset of ℓ¹_+(ℤ) is compact in physical L²; a fibre is the preimage of one action vector. -/
namespace DEF018_019Spec
open QuantumNLS.ActionTorus QuantumNLS.IndexedMassProperness QuantumNLS.ResetNormalizationUniqueness MeasureTheory

theorem spec :
    -- DEF-019
    (∀ (a : PosL1) (z : S2 ℤ), z ∈ actionTorus a ↔ ∀ n, ‖z n‖ ^ 2 = a.1 n) ∧
    (∀ a : PosL1, IsCompact (actionTorus a) ∧ (actionTorus a).Nonempty) ∧
    (∀ (θ : ℤ → Circle) (z : S2 ℤ) (n : ℤ), rotate θ z n = (θ n : ℂ) * z n) ∧
    (∀ (θ : ℤ → Circle) (a : PosL1) (z : S2 ℤ), z ∈ actionTorus a → rotate θ z ∈ actionTorus a) ∧
    (∀ (θ : ℤ → Circle) (a : PosL1) (z : S2 ℤ) (n : ℤ), z ∈ actionTorus a → a.1 n = 0 → rotate θ z n = z n) ∧
    Continuous (fun p : (ℤ → Circle) × S2 ℤ => rotate p.1 p.2) ∧
    (∀ z : S2 ℤ, rotate 1 z = z) ∧ (∀ (θ φ : ℤ → Circle) (z : S2 ℤ), rotate (θ * φ) z = rotate θ (rotate φ z)) ∧
    -- DEF-018
    (∀ (L κ : ℝ) [Fact (0 < L)] (D : IndexedMassData L κ),
      (IndexedMassProper D ↔ ∀ K : Set PosL1, IsCompact K → IsCompact (D.map ⁻¹' K)) ∧
      (∀ (u : Lp ℂ 2 (volume : Measure (AddCircle L))) (n : ℤ), (D.map u).1 n = D.seq u n) ∧
      (∀ a : PosL1, actionFibre D a = D.map ⁻¹' {a}) ∧
      (IndexedMassProper D → ∀ a : PosL1, IsCompact (actionFibre D a))) := by
  refine ⟨fun a z => Iff.rfl, fun a => ⟨isCompact_actionTorus a, actionTorus_nonempty a⟩, ?_,
    fun θ a z hz => rotate_mem θ hz, fun θ a z n hz hn => rotate_apply_of_eq_zero θ hz hn,
    continuous_rotate, rotate_one, rotate_mul, ?_⟩
  · intro θ z n; rfl
  · intro L κ _ D
    exact ⟨Iff.rfl, fun u n => rfl, fun a => rfl, fun h a => h.isCompact_fibre a⟩

end DEF018_019Spec
#print axioms DEF018_019Spec.spec
