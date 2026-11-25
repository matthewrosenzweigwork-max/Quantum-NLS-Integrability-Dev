import QuantumNLS.Def044HierarchyR26m

/-! Repaired three-clause DEF-044 interface. The spectral clause remains
explicit at its printed scope; the other two clauses are constructed.
No input is an entire MixedInterface or an arbitrary DEF-033 convention record.
No asymptotic difference limit is asserted or assigned a universal mode. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.Def044BindingR26m
open PhysicalTensor Def044D1SpectralR51a Def044ChartR51a
open Def033CoreR24m Def033HierarchyR24m BetheLabels BetheCoefficientTransform
variable {L κ : ℝ} [Fact (0 < L)]

/-- Receiver minus donor, only in the occupied-donor sector. -/
abbrev adjacent (N r : ℕ) (a b : ℤ) (m : MArr N)
    (hd : Occupation.DonorOK a (marrArr N m).1) : ℝ :=
  TerraMultiRound12Definitions.adjacentDifference L κ N r a b m hd

/-- Total extension with its missing-donor value specified, not discarded. -/
abbrev total (N r : ℕ) (a b : ℤ) (missing : MArr N → ℝ) (m : MArr N) : ℝ :=
  Def033CoreR24m.withMissing L κ N r a b missing m

/-- A target is attached to two actual active frequencies on the same
trajectory. Neither inactive endpoint nor arbitrary multiplier is selected. -/
def ActiveTarget (z : ℤ → ℝ → ℂ) (w : ℤ → ℂ) (a b : ℤ) (c : ℝ) : Prop :=
  ∃ ωa ωb : ℝ, ActiveFrequency (z a) (w a) ωa ∧
    ActiveFrequency (z b) (w b) ωb ∧ c = ωb - ωa

/-- Active-target uniqueness is a theorem about the real rotation law. -/
theorem active_target_unique {z : ℤ → ℝ → ℂ} {w : ℤ → ℂ} {a b : ℤ} {c d : ℝ}
    (hc : ActiveTarget z w a b c) (hd : ActiveTarget z w a b d) : c = d := by
  obtain ⟨ωa, ωb, ha, hb, rfl⟩ := hc
  obtain ⟨ωa', ωb', ha', hb', rfl⟩ := hd
  rw [activeFrequency_unique ha ha', activeFrequency_unique hb hb']

/-- Both endpoints are selected from the unique active frequencies of the
same physical flow. Positive actions are hypotheses only of this target
selection, never of the mixed interface or its zero-action periods. -/
theorem active_targets_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : Def044HierarchyR26m.HierarchyR7B122087Input hκ C) :
    ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΦ : ∀ r, 2 ≤ r → HierarchyFlow.IsHamFlow L (HierarchyFlow.hamiltonian L κ r) (Φ r)),
      ∀ r (hr : 2 ≤ r) (u : Def033HierarchyR24m.Smooth L) (a b : ℤ),
        0 < Def044ChartR51a.action hκ (Def033HierarchyR24m.physical u) a →
        0 < Def044ChartR51a.action hκ (Def033HierarchyR24m.physical u) b →
        ∃! c : ℝ, ActiveTarget
          (fun n t => C.Φ (Def033HierarchyR24m.physical
            ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n)
          (fun n => C.Φ (Def033HierarchyR24m.physical u) n) a b c := by
  obtain ⟨Φ, hΦ, hf⟩ := Def044HierarchyR26m.DEF033_higher_intermediate hκ C HierarchyR7B122087Input
  refine ⟨Φ, hΦ, fun r hr u a b ha hb => ?_⟩
  obtain ⟨ωa, hωa, _⟩ := hf r hr u a ha
  obtain ⟨ωb, hωb, _⟩ := hf r hr u b hb
  have hc : ActiveTarget
      (fun n t => C.Φ (Def033HierarchyR24m.physical
        ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n)
      (fun n => C.Φ (Def033HierarchyR24m.physical u) n) a b (ωb - ωa) :=
    ⟨ωa, ωb, hωa, hωb, rfl⟩
  exact ⟨ωb - ωa, hc, fun _ hd => active_target_unique hd hc⟩

/-- Explicit original product Born marginals. This specifies the law when
needed; it does not dictate a mode of convergence for every proposed limit. -/
abbrev originalBorn (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :=
  Def033CoreR24m.originalBorn hκ u hu N

omit [Fact (0 < L)] in
theorem total_occupied (N r : ℕ) (a b : ℤ) (missing : MArr N → ℝ) (m : MArr N)
    (hd : Occupation.DonorOK a (marrArr N m).1) :
    total (L := L) (κ := κ) N r a b missing m = adjacent (L := L) (κ := κ) N r a b m hd :=
  Def033CoreR24m.withMissing_occupied L κ N r a b missing m hd

omit [Fact (0 < L)] in
theorem total_missing (N r : ℕ) (a b : ℤ) (missing : MArr N → ℝ) (m : MArr N)
    (hd : ¬ Occupation.DonorOK a (marrArr N m).1) :
    total (L := L) (κ := κ) N r a b missing m = missing m :=
  Def033CoreR24m.withMissing_empty L κ N r a b missing m hd

/-- All three source clauses at one profile, measure, chart and hierarchy.
The higher-order hierarchy is exactly the shared R25m conclusion. -/
structure MixedInterface (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) where
  spectral : SpectralInterface hκ (physical u) hu
  chart : Def044ChartR26m.ChartInterface (L := L) hκ
  dynamics : Def044HierarchyR26m.DynamicsInterface hκ chart.chart

/-- INTERMEDIATE: retain the printed spectral dependencies explicitly, then
construct both remaining clauses from accepted proofs and the single pending
printed hierarchy theorem. This does not prove physical spectral inhabitance.
The final accepted-predecessor theorem is intentionally absent. -/
def DEF044_intermediate (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (C : Def021ChartR41b.Chart L κ hκ)
    (quantum : QuantumRequirements (L := L) hκ)
    (scalar : ScalarRequirements hκ (physical u) hu)
    (HierarchyR7B122087Input : Def044HierarchyR26m.HierarchyR7B122087Input hκ C) :
    MixedInterface hκ u hu :=
  ⟨⟨quantum, scalar⟩, Def044ChartR26m.chart_interface hκ C,
    Def044HierarchyR26m.dynamics_intermediate hκ C HierarchyR7B122087Input⟩

end QuantumNLS.Def044BindingR26m
#print axioms QuantumNLS.Def044BindingR26m.active_targets_intermediate
#print axioms QuantumNLS.Def044BindingR26m.active_target_unique
#print axioms QuantumNLS.Def044BindingR26m.total_occupied
#print axioms QuantumNLS.Def044BindingR26m.total_missing
#print axioms QuantumNLS.Def044BindingR26m.DEF044_intermediate
#print QuantumNLS.Def044BindingR26m.DEF044_intermediate
