import NlsGge.Atomic.G1.G1104Host
import NlsGge.Atomic.G1.G1104Sup
import NlsGge.Atomic.G1.G1104FD
import NlsGge.Atomic.G1.G1104Jor
import NlsGge.Atomic.G1.G1104Root
import NlsGge.ThirdConsultation.G1.G1104SNF3

/-!
# G1-104: match characteristic-zero and operator multiplicities

Head: Pro round 9/10 (followup7/8) `STATEMENTS/G1.md` line 759, `theorem G1_104`.

Route (root Decision 12; see `G1104_ROUTE.md`): the direct pointwise route, for every `φ : PotPair`,
`bc`, `z`:

* `algebraicMultiplicity = finrank (rootSpace ..)` (definition);
* `FiniteDimensional (rootSpace ..)` (M7, `G1104FD.rootSpace_finiteDimensional_interval`);
* for `N ≥ finrank`, `opChainSpace φ bc z (N+1) ≃ₗ rootSpace` (M6, `G1104Root`);
* `tayKer bc φ z (N+1) ≃ₗ opChainSpace φ bc z (N+1)` (M4, `G1104Jor.tayChainEquiv`);
* for `N+1 ≥ order det`, `finrank (tayKer ..) = analyticOrderAt (boundaryCharacteristic φ bc) z`
  and `det ≠ 0` (M5, `G1104SNF3`).

Clause 2 follows from clause 1 by the landed `G1104Sup.clause2_of_clause1`.
No hypothesis is added to the head.
-/

set_option autoImplicit false

open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB041
open NlsGge.Atomic.LIB042
open NlsGge.Pilot NlsGge.GK38 MeasureTheory
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1104
noncomputable section

/-- Clause 1 of the G1-104 head, for every boundary condition and spectral parameter. -/
theorem clause1 (φ : PotPair) : NlsGge.Atomic.G1104Sup.Clause1 φ := by
  intro bc z
  have hfd : FiniteDimensional ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z) :=
    NlsGge.Atomic.G1104FD.rootSpace_finiteDimensional_interval φ bc z
  have hdet := NlsGge.ThirdConsultation.G1.G1104SNF3.charTaylorMatrix_det_ne_zero φ bc z
  have hord :=
    NlsGge.ThirdConsultation.G1.G1104SNF3.charTaylorMatrix_det_order_eq_analyticOrderAt
      φ bc z hdet
  have hne : analyticOrderAt (boundaryCharacteristic φ bc) z ≠ ⊤ := by
    rw [← hord]
    exact fun h => hdet (PowerSeries.order_eq_top.1 h)
  refine ⟨hfd, hne, ?_⟩
  set d : ℕ := Module.finrank ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z) with hd
  set o : ℕ := ((NlsGge.ThirdConsultation.G1.G1104SNF3.charTaylorMatrix bc φ z).det).order.toNat
    with ho
  have hN1 : d ≤ max d o := le_max_left d o
  have hN2 : o ≤ max d o + 1 := le_trans (le_max_right d o) (Nat.le_succ _)
  have e1 := NlsGge.Atomic.G1104Root.opChainSpace_equiv_rootSpace_of_finrank_le φ bc z (max d o)
    hN1
  have e2 := NlsGge.Atomic.G1104Jor.tayChainEquiv φ bc z (max d o + 1)
  have hcount :=
    NlsGge.ThirdConsultation.G1.G1104SNF3.concrete_tayKer_finrank_eq_analyticOrderAt
      φ bc z (max d o + 1) hN2
  have hfin : Module.finrank ℂ
      (NlsGge.Atomic.G1104Jor.tayKer bc φ z (max d o + 1)) = d :=
    (e2.trans e1).finrank_eq
  show ((d : ℕ) : ℕ∞) = _
  rw [← hfin]
  exact hcount

/-- The G1-104 head. -/
theorem core (φ : PotPair) :
    (∀ bc : ZSBoundaryCondition, ∀ z : ℂ,
      FiniteDimensional ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z) ∧
      analyticOrderAt (boundaryCharacteristic φ bc) z ≠ ⊤ ∧
      (algebraicMultiplicity (zsRealization (intervalPotential φ) bc) z : ℕ∞) =
        analyticOrderAt (boundaryCharacteristic φ bc) z) ∧
    (∀ z : ℂ,
      ((algebraicMultiplicity
          (zsRealization (intervalPotential φ) .periodic) z +
        algebraicMultiplicity
          (zsRealization (intervalPotential φ) .antiperiodic) z : ℕ) : ℕ∞) =
        analyticOrderAt (perChar φ) z) :=
  ⟨clause1 φ, NlsGge.Atomic.G1104Sup.clause2_of_clause1 φ (clause1 φ)⟩

end
end NlsGge.Atomic.G1104

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_104 (φ : PotPair) :
    (∀ bc : ZSBoundaryCondition, ∀ z : ℂ,
      FiniteDimensional ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z) ∧
      analyticOrderAt (boundaryCharacteristic φ bc) z ≠ ⊤ ∧
      (algebraicMultiplicity (zsRealization (intervalPotential φ) bc) z : ℕ∞) =
        analyticOrderAt (boundaryCharacteristic φ bc) z) ∧
    (∀ z : ℂ,
      ((algebraicMultiplicity
          (zsRealization (intervalPotential φ) .periodic) z +
        algebraicMultiplicity
          (zsRealization (intervalPotential φ) .antiperiodic) z : ℕ) : ℕ∞) =
        analyticOrderAt (perChar φ) z) :=
  NlsGge.Atomic.G1104.core φ

end
end NlsGge.GKDefinitionDesign
