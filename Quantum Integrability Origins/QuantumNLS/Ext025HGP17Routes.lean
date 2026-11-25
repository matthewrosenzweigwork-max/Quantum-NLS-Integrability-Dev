import Mathlib
import QuantumNLS.Ext025B3RankContinuation

/-! # EXT-025 GP-17 (Riesz-rank convention): operator-level routes (i) and (ii)

Operator part of the repaired contract FIN-EXT025-GP-17 (`OWNER_CONTRACT_REPAIRS_2026-11-16.md`,
sha256 7af85990...): the finite-rank conclusion is claimed only under
(i) finite total algebraic multiplicity, (ii) finite-dimensional range of the Riesz projection
at a base parameter, propagated by continuity, or (iii) a proved compact resolvent.

Convention (explicit OWNER CHOICE, addendum 2026-11-17 to
`ops/contracts/OWNER_DECISIONS_EXT025_GP14_GP04_GP17_2026-11-17.md`): algebraic multiplicity
of an isolated spectral set is the RANK OF ITS RIESZ PROJECTION (Kato's convention).

Ambiguity recorded, not resolved: review record r81 found source intent NOT DEMONSTRATED. The
source gives no general definition of operator algebraic multiplicity, and the
generalized-eigenspace alternative does not imply finite Riesz rank in general (counterexample
in r81: `C ⊕ L²(0,1)`, `T = 0 ⊕ V` with `V` injective quasinilpotent). Nothing here claims source
intent. The convention is adopted by choice; every consumer is checked separately
(see the GP-17 section of `implementation/review records/haiku_inventory.md`).

Built here:
* `algMult P` := `Module.finrank ℂ (range P)` (the Riesz-rank convention);
* route (i) as stated: finite total algebraic multiplicity is, by definition, finite rank of the
  Riesz projection. Under this convention route (i) is a tautology, not a theorem about spectra;
* route (ii): the frozen theorem `Ext025B3RankContinuation.«FIN-EXT025-GP-17-corrected-rank-continuation»`
  (rank constant along any connected parameter space of continuous idempotents) restated with
  `algMult`.

NOT built here: route (iii) (compact resolvent ⟹ compact Riesz projection ⟹ finite rank), and
the resolvent contour-integral idempotent / commuting statement. See the review record section.

Author: haiku_inventory (EXT-025 GP-17 packaging round, 2026-11-17). No `sorry`, no axioms
beyond the standard three. Frozen modules untouched. -/

noncomputable section
set_option autoImplicit false

open Filter Topology Set

namespace QuantumNLS.Ext025HGP17Routes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Algebraic multiplicity under the Riesz-rank convention (owner choice, 2026-11-17). -/
def algMult (P : E →L[ℂ] E) : ℕ := Module.finrank ℂ (LinearMap.range P.toLinearMap)

/-- "Finite total algebraic multiplicity" under the Riesz-rank convention: the range of the
Riesz projection is finite-dimensional. -/
def HasFiniteAlgMult (P : E →L[ℂ] E) : Prop :=
  FiniteDimensional ℂ (LinearMap.range P.toLinearMap)

/-- ROUTE (i), as stated in the repaired text. Under the Riesz-rank convention, the hypothesis
"finite total algebraic multiplicity" is exactly "finite rank of the Riesz projection", so the
finite-rank conclusion is the hypothesis itself. This is a convention consequence, not a spectral
theorem; it does not establish finite rank for any operator. -/
theorem route_i (P : E →L[ℂ] E) (h : HasFiniteAlgMult P) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) := h

/-- ROUTE (ii), restated with `algMult`: finite rank at one base parameter of a continuous
idempotent family propagates to every parameter, with the same algebraic multiplicity. -/
theorem route_ii {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (P : X → E →L[ℂ] E) (hc : Continuous P) (hid : ∀ x v, P x (P x v) = P x v)
    (x₀ : X) [FiniteDimensional ℂ (LinearMap.range (P x₀).toLinearMap)] (x : X) :
    HasFiniteAlgMult (P x) ∧ algMult (P x) = algMult (P x₀) :=
  QuantumNLS.Ext025B3RankContinuation.«FIN-EXT025-GP-17-corrected-rank-continuation» P hc hid x₀ x

end QuantumNLS.Ext025HGP17Routes

#print axioms QuantumNLS.Ext025HGP17Routes.route_i
#print axioms QuantumNLS.Ext025HGP17Routes.route_ii
