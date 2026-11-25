import Mathlib
import QuantumNLS.QuantumFourierSpecification

/-!
# DEF-021: reflected hierarchy coordinates and physical scaling

Source: `DEFINITIONS_LEDGER.md` (DEF-021), `chapters/definitions.tex`, `def:report-21`.  Ledger text: "The hierarchy
notation uses `Z_j = √2 w_{-j}`, hence `{Z_j, \bar Z_k} = -2iδ_{jk}`.  The physical corrected label is still `n`.  Period
and coupling are converted by `Φ^q_{L,κ}(u) = (κL)^{-1/2} Φ^q_{1,1}(L√κ u(L·))`.  This formula is verified in the
normalization part of the report."  Ambient: fixed positive `L, κ`; integer indices.  Topology: physical and sequence
Hilbert norms.  Conventions: reflection is a coordinate conversion, not a change in the quantum label; the signed
comparison with a published chart is a separate terminal theorem.

## Prerequisites used read-only
DEF-001 (`AddCircle L` with Lebesgue measure of mass `L`, `PhysicalField L = L²(𝕋_L;ℂ)`), DEF-020
(`QuantumFourierSpecification.Coordinates = ℓ²(ℤ)` and `PhysicalField`, the candidate maps `w = Φ^q_{L,κ}`).

## What is realized (definitions; no theorem conclusions)
* `hierarchyZ w = (j ↦ √2 w_{-j})` as an element of `ℓ²(ℤ)` (`hierarchyZ_apply`), and `hierarchyCoordinates Φ u =
  hierarchyZ (Φ u)`.  The reflection `j ↦ -j` only converts coordinates; the quantum label `n` of the action
  `a_n` is untouched (nothing here re-indexes `D.seq`).
* The period-coupling rescaling: `dilation L : AddCircle 1 → AddCircle L` (`x ↦ L x`, the realized
  `AddCircle.equivAddCircle`); `IsRescaling L κ u v` says `v = L√κ u(L·)` (as `L²(𝕋_1)` classes, almost everywhere);
  `scalingFactor L κ = (κL)^{-1/2}`.
* `PeriodCouplingNormalization Φ`: for a family of candidate maps `Φ L κ : L²(𝕋_L) → ℓ²(ℤ)` the displayed conversion
  `Φ L κ u = (κL)^{-1/2} Φ 1 1 (L√κ u(L·))` holds for all `L, κ > 0`, `u`.  It is a PROPERTY of a family of candidate
  maps (the maps themselves are not realized: DEF-020 is a specification), so it is stated, never asserted.

Not asserted (not part of the definition): that `Φ^q` exists, the bracket `{Z_j, \bar Z_k} = -2iδ_{jk}` (a consequence of the symplectic
structure of `w`, which is a theorem about the constructed chart), and that the scaling formula holds for the
constructed chart (it is "verified in the normalization part of the report").
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace QuantumNLS.HierarchyScaling

open QuantumNLS.QuantumFourierSpecification

/-! ### Reflected hierarchy coordinates -/

/-- `j ↦ w_{-j}` is again square summable (reflection of the index set). -/
theorem memℓp_reflect (w : Coordinates) : Memℓp (fun j : ℤ => w (-j)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).1 w.2
  exact (Equiv.neg ℤ).summable_iff.2 h

/-- The hierarchy coordinates `Z_j = √2 w_{-j}`, as an element of `ℓ²(ℤ)`. -/
def hierarchyZ (w : Coordinates) : Coordinates :=
  ⟨fun j => (Real.sqrt 2 : ℂ) * w (-j), (memℓp_reflect w).const_smul (Real.sqrt 2 : ℂ)⟩

theorem hierarchyZ_apply (w : Coordinates) (j : ℤ) :
    hierarchyZ w j = (Real.sqrt 2 : ℂ) * w (-j) := rfl

/-- The reflected hierarchy coordinates of a candidate chart. -/
def hierarchyCoordinates {L : ℝ} [Fact (0 < L)] (Φ : PhysicalField L → Coordinates)
    (u : PhysicalField L) : Coordinates :=
  hierarchyZ (Φ u)

/-! ### Period and coupling conversion -/

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The rescaling of the circle `x ↦ L x`, `AddCircle 1 → AddCircle L`. -/
def dilation (L : ℝ) [Fact (0 < L)] : AddCircle (1 : ℝ) → AddCircle L :=
  AddCircle.equivAddCircle (p := (1 : ℝ)) (q := L) one_ne_zero (Fact.out : 0 < L).ne'

/-- `v = L√κ u(L·)`, as classes in `L²(𝕋_1)`. -/
def IsRescaling (L κ : ℝ) [Fact (0 < L)] (u : PhysicalField L) (v : PhysicalField 1) : Prop :=
  ∀ᵐ x : AddCircle (1 : ℝ) ∂volume,
    (v : AddCircle (1 : ℝ) → ℂ) x =
      ((L * Real.sqrt κ : ℝ) : ℂ) * (u : AddCircle L → ℂ) (dilation L x)

/-- The factor `(κL)^{-1/2}`. -/
def scalingFactor (L κ : ℝ) : ℝ := (κ * L) ^ (-(1 / 2 : ℝ))

/-- The conversion `Φ_{L,κ}(u) = (κL)^{-1/2} Φ_{1,1}(L√κ u(L·))` for a family of candidate maps. -/
def PeriodCouplingNormalization
    (Φ : ∀ (L : ℝ) [Fact (0 < L)], ℝ → PhysicalField L → Coordinates) : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (κ : ℝ), 0 < κ → ∀ (u : PhysicalField L) (v : PhysicalField 1),
    IsRescaling L κ u v → Φ L κ u = ((scalingFactor L κ : ℝ) : ℂ) • Φ 1 1 v

end QuantumNLS.HierarchyScaling

#print axioms QuantumNLS.HierarchyScaling.hierarchyZ
#print axioms QuantumNLS.HierarchyScaling.hierarchyZ_apply
#print axioms QuantumNLS.HierarchyScaling.hierarchyCoordinates
#print axioms QuantumNLS.HierarchyScaling.dilation
#print axioms QuantumNLS.HierarchyScaling.IsRescaling
#print axioms QuantumNLS.HierarchyScaling.PeriodCouplingNormalization
