import QuantumNLS.L2Flow

/-!
# DEF-023: the physical cubic solution

`DEFINITIONS_LEDGER.md` DEF-023 (`chapters/definitions.tex`, `def:report-23`):

"The physical cubic evolution is the unique Duhamel solution of `iu_t = −u_xx + 2κ|u|²u` in
`C(ℝ;L²) ∩ L⁴_loc(ℝ × 𝕋_L)`. It is the solution supplied by ordinary harmonic-analysis
well-posedness. Its identification with coordinate rotations is a further theorem."

Ambient: arbitrary `L²` initial datum, `κ ≥ 0`; topology: continuous time in `L²`, local space-time
`L⁴`.

Realization, on the frozen FL1 (`L2Flow.lean`, `cccbffe5…`, read-only): the torus, `L²(𝕋_L)` with
its mass-`L` Fourier normalization are DEF-001's (`HL L`, `fourierL2`). The harmonic-analysis
well-posedness (EXT-003) is proved internally in Route Y (an elementary proof instead of Bourgain's
`X^{0,b}`; LC1–FL1). `IsFlow κ w` is the solution class: `w ∈ C(ℝ;L²)` and on every time interval
`J = (α, β]` of length `≤ T_L` an `L⁴(J × 𝕋_L)` class whose time slices are `w(t)` and which
satisfies the Duhamel formula `w(t) = U(t − a) w(a) − 2iκ ∫_a^t U(t − s)(|u|²u)(s) ds` between any
two times of `[α, β]`, where `U(t) = e^{it∂_x²}` (the Duhamel form of `iu_t = −u_xx + 2κ|u|²u`).

`physicalCubic κ hκ f` is defined as the FL1 flow; `physicalCubic_spec` is its defining
characterization (it is in the class with value `f` at `t = 0`, and it is the only such curve).
No identification with coordinate rotations is asserted. DEF-022 (the classical charges, with the
same coupling convention `2κ`, energy `I₃ = ∫(|∂_x u|² + κ|u|⁴)`) is the prerequisite fixing the
coupling convention; no charge statement is made here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.L4Strichartz
  QuantumNLS.LocalL4Contraction QuantumNLS.L4Gluing QuantumNLS.L2Flow

namespace QuantumNLS.PhysicalCubic

variable {L : ℝ} [Fact (0 < L)]

/-- The DEF-023 solution class: `w` is a Duhamel solution of `iu_t = −u_xx + 2κ|u|²u` in
`C(ℝ;L²) ∩ L⁴_loc(ℝ × 𝕋_L)` with `w(0) = f`. -/
def IsPhysicalCubicSolution (κ : ℝ) (f : HL L) (w : ℝ → HL L) : Prop :=
  IsFlow κ w ∧ w 0 = f

/-- **DEF-023: the physical cubic evolution** of the datum `f ∈ L²(𝕋_L)`, `κ ≥ 0`. -/
def physicalCubic {κ : ℝ} (hκ : 0 ≤ κ) (f : HL L) : ℝ → HL L := flowMap hκ f

/-- **DEF-023, defining characterization**: the physical cubic evolution is a Duhamel solution in
the class with initial value `f`, and it is the unique one. -/
theorem physicalCubic_spec {κ : ℝ} (hκ : 0 ≤ κ) (f : HL L) :
    IsPhysicalCubicSolution κ f (physicalCubic hκ f) ∧
      ∀ w : ℝ → HL L, IsPhysicalCubicSolution κ f w → w = physicalCubic hκ f :=
  ⟨⟨(flowMap_spec hκ f).1, (flowMap_spec hκ f).2.1⟩,
    fun _ hw => flowMap_unique hκ f hw.1 hw.2⟩

/-- Equivalent form: a curve is the physical cubic evolution iff it is a Duhamel solution in the
class with initial value `f`. -/
theorem isPhysicalCubicSolution_iff {κ : ℝ} (hκ : 0 ≤ κ) (f : HL L) (w : ℝ → HL L) :
    IsPhysicalCubicSolution κ f w ↔ w = physicalCubic hκ f :=
  ⟨(physicalCubic_spec hκ f).2 w, fun h => h ▸ (physicalCubic_spec hκ f).1⟩

/-- The class unfolded: continuity in `L²`, and on every interval of length `≤ T_L` an `L⁴` class
solving the Duhamel equation (coefficient `cNLS κ = −2iκ`) with the curve as its slices. -/
theorem isPhysicalCubicSolution_def (κ : ℝ) (f : HL L) (w : ℝ → HL L) :
    IsPhysicalCubicSolution κ f w ↔
      Continuous w ∧ (∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L),
        ∃ u : Lp ℂ 4 (μJ (L := L) α β), Sol hαβ hlen (cNLS κ) u w) ∧ w 0 = f :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

#print axioms physicalCubic_spec
#print axioms isPhysicalCubicSolution_iff
#print axioms isPhysicalCubicSolution_def

end QuantumNLS.PhysicalCubic
