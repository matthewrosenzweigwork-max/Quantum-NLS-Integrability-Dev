import Mathlib
import QuantumNLS.ActionTorus
import QuantumNLS.QuantumFourierSpecification
import QuantumNLS.BetheOccupationGauge

/-!
# DEF-053: count rotations and the full product of angle circles

Source: `DEFINITIONS_LEDGER.md` (DEF-053), `chapters/global/product_torus.tex`, `thm:global-product-torus`.  Ledger text:
"The product torus is `𝕋^ℤ` with the product topology and product Haar probability.  It acts quantum mechanically by
`V_N(θ)Ψ_{N,m} = e^{-i∑_nθ_nm_n}Ψ_{N,m}`; the sum is finite on each basis vector.  In coordinates it acts by
`(w_n) ↦ (e^{-iθ_n}w_n)`.  The physical action is the conjugate by the constructed inverse coordinate map."
Ambient: all angle sequences; fixed sector `N`; constructed global chart.  Topology: product topology in parameters;
strong quantum unitaries; norm topology on each fixed action torus.

## Prerequisites used read-only
DEF-006 (`BetheLabels.MArr N`, finitely supported occupation arrays `m : ℤ →₀ ℕ`, `∑ m = N`), the normalized basis
`Ψ_{N,m}` (`BetheCoefficientTransform.BetheBasis`, a Hilbert basis of `H_N` indexed by `MArr N`) and its rephasing
`BetheOccupationGauge.gaugedBasis`; DEF-019 (`ActionTorus.rotate`, the coordinate rotation of `ℓ²(ℤ)`); DEF-020
(`QuantumFourierSpecification.Coordinates`, `PhysicalField`).

## What is realized (definitions; no theorem conclusions)
* `AngleTorus = ℤ → Circle` with the product topology, `circleHaar` the Haar probability measure of `Circle`
  (`haarMeasure ⊤`), and `productHaar = Measure.infinitePi (fun _ => circleHaar)`, the product Haar probability.  An
  angle `θ_n ∈ ℝ/2πℤ` is the circle element `e^{iθ_n}`, so `e^{-iθ_n} = (θ_n)⁻¹`.
* `countPhase θ m = ∏_n (θ_n)⁻¹^{m_n} = e^{-i∑_nθ_nm_n}` (a `Finsupp.prod`: finite on every `m`), `phaseGauge θ` the
  corresponding unit-phase gauge, and the **quantum action** `quantumRotation b θ = b.repr ≫ (gaugedBasis b (phaseGauge θ)).repr⁻¹`,
  the unitary of `H_N` taking `Ψ_{N,m}` to `e^{-i∑θ_nm_n}Ψ_{N,m}`; `quantumRotation_basis` records that defining
  relation on each basis vector.
* `coordinateRotation θ = ActionTorus.rotate (θ⁻¹)`, `(w_n) ↦ (e^{-iθ_n} w_n)` on `ℓ²(ℤ)` (DEF-019).
* `physicalRotation Φ θ = Φ⁻¹ ∘ coordinateRotation θ ∘ Φ` for a coordinate bijection `Φ : L²(𝕋_L) ≃ ℓ²(ℤ)`.  The
  constructed global chart and its inverse are not realized in the repository: `Φ` is an explicit PARAMETER.

Not asserted (theorems of the source): that `quantumRotation` is strongly continuous in `θ`, that it agrees with
`physicalRotation` under the chart, preservation of action tori, and Haar invariance.
-/

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.CountRotations

open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
  QuantumNLS.QuantumFourierSpecification

local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The full product of angle circles `𝕋^ℤ`, with the product topology. -/
abbrev AngleTorus : Type := ℤ → Circle

/-- The Haar probability measure of the circle. -/
def circleHaar : Measure Circle := Measure.haarMeasure ⊤

instance : IsProbabilityMeasure circleHaar :=
  ⟨by
    have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle))
    simpa [circleHaar] using h⟩

/-- The product Haar probability measure on `𝕋^ℤ`. -/
def productHaar : Measure AngleTorus := Measure.infinitePi fun _ : ℤ => circleHaar

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `e^{-i∑_nθ_nm_n} = ∏_n (θ_n)⁻¹^{m_n}`, a finite product over the support of `m`. -/
def countPhase (θ : AngleTorus) (m : MArr N) : Circle :=
  m.1.prod fun n k => (θ n)⁻¹ ^ k

/-- The unit-phase gauge `m ↦ e^{-i∑_nθ_nm_n}` (in every sector). -/
def phaseGauge (θ : AngleTorus) : Gauge :=
  fun _ m => ⟨(countPhase θ m : ℂ), Circle.norm_coe _⟩

/-- The quantum action `V_N(θ)`: the unitary of `H_N` with `V_N(θ)Ψ_{N,m} = e^{-i∑θ_nm_n}Ψ_{N,m}`. -/
def quantumRotation (b : BetheBasis L N) (θ : AngleTorus) : HN L N ≃ₗᵢ[ℂ] HN L N :=
  b.repr.trans (gaugedBasis b (phaseGauge θ)).repr.symm

theorem quantumRotation_basis (b : BetheBasis L N) (θ : AngleTorus) (m : MArr N) :
    quantumRotation b θ (b m) = ((countPhase θ m : Circle) : ℂ) • b m := by
  unfold quantumRotation
  rw [LinearIsometryEquiv.trans_apply, HilbertBasis.repr_self, HilbertBasis.repr_symm_single,
    gaugedBasis_apply]
  rfl

/-- The coordinate action `(w_n) ↦ (e^{-iθ_n} w_n)` on `ℓ²(ℤ)`. -/
def coordinateRotation (θ : AngleTorus) (w : Coordinates) : Coordinates :=
  QuantumNLS.ActionTorus.rotate (fun n => (θ n)⁻¹) w

/-- The physical action: conjugation of the coordinate action by the (parametric) coordinate bijection. -/
def physicalRotation (Φ : PhysicalField L ≃ Coordinates) (θ : AngleTorus) (u : PhysicalField L) :
    PhysicalField L :=
  Φ.symm (coordinateRotation θ (Φ u))

end QuantumNLS.CountRotations

#print axioms QuantumNLS.CountRotations.productHaar
#print axioms QuantumNLS.CountRotations.countPhase
#print axioms QuantumNLS.CountRotations.quantumRotation
#print axioms QuantumNLS.CountRotations.quantumRotation_basis
#print axioms QuantumNLS.CountRotations.coordinateRotation
#print axioms QuantumNLS.CountRotations.physicalRotation
