import Mathlib
import QuantumNLS.BulkResponseForm
import QuantumNLS.BornConvergence
import QuantumNLS.EmpiricalRapidity
import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.SpatialTransfer

/-!
# DEF-052 for the actual limiting measure `μ_{κ,u}`: its literal DEF-010 specification and the bulk-response data

Sources: `DEFINITIONS_LEDGER.md` DEF-052 and DEF-010; `source/chapters/foundations/ROOT_spectral_measure.tex`
(`thm:root-measure`, R-09E1EAE9) and `ROOT_spectral_density.tex` (`thm:root-spectral-density`, R-7E0532E7);
`source/chapters/root_response/F03.tex` (`CC:F03:section`, `CC:F03:core`).  Terra r125 held DEF-052 because the actual
measure was a parameter.

## What the source says `μ_{κ,u}` is
DEF-010 names the limiting unit-mass measure `μ_{κ,u}` and R-09E1EAE9 defines it by the quantum model: for a unit
`u ∈ L²(𝕋_L)` there is a unique Borel probability measure `μ_{κ,u}` such that the empirical rapidity measures
`ν_N = N⁻¹∑_jδ_{q_j}` of the complete Bethe basis at coupling `κ/N`, under the Born law `|⟨Ψ_{N,α}, u^{⊗N}⟩|²`, converge
weakly in probability to it.  R-7E0532E7 gives its density `(πκ)⁻¹ arcosh(|Δ_u(t)|/2)·1_{|Δ_u(t)|>2}` (with `Δ_u` the DEF-013
discriminant), continuous, bounded by `‖u‖_{L¹}/(π√κ)`, with bounded-interval components and locally finite endpoints; F03's
`CC:F03:core` records that the measure of every unit `H¹` input satisfies the density assumptions of the form.

## What is realizable from the accepted objects, and what is not
* **Realized here (literal specification, no invention):** `IsLimitingRapidityMeasure` is exactly "`ν_N → μ` weakly in
  probability on the Born spaces", built from the accepted unconditional physical basis `UnconditionalBetheBasis.meanField_physicalBasis`
  (UBB1), DEF-010's `bornMeasure`/`empiricalMeasureκ`, and DEF-011's `TendstoInProbabilityWeak` (Lévy-Prokhorov).  Its
  uniqueness half (the "unique" of R-09E1EAE9) is PROVED (`IsLimitingRapidityMeasure.unique`) from `TendstoInProbability.unique`.
  `HasRootDensity` is the explicit R-7E0532E7 density formula as a predicate on a measure, through the realized DEF-013
  `discriminant` and mathlib's `Real.arcosh`; it is not asserted of any measure.
* **Not realized in the repository (theorem conclusions depending on unproved spectral results):** the EXISTENCE of `μ_{κ,u}`
  (R-09E1EAE9: transfer-eigenvalue concentration `eq:root-transfer-estimates`, the injectivity estimate, the vague-compactness and no-loss-of-mass
  steps), its density formula (R-7E0532E7, which also needs the `L¹` fundamental-solution theory that `SpatialTransfer`
  records as a gap), finiteness of its second moment, and `CC:F03:core`'s density assumptions for `H¹` input.  PROP-002
  (`LabelWeakJointLimit`) takes `ν_N ⇀ μ` as a hypothesis, DEF-043 is parametric in `μ`, and R-409128A9 (`RootHilbertQuantiles`) is a
  monotonicity lemma for Hilbert transforms of density measures, not an existence theorem for `μ_{κ,u}`; none of them
  constructs the measure.
* Therefore the measure is NOT invented: `ActualBulkData` carries a measure `μ` together with the proof field `limit :
  IsLimitingRapidityMeasure …` (it IS `μ_{κ,u}`, by the proved uniqueness) and the F03 standing assumptions `BulkMeasure μ`
  as an explicit field (the source's theorem that the actual measure of a unit `H¹` profile satisfies them is not formalized).
  From it `ActualBulkData.toBulkResponseData` produces the DEF-052 data of `BulkResponseForm` (form, quantile `Q`, response
  equation) FOR THE ACTUAL MEASURE, and the response predicate depends only on `(L,κ,u)` (`ActualBulkData.measure_unique`).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.BulkResponseActual

open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (BetheBasis freeBasis)
open QuantumNLS.EmpiricalRapidity (bornMeasure empiricalMeasureκ isProbabilityMeasure_empiricalMeasure)
open QuantumNLS.BornConvergence (TendstoInProbabilityWeak TendstoInProbability)

variable {L : ℝ} [Fact (0 < L)]

/-- The accepted unconditional physical basis `Ψ_{N,m}` at coupling `κ/N` for `N ≥ 1` (UBB1; an arbitrary basis at `N = 0`,
which no statement uses). -/
def physBasis (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (N : ℕ) : BetheBasis L N :=
  if hN : 1 ≤ N then QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ
  else freeBasis L N

/-- The empirical rapidity measure `ν_N(m) = N⁻¹∑_jδ_{q_j(m)}` (roots at coupling `κ/N`) as a probability measure
(`N ≥ 1`; the value at `N = 0` is immaterial). -/
def empiricalProb (L κ : ℝ) (N : ℕ) (m : MArr N) : ProbabilityMeasure ℝ :=
  if h : 0 < N then ⟨empiricalMeasureκ L κ m, isProbabilityMeasure_empiricalMeasure L (κ / N) h m⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- **`μ` is the quantum-derived limiting rapidity measure `μ_{κ,u}` (DEF-010, R-09E1EAE9)**: `ν_N → μ` weakly in
probability on the Born spaces `(𝓜_N, |⟨Ψ_{N,m}, u^{⊗N}⟩|²)` of the physical basis at coupling `κ/N`. -/
def IsLimitingRapidityMeasure (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (μ : ProbabilityMeasure ℝ) : Prop :=
  TendstoInProbabilityWeak (fun N => bornMeasure (physBasis L hκ N) u hu)
    (fun N m => empiricalProb L κ N m) μ

/-- **Uniqueness of `μ_{κ,u}`** (the "unique" of R-09E1EAE9). -/
theorem IsLimitingRapidityMeasure.unique {κ : ℝ} {hκ : 0 < κ} {u : L2T L} {hu : ‖u‖ = 1}
    {μ μ' : ProbabilityMeasure ℝ} (h : IsLimitingRapidityMeasure L κ hκ u hu μ)
    (h' : IsLimitingRapidityMeasure L κ hκ u hu μ') : μ = μ' := by
  have := TendstoInProbability.unique h h'
  exact congrArg LevyProkhorov.toMeasure this

/-! ### The explicit density of R-7E0532E7 as a predicate -/

/-- `(πκ)⁻¹ arcosh(|Δ_u(t)|/2)` on `{|Δ_u| > 2}`, `0` elsewhere (`eq:root-explicit-density`), `Δ_u` the DEF-013 discriminant of the
continuous representative `uf`. -/
def rootDensityFormula (L κ : ℝ) (uf : ℝ → ℂ) (t : ℝ) : ℝ :=
  if 2 < ‖QuantumNLS.SpatialTransfer.discriminant L κ uf (t : ℂ)‖ then
    Real.arcosh (‖QuantumNLS.SpatialTransfer.discriminant L κ uf (t : ℂ)‖ / 2) / (Real.pi * κ)
  else 0

/-- `μ` has the density of R-7E0532E7 (a predicate; asserted of no measure here). -/
def HasRootDensity (L κ : ℝ) (uf : ℝ → ℂ) (μ : Measure ℝ) : Prop :=
  μ = volume.withDensity (fun t => ENNReal.ofReal (rootDensityFormula L κ uf t))

/-- `uf` is a continuous `L`-periodic representative of the `L²` class `u`. -/
def IsPeriodicRepresentative (L : ℝ) [Fact (0 < L)] (u : L2T L) (uf : ℝ → ℂ) : Prop :=
  Continuous uf ∧ (∀ x, uf (x + L) = uf x) ∧
    (u : AddCircle L → ℂ) =ᵐ[volume] fun x => uf ((AddCircle.equivIco L 0 x : ℝ))

/-! ### The bulk-response data of the actual measure -/

/-- DEF-052 data for the actual limiting measure of a unit profile `u`: `μ` IS `μ_{κ,u}` (field `limit`), and satisfies the
standing assumptions of `CC:F03:section` (field `bulk`; the source's theorem that the actual measure of a unit `H¹` profile does is
not formalized, so it is an explicit field). -/
structure ActualBulkData (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) where
  μ : ProbabilityMeasure ℝ
  limit : IsLimitingRapidityMeasure L κ hκ u hu μ
  bulk : QuantumNLS.BulkResponseForm.BulkMeasure (μ : Measure ℝ)

variable {κ : ℝ} {hκ : 0 < κ} {u : L2T L} {hu : ‖u‖ = 1}

/-- The DEF-052 data of `BulkResponseForm` for the actual measure. -/
def ActualBulkData.toBulkResponseData (D : ActualBulkData L κ hκ u hu) :
    QuantumNLS.BulkResponseForm.BulkResponseData where
  L := L
  κ := κ
  hL := Fact.out
  hκ := hκ
  μ := D.μ
  hμ := D.bulk

/-- The measure of the data is the unique `μ_{κ,u}`: any two data for the same `(L, κ, u)` have equal measures, hence the same quantile and
the same response predicate. -/
theorem ActualBulkData.measure_unique (D D' : ActualBulkData L κ hκ u hu) : D.μ = D'.μ :=
  D.limit.unique D'.limit

theorem ActualBulkData.response_iff (D D' : ActualBulkData L κ hκ u hu)
    (W : QuantumNLS.BulkResponseForm.L2Unit) :
    D.toBulkResponseData.IsResponse W ↔ D'.toBulkResponseData.IsResponse W := by
  have h : D.μ = D'.μ := D.measure_unique D'
  unfold ActualBulkData.toBulkResponseData QuantumNLS.BulkResponseForm.BulkResponseData.IsResponse
    QuantumNLS.BulkResponseForm.BulkResponseData.Q
  simp only [h]

end QuantumNLS.BulkResponseActual

#print axioms QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure.unique
#print axioms QuantumNLS.BulkResponseActual.HasRootDensity
#print axioms QuantumNLS.BulkResponseActual.ActualBulkData.toBulkResponseData
#print axioms QuantumNLS.BulkResponseActual.ActualBulkData.measure_unique
#print axioms QuantumNLS.BulkResponseActual.ActualBulkData.response_iff
