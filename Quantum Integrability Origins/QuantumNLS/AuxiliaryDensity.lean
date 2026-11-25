import Mathlib
import QuantumNLS.CartesianOccupationTransfer
import QuantumNLS.StrongSymbolDef
import QuantumNLS.TraceClass

/-!
# DEF-029: auxiliary one-body density and common-phase ray

Source: `DEFINITIONS_LEDGER.md:621` (DEF-029), `chapters/definitions.tex`, `def:report-29`.  Ledger text: "For the gauged
coefficient vector, define `Γ_{N,ab} = ⟨ψ_N, E^q_{N,ab} ψ_N⟩`.  This positive trace-one matrix acts on the auxiliary
label space `ℓ²(ℤ)`.  Its rank-one limit `|w⟩⟨w|` determines `w` up to multiplication by one unit complex scalar.  A
nonzero column, normalized to unit norm and with its anchor phase fixed, supplies a representative of that ray."
Ambient: unit total mass, a fixed nonzero anchor in the limit.  Topology: trace norm; `ℓ²` norm for a normalized
column.  Convention: the auxiliary matrix is distinct from a physical reduced density matrix.

## Prerequisites used read-only
DEF-026 (`CartesianOccupationTransfer`): `physical b g a c = E^q_{N,ac}` (the pullback of `E_{N,ac}` through the gauged
transform), `coordinates b g` (the gauged coefficient map), `OccupationHilbert.E`.  DEF-028 (`StrongSymbolDef`):
`IsNormalized` (the unit total mass of the preparation).  `TraceClass.traceNorm` (DEF-030's trace norm) for the
topology.

## What is realized (definitions; no theorem conclusions)
* `gammaEntry b g ψ a c = ⟨ψ, E^q_{N,ac} ψ⟩` and its gauged-coefficient form `gammaEntryCoefficient φ a c =
  ⟨φ, E_{N,ac} φ⟩`, `φ = coordinates b g ψ`.  `gammaEntry_eq_coefficient` is the (trivial) agreement of the two
  readings of "the gauged coefficient vector".
* `IsAuxiliaryOperator T Γ`: `T` is a bounded operator on `ℓ²(ℤ) = OneParticle` whose matrix in the canonical basis
  is `Γ` (`⟨e_a, T e_c⟩ = Γ_{ac}`).  That `Γ_N` is such a bounded positive trace-one operator is the ledger's
  descriptive sentence (a theorem about `Γ_N`, not part of the data); the operator is therefore an explicit
  PARAMETER `T`, constrained only by its matrix.
* `rankOneOperator w = |w⟩⟨w|` (`rankOneOperator_matrix`: its matrix is `w_a \bar w_c`) and `HasRankOneLimit T w`: `‖T_N − |w⟩⟨w|‖₁ → 0` in trace norm (the topology).
  The classical symbol `c_{ab} = w_a \bar w_b` of DEF-026 is the matrix of `|w⟩⟨w|` in this convention
  (`⟨e_a, |w⟩⟨w| e_b⟩ = w_a \bar w_b`).
* `commonPhaseRay w = {c w : ‖c‖ = 1}` (the ray: `w` up to one unit scalar).
* `column T c = T e_c`, `normalizedColumn T c = T e_c/‖T e_c‖` (unit norm when nonzero), `anchorPhase n v =
  \bar{v_n}/|v_n|` and `anchorRepresentative n T c = anchorPhase n (normalizedColumn T c) • normalizedColumn T c`:
  the normalized column with its phase fixed so that the anchor coordinate `n` is real and nonnegative.  This
  anchor convention ("anchor phase fixed") is a CHOICE of the realization: the ledger does not state which fixed phase;
  positive-real anchor is the one used here.  That the anchored normalized column is a representative of the ray
  of `w` (for a nonzero column and a nonzero anchor in the limit) is the ledger's last sentence, a theorem, not asserted.
* `AuxiliaryData`: the preparation (a family of bases, one gauge, unit vectors `ψ_N`), with `IsNormalized` (DEF-028).
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace QuantumNLS.AuxiliaryDensity

open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
  QuantumNLS.OccupationUnitary QuantumNLS.CartesianOccupationTransfer

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `Γ_{N,ac} = ⟨ψ_N, E^q_{N,ac} ψ_N⟩` (DEF-029, with `E^q` the DEF-026 pullback). -/
def gammaEntry (b : BetheBasis L N) (g : Gauge) (ψ : HN L N) (a c : ℤ) : ℂ :=
  ⟪ψ, physical b g a c ψ⟫_ℂ

/-- The same entry for the gauged coefficient vector `φ`: `⟨φ, E_{N,ac} φ⟩`. -/
def gammaEntryCoefficient (φ : QuantumNLS.OccupationHilbert.H N) (a c : ℤ) : ℂ :=
  ⟪φ, QuantumNLS.OccupationHilbert.E N a c φ⟫_ℂ

theorem gammaEntry_eq_coefficient (b : BetheBasis L N) (g : Gauge) (ψ : HN L N) (a c : ℤ) :
    gammaEntry b g ψ a c = gammaEntryCoefficient (coordinates b g ψ) a c := by
  unfold gammaEntry gammaEntryCoefficient
  rw [← physical_coordinates, (coordinates b g).inner_map_map]

/-- `T` is a bounded operator on the auxiliary label space `ℓ²(ℤ)` with matrix `Γ` in the canonical basis. -/
def IsAuxiliaryOperator (T : OneParticle →L[ℂ] OneParticle) (Γ : ℤ → ℤ → ℂ) : Prop :=
  ∀ a c : ℤ, ⟪oneBasis a, T (oneBasis c)⟫_ℂ = Γ a c

/-- The rank-one operator `|w⟩⟨w|` on `ℓ²(ℤ)`. -/
def rankOneOperator (w : OneParticle) : OneParticle →L[ℂ] OneParticle :=
  InnerProductSpace.rankOne ℂ w w

/-- The matrix of `|w⟩⟨w|` is `w_a \bar w_c`, the DEF-026 classical symbol `c_{ac}` of `w` (so the limit
convention matches `CartesianOccupationTransfer.symbol`). -/
theorem rankOneOperator_matrix (w : OneParticle) :
    IsAuxiliaryOperator (rankOneOperator w) (fun a c => w a * conj (w c)) := by
  intro a c
  simp only [rankOneOperator, InnerProductSpace.rankOne_apply, oneBasis_apply, inner_smul_right,
    lp.inner_single_left, lp.inner_single_right]
  simp [mul_comm]

/-- `T_N → |w⟩⟨w|` in trace norm. -/
def HasRankOneLimit (T : ∀ _ : ℕ, OneParticle →L[ℂ] OneParticle) (w : OneParticle) : Prop :=
  Tendsto (fun n : ℕ => QuantumNLS.TraceClass.traceNorm (T n - rankOneOperator w)) atTop (𝓝 0)

/-- The common-phase ray of `w`: `w` up to multiplication by one unit complex scalar. -/
def commonPhaseRay (w : OneParticle) : Set OneParticle :=
  {v | ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • w}

/-- The column `c` of the operator `T`: `T e_c`. -/
def column (T : OneParticle →L[ℂ] OneParticle) (c : ℤ) : OneParticle := T (oneBasis c)

/-- The column normalized to unit norm (it has unit norm when it is nonzero). -/
def normalizedColumn (T : OneParticle →L[ℂ] OneParticle) (c : ℤ) : OneParticle :=
  (((‖column T c‖ : ℝ) : ℂ))⁻¹ • column T c

/-- The unit phase `\bar{v_n}/|v_n|` that makes the anchor coordinate `v_n` real and nonnegative. -/
def anchorPhase (n : ℤ) (v : OneParticle) : ℂ := conj (v n) / ((‖v n‖ : ℝ) : ℂ)

/-- The normalized column with its anchor phase fixed (anchor coordinate `n` real nonnegative). -/
def anchorRepresentative (n : ℤ) (T : OneParticle →L[ℂ] OneParticle) (c : ℤ) : OneParticle :=
  anchorPhase n (normalizedColumn T c) • normalizedColumn T c

/-- The preparation of DEF-029: bases `b_N`, one gauge `g`, and vectors `ψ_N` of unit total mass (DEF-028). -/
structure AuxiliaryData (L : ℝ) [Fact (0 < L)] where
  b : ∀ N : ℕ, BetheBasis L N
  g : Gauge
  ψ : ∀ N : ℕ, HN L N
  normalized : QuantumNLS.StrongSymbolDef.IsNormalized ψ

/-- `Γ_{N,ab}` of the preparation. -/
def AuxiliaryData.gamma (D : AuxiliaryData L) (N : ℕ) (a c : ℤ) : ℂ :=
  gammaEntry (D.b N) D.g (D.ψ N) a c

end QuantumNLS.AuxiliaryDensity

#print axioms QuantumNLS.AuxiliaryDensity.gammaEntry
#print axioms QuantumNLS.AuxiliaryDensity.gammaEntry_eq_coefficient
#print axioms QuantumNLS.AuxiliaryDensity.IsAuxiliaryOperator
#print axioms QuantumNLS.AuxiliaryDensity.rankOneOperator_matrix
#print axioms QuantumNLS.AuxiliaryDensity.HasRankOneLimit
#print axioms QuantumNLS.AuxiliaryDensity.anchorRepresentative
#print axioms QuantumNLS.AuxiliaryDensity.AuxiliaryData.gamma
