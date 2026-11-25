import Mathlib
import QuantumNLS.ExactDensity
import QuantumNLS.AuxiliaryDensity
import QuantumNLS.UnconditionalPhysicalWrappers
import QuantumNLS.UnconditionalBetheBasis

/-!
# DEF-029 closed for the physical family: the actual auxiliary operator `Γ_N[ψ_N]` and the source's anchor convention

Source: `DEFINITIONS_LEDGER.md` DEF-029 (`def:report-29`) and `source/chapters/core/projective_reconstruction.tex`
(`prop:exact-density` R-BB03032A, `cor:column` R-AA5864B7 with the remark after it, `prop:obstruction`).  Terra r125 left
DEF-029 as parametric support: the operator on `ℓ²(ℤ)` was a parameter and the anchor-phase choice was flagged.

## The actual operator (now constructed)
`ExactDensity.Gamma d` (accepted `388d49e7`, R-BB03032A) constructs `Γ = T†T = ∑_ν |v_ν⟩⟨v_ν|` from a coefficient vector `d`.
For the physical family: the unconditional physical basis at coupling `κ/N` (UBB1 `meanField_physicalBasis`, `N = 1+q`), the
selected gauge `s L κ` of a once-for-all `UniversalSelection` (the gauge of the wrapped
`UnconditionalPhysicalWrappers.CartesianTransfer.selectedMeanFieldPhysical_physical`), and unit vectors `ψ_N` form a
`PhysicalPreparation`.  `gammaOp q = Gamma (J_N ψ_N)` is proved to satisfy DEF-029's `IsAuxiliaryOperator` with the matrix
`Γ_{N,ab} = ⟨ψ_N, E^q_{N,ab} ψ_N⟩` (`gammaEntry`, and `gammaEntry_eq_selected` identifies it with the wrapped selected mean-field
transfer), is positive, trace class and has trace one (`auxiliary_operator`); the full R-BB03032A entry statement applies verbatim to the family
(`ExactDensity.exact_density (P.basis q) P.gauge (P.ψ q) (P.unit q)`).  No unrealized object remains for this part; the unit vectors `ψ_N` are the preparation data.

## Anchor-phase convention against the source
The source fixes no separate phase factor: `cor:column` takes the column `Γ_N e_b` at the nonzero coordinate `b` of the limit
(`c_N^{(b)} = Γ e_b/√(Γ_{bb})`, exactly normalized `ĉ = Γ e_b/‖Γ e_b‖`), and the remark states the limit "has positive real `b`-th
coordinate and is `e^{-i arg w_b} w`".  For a positive operator the anchor coordinate `(Γ e_b)_b = Γ_{bb}` is real and
nonnegative automatically (`column_anchor_nonneg`).  Hence the DEF-029 realization `anchorRepresentative b T b` (anchor index = column
index = `b`, positive-real-anchor phase) coincides with the source's `ĉ` whenever `Γ_{bb} ≠ 0`: `anchorRepresentative_self`
(`anchorPhase = 1`, `normalizedColumn_anchor_pos`).  The limit column is `(\overline{w_b}/|w_b|) w ∈` the common-phase ray
(`normalizedColumn_rankOne`, `normalizedColumn_rankOne_mem_ray`), and `tendsto_normalizedColumn` (trace-norm convergence ⟹ normalized
column convergence, qualitative `eq:column-limit`) holds under the hypothesis `HasRankOneLimit`.  `sourceColumn` is the unnormalized
`c_N^{(b)}`.  The general `anchorRepresentative n T c` (anchor index different from the column index) remains a convenience
of the DEF-029 realization; the source uses only `n = c = b`.

## Parameters that remain hypotheses
The limit vector `w` (unit, `w_b ≠ 0`) and the convergence `HasRankOneLimit (fun q => gammaOp q) w`; the preparation `ψ_N`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate ComplexOrder
open Filter Topology

noncomputable section

namespace QuantumNLS.PhysicalAuxiliaryDensity

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity

/-! ### The source's column convention versus the anchor-phase choice of DEF-029 -/

section Anchor

theorem column_apply_anchor (T : OneParticle →L[ℂ] OneParticle) (b : ℤ) :
    column T b b = ⟪oneBasis b, T (oneBasis b)⟫_ℂ := by
  unfold column
  rw [QuantumNLS.OccupationUnitary.oneBasis_apply, lp.inner_single_left]
  simp

/-- The anchor coordinate of the column `Γ e_b` of a positive operator is real and nonnegative. -/
theorem column_anchor_nonneg {T : OneParticle →L[ℂ] OneParticle} (hT : T.IsPositive) (b : ℤ) :
    0 ≤ column T b b := by
  rw [column_apply_anchor]
  exact hT.inner_nonneg_right _

theorem anchorPhase_eq_one_of_pos (n : ℤ) (v : OneParticle) (r : ℝ) (hr : 0 < r)
    (h : v n = (r : ℂ)) : anchorPhase n v = 1 := by
  unfold anchorPhase
  rw [h, Complex.conj_ofReal, norm_real_aux r hr.le]
  exact div_self (by exact_mod_cast hr.ne')
where
  norm_real_aux (r : ℝ) (hr : 0 ≤ r) : ((‖(r : ℂ)‖ : ℝ) : ℂ) = (r : ℂ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

end Anchor


section Column

/-- The source's column `c_N^{(b)} = Γ e_b / √(Γ_{bb})` (`cor:column`). -/
def sourceColumn (T : OneParticle →L[ℂ] OneParticle) (b : ℤ) : OneParticle :=
  (((Real.sqrt (column T b b).re : ℝ) : ℂ))⁻¹ • column T b

/-- **Anchor-phase equivalence.**  For a positive operator whose `b`-th diagonal entry is nonzero, the source's
exactly normalized column `ĉ^{(b)} = Γ e_b/‖Γ e_b‖` already has positive real `b`-th coordinate, so the phase factor
of `anchorRepresentative` (anchor coordinate `b`, column `b`) is `1`:
`anchorRepresentative b T b = normalizedColumn T b`. -/
theorem normalizedColumn_anchor_pos {T : OneParticle →L[ℂ] OneParticle} (hT : T.IsPositive) (b : ℤ)
    (hb : column T b b ≠ 0) : ∃ r : ℝ, 0 < r ∧ normalizedColumn T b b = (r : ℂ) := by
  have h0 := column_anchor_nonneg hT b
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 h0
  have hcb : column T b b = ((column T b b).re : ℂ) := by
    apply Complex.ext <;> simp [← him]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, column T b b = (a : ℂ) := ⟨_, hcb⟩
  have hre' : 0 ≤ a := by
    have : (column T b b).re = a := by rw [ha]; simp
    rw [← this]; exact hre
  have hrepos : 0 < a := by
    rcases hre'.lt_or_eq with h | h
    · exact h
    · exfalso; apply hb; rw [ha, ← h]; simp
  have hnorm : 0 < ‖column T b‖ := by
    refine lt_of_lt_of_le ?_ (lp.norm_apply_le_norm (p := (2 : ENNReal)) (by norm_num) (column T b) b)
    rw [ha, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrepos]; exact hrepos
  refine ⟨a / ‖column T b‖, div_pos hrepos hnorm, ?_⟩
  unfold normalizedColumn
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ha]
  push_cast
  ring

theorem anchorRepresentative_self {T : OneParticle →L[ℂ] OneParticle} (hT : T.IsPositive) (b : ℤ)
    (hb : column T b b ≠ 0) : anchorRepresentative b T b = normalizedColumn T b := by
  obtain ⟨r, hr, h⟩ := normalizedColumn_anchor_pos hT b hb
  unfold anchorRepresentative
  rw [anchorPhase_eq_one_of_pos b _ r hr h, one_smul]

/-- The column of the rank-one limit: `|w⟩⟨w| e_b = \overline{w_b} w`. -/
theorem column_rankOne (w : OneParticle) (b : ℤ) :
    column (rankOneOperator w) b = conj (w b) • w := by
  unfold column rankOneOperator
  rw [InnerProductSpace.rankOne_apply, QuantumNLS.OccupationUnitary.oneBasis_apply,
    lp.inner_single_right]
  simp

/-- **Limiting column** (`eq:column-limit`): the exactly normalized column of `|w⟩⟨w|` is
`e^{-i arg w_b} w = (\overline{w_b}/|w_b|) w`, a point of the common-phase ray of `w`. -/
theorem normalizedColumn_rankOne (w : OneParticle) (hw : ‖w‖ = 1) (b : ℤ) (hb : w b ≠ 0) :
    normalizedColumn (rankOneOperator w) b = (conj (w b) / ((‖w b‖ : ℝ) : ℂ)) • w := by
  unfold normalizedColumn
  rw [column_rankOne, norm_smul, hw, Complex.norm_conj, mul_one, smul_smul]
  congr 1
  rw [inv_mul_eq_div]

theorem normalizedColumn_rankOne_mem_ray (w : OneParticle) (hw : ‖w‖ = 1) (b : ℤ) (hb : w b ≠ 0) :
    normalizedColumn (rankOneOperator w) b ∈ commonPhaseRay w := by
  rw [normalizedColumn_rankOne w hw b hb]
  refine ⟨conj (w b) / ((‖w b‖ : ℝ) : ℂ), ?_, rfl⟩
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (norm_ne_zero_iff.2 hb)

/-- **Column convergence** (`cor:column`, qualitative form): trace-norm convergence to the rank-one limit gives
convergence of the exactly normalized columns to `(\overline{w_b}/|w_b|) w`. -/
theorem tendsto_normalizedColumn (T : ∀ _ : ℕ, OneParticle →L[ℂ] OneParticle) (w : OneParticle)
    (hw : ‖w‖ = 1) (b : ℤ) (hb : w b ≠ 0) (hT : HasRankOneLimit T w) :
    Tendsto (fun n => normalizedColumn (T n) b) atTop
      (𝓝 ((conj (w b) / ((‖w b‖ : ℝ) : ℂ)) • w)) := by
  have hop : Tendsto (fun n => ‖T n - rankOneOperator w‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal ‖T n - rankOneOperator w‖) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
        (fun _ => bot_le) (fun n => QuantumNLS.TraceClass.norm_le_traceNorm _)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h2
  have hcol : Tendsto (fun n => column (T n) b) atTop (𝓝 (column (rankOneOperator w) b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hop
    unfold column
    rw [← ContinuousLinearMap.sub_apply]
    calc _ ≤ ‖T n - rankOneOperator w‖ * ‖oneBasis b‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖T n - rankOneOperator w‖ := by
        rw [QuantumNLS.OccupationUnitary.oneBasis_apply, lp.norm_single (by norm_num)]; simp
  have hy : column (rankOneOperator w) b ≠ 0 := by
    rw [column_rankOne]
    intro h
    have : conj (w b) = 0 ∨ w = 0 := smul_eq_zero.1 h
    rcases this with h1 | h1
    · exact hb (by simpa using h1)
    · simp [h1] at hw
  have hnorm : ContinuousAt (fun x : OneParticle => (((‖x‖ : ℝ) : ℂ))⁻¹ • x)
      (column (rankOneOperator w) b) := by
    have hne : (((‖column (rankOneOperator w) b‖ : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.2 hy
    exact ((Complex.continuous_ofReal.comp continuous_norm).continuousAt.inv₀ hne).smul
      continuousAt_id
  have := hnorm.tendsto.comp hcol
  have hlim : (((‖column (rankOneOperator w) b‖ : ℝ) : ℂ))⁻¹ • column (rankOneOperator w) b =
      (conj (w b) / ((‖w b‖ : ℝ) : ℂ)) • w := by
    have := normalizedColumn_rankOne w hw b hb
    unfold normalizedColumn at this
    exact this
  rw [hlim] at this
  exact this

end Column


/-! ### The actual auxiliary operator of the physical family -/

section Physical

open QuantumNLS.BetheOccupationGauge (UniversalSelection Gauge)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.CartesianOccupationTransfer (coordinates physical)
open QuantumNLS.ExactDensity (Gamma)

/-- A physical preparation at mean-field coupling `κ/N`: a once-for-all gauge selection `s`
(`BetheOccupationGauge.UniversalSelection`) and unit vectors `ψ_N ∈ 𝓗_N`, `N = 1+q`. -/
structure PhysicalPreparation (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) where
  s : UniversalSelection
  ψ : ∀ q : ℕ, HN L (1 + q)
  unit : ∀ q : ℕ, ‖ψ q‖ = 1

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} {hκ : 0 < κ}

/-- The accepted unconditional physical basis `Ψ_{N,m}` at coupling `κ/N` (UBB1). -/
def PhysicalPreparation.basis (_ : PhysicalPreparation L κ hκ) (q : ℕ) : BetheBasis L (1 + q) :=
  QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (1 + q) (by omega) hκ

/-- The selected gauge at `(L, κ)`. -/
def PhysicalPreparation.gauge (P : PhysicalPreparation L κ hκ) : Gauge := P.s L Fact.out κ hκ

/-- DEF-029's matrix `Γ_{N,ab} = ⟨ψ_N, E^q_{N,ab} ψ_N⟩` of the physical family. -/
def PhysicalPreparation.gammaEntry (P : PhysicalPreparation L κ hκ) (q : ℕ) (a c : ℤ) : ℂ :=
  QuantumNLS.AuxiliaryDensity.gammaEntry (P.basis q) P.gauge (P.ψ q) a c

/-- **The actual auxiliary operator `Γ_N[ψ_N]` on `ℓ²(ℤ)`** of the physical family (`N = 1+q`). -/
def PhysicalPreparation.gammaOp (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    OneParticle →L[ℂ] OneParticle :=
  Gamma (coordinates (P.basis q) P.gauge (P.ψ q))

/-- The matrix is the expectation of the wrapped selected mean-field transfer
(`UnconditionalPhysicalWrappers.CartesianTransfer.selectedMeanFieldPhysical_physical`). -/
theorem PhysicalPreparation.gammaEntry_eq_selected (P : PhysicalPreparation L κ hκ) (q : ℕ) (a c : ℤ) :
    P.gammaEntry q a c =
      ⟪P.ψ q, QuantumNLS.UnconditionalPhysicalWrappers.CartesianTransfer.selectedMeanFieldPhysical_physical
        P.s L κ hκ (1 + q) (by omega) a c (P.ψ q)⟫_ℂ := rfl

theorem PhysicalPreparation.norm_coordinates (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    ‖coordinates (P.basis q) P.gauge (P.ψ q)‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, P.unit]

/-- **DEF-029's `IsAuxiliaryOperator`** for the actual `Γ_N[ψ_N]`. -/
theorem PhysicalPreparation.gammaOp_isAuxiliaryOperator (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    IsAuxiliaryOperator (P.gammaOp q) (P.gammaEntry q) := by
  intro a c
  unfold PhysicalPreparation.gammaOp PhysicalPreparation.gammaEntry
  rw [QuantumNLS.ExactDensity.inner_Gamma, ← QuantumNLS.ExactDensity.inner_E_eq_tsum,
    QuantumNLS.AuxiliaryDensity.gammaEntry_eq_coefficient]
  rfl

theorem PhysicalPreparation.gammaOp_isPositive (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    (P.gammaOp q).IsPositive :=
  QuantumNLS.ExactDensity.gamma_isPositive _

theorem PhysicalPreparation.gammaOp_posTrace (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    QuantumNLS.TraceClass.posTrace (P.gammaOp q) = 1 := by
  unfold PhysicalPreparation.gammaOp
  rw [QuantumNLS.ExactDensity.posTrace_Gamma, P.norm_coordinates]
  simp

theorem PhysicalPreparation.gammaOp_isTraceClass (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    QuantumNLS.TraceClass.IsTraceClass (P.gammaOp q) := by
  rw [QuantumNLS.TraceClass.IsTraceClass,
    QuantumNLS.TraceClass.traceNorm_of_isPositive (P.gammaOp_isPositive q), P.gammaOp_posTrace]
  exact ENNReal.one_lt_top

/-- **DEF-029 closed for the physical family**: the actual operator is the positive trace-one trace-class operator
with matrix `Γ_{N,ab} = ⟨ψ_N, E^q_{N,ab} ψ_N⟩` (and `R-BB03032A`'s entry formulas hold for it). -/
theorem PhysicalPreparation.auxiliary_operator (P : PhysicalPreparation L κ hκ) (q : ℕ) :
    IsAuxiliaryOperator (P.gammaOp q) (P.gammaEntry q) ∧ (P.gammaOp q).IsPositive ∧
      QuantumNLS.TraceClass.IsTraceClass (P.gammaOp q) ∧
      QuantumNLS.TraceClass.posTrace (P.gammaOp q) = 1 :=
  ⟨P.gammaOp_isAuxiliaryOperator q, P.gammaOp_isPositive q, P.gammaOp_isTraceClass q,
    P.gammaOp_posTrace q⟩

/-- Under the (hypothesized) trace-norm rank-one limit `|w⟩⟨w|`, `w` a unit vector with `w_b ≠ 0`, the exactly
normalized columns of the physical `Γ_N` converge to `(\overline{w_b}/|w_b|) w`, a point of the ray of `w`
whose `b`-th coordinate is positive (the source's `cor:column`, qualitative form). -/
theorem PhysicalPreparation.tendsto_column (P : PhysicalPreparation L κ hκ) (w : OneParticle) (hw : ‖w‖ = 1)
    (b : ℤ) (hb : w b ≠ 0) (hlim : HasRankOneLimit (fun q => P.gammaOp q) w) :
    Tendsto (fun q => normalizedColumn (P.gammaOp q) b) atTop
      (𝓝 ((conj (w b) / ((‖w b‖ : ℝ) : ℂ)) • w)) :=
  tendsto_normalizedColumn (fun q => P.gammaOp q) w hw b hb hlim

end Physical

end QuantumNLS.PhysicalAuxiliaryDensity

#print axioms QuantumNLS.PhysicalAuxiliaryDensity.column_anchor_nonneg
#print axioms QuantumNLS.PhysicalAuxiliaryDensity.anchorRepresentative_self
#print axioms QuantumNLS.PhysicalAuxiliaryDensity.normalizedColumn_rankOne
#print axioms QuantumNLS.PhysicalAuxiliaryDensity.tendsto_normalizedColumn
#print axioms QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.gammaOp_isAuxiliaryOperator
#print axioms QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.auxiliary_operator
#print axioms QuantumNLS.PhysicalAuxiliaryDensity.PhysicalPreparation.tendsto_column
