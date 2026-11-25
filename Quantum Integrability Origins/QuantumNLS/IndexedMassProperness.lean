import Mathlib
import QuantumNLS.IndexedMasses
import QuantumNLS.ActionTorus

/-!
# DEF-018: properness of the action map (definition only)

Source: `DEFINITIONS_LEDGER.md:379` (DEF-018), `chapters/definitions.tex`, `def:report-18`.  Ledger text: *the
indexed-mass map is proper if the inverse image of every compact subset of `ℓ¹_+(ℤ)` is compact in physical `L²`.
This concerns compact action sets, not bounded Hilbert balls.  A fibre is the inverse image of one action vector.*

## What is defined (definition only; properness is `thm:root-mass-properness` and is NOT proved here)
* `IndexedMassData L κ`: the parametric DEF-014 data realized in `IndexedMasses` (the measure `M_{κ,u}` itself and
  the strict monotonicity of `Re γ_u` are parameters there as well): finite measures `M u` on `ℝ` and selected
  boundary phases `P u : SelectedPhase L κ (M u)` for every `u ∈ L²(𝕋_L)`.
* `indexedMassMap D : L²(𝕋_L) → ℓ¹_+(ℤ)` (`PosL1`, DEF-019 module): `u ↦ (a_n(u))`, `a_n(u) = (P u).indexedMassReal
  (M u) n`; the `ℓ¹` membership is `summable_indexedMassReal` and nonnegativity is `toReal ≥ 0`.
* `IndexedMassProper D : Prop` := `∀ K ⊆ ℓ¹_+(ℤ)` compact, `indexedMassMap D ⁻¹' K` is compact in `L²`
  (norm topology of `Lp ℂ 2 volume`).
* `actionFibre D a := indexedMassMap D ⁻¹' {a}`.
* Basic lemmas: `indexedMassProper_iff` (definition unfolds as stated), `mem_actionFibre_iff` (a point of the fibre is
  `u` with `a_n(u) = a_n` for all `n`), `IndexedMassProper.isCompact_fibre` (proper ⇒ every fibre compact),
  `IndexedMassProper.isCompact_preimage_of_finite`, and `chartMasses_iff_mem_actionTorus_map` (the DEF-014 chart
  binding `|w_n|² = a_n(u)` is membership in the DEF-019 torus `T_{a(u)}`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace QuantumNLS.IndexedMassProperness

open QuantumNLS.IndexedMasses QuantumNLS.ActionTorus QuantumNLS.ResetNormalizationUniqueness

/-- The parametric DEF-014 data at fixed `L`, `κ`: for every physical `L²` datum `u`, the finite spectral measure
`M_{κ,u}` and the selected boundary phase `Re γ_u` (strictly monotone, as in `BoundaryPhase`). -/
structure IndexedMassData (L κ : ℝ) [Fact (0 < L)] where
  M : Lp ℂ 2 (volume : Measure (AddCircle L)) → Measure ℝ
  isFinite : ∀ u, IsFiniteMeasure (M u)
  P : ∀ u, SelectedPhase L κ (M u)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The indexed masses `a_n(u) = M_{κ,u}((b_{n−1}(u), b_n(u)))` as real numbers. -/
def IndexedMassData.seq (D : IndexedMassData L κ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) (n : ℤ) : ℝ :=
  (D.P u).toBoundaryPhase.indexedMassReal (D.M u) n

theorem IndexedMassData.summable_seq (D : IndexedMassData L κ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    Summable (D.seq u) := by
  have := D.isFinite u
  exact (D.P u).toBoundaryPhase.summable_indexedMassReal (D.M u)

theorem IndexedMassData.seq_nonneg (D : IndexedMassData L κ) (u : Lp ℂ 2 (volume : Measure (AddCircle L)))
    (n : ℤ) : 0 ≤ D.seq u n :=
  ENNReal.toReal_nonneg

/-- The indexed-mass sequence of `u` as an element of `ℓ¹_+(ℤ)`. -/
def IndexedMassData.map (D : IndexedMassData L κ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) : PosL1 :=
  ⟨⟨D.seq u, by
      refine memℓp_gen ?_
      have h1 : (1 : ℝ≥0∞).toReal = 1 := by norm_num
      have : (fun n : ℤ => ‖D.seq u n‖ ^ (1 : ℝ≥0∞).toReal) = D.seq u := by
        refine funext fun n => ?_
        rw [h1, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (D.seq_nonneg u n)]
      rw [this]
      exact D.summable_seq u⟩, D.seq_nonneg u⟩

@[simp] theorem IndexedMassData.map_apply (D : IndexedMassData L κ)
    (u : Lp ℂ 2 (volume : Measure (AddCircle L))) (n : ℤ) : (D.map u).1 n = D.seq u n := rfl

/-- **DEF-018.**  The indexed-mass map is proper: the inverse image of every compact subset of `ℓ¹_+(ℤ)` is
compact in physical `L²`.  (Definition only; this is the statement of `thm:root-mass-properness`.) -/
def IndexedMassProper (D : IndexedMassData L κ) : Prop :=
  ∀ K : Set PosL1, IsCompact K → IsCompact (D.map ⁻¹' K)

/-- The fibre over the action vector `a`: the inverse image of the single action vector. -/
def actionFibre (D : IndexedMassData L κ) (a : PosL1) : Set (Lp ℂ 2 (volume : Measure (AddCircle L))) :=
  D.map ⁻¹' {a}

theorem indexedMassProper_iff (D : IndexedMassData L κ) :
    IndexedMassProper D ↔ ∀ K : Set PosL1, IsCompact K → IsCompact (D.map ⁻¹' K) := Iff.rfl

theorem mem_actionFibre_iff (D : IndexedMassData L κ) (a : PosL1)
    (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    u ∈ actionFibre D a ↔ ∀ n, D.seq u n = a.1 n := by
  constructor
  · intro h n
    have h' : D.map u = a := h
    exact congrArg (fun b : PosL1 => b.1 n) h'
  · intro h
    show D.map u = a
    refine Subtype.ext (lp.ext (funext fun n => ?_))
    exact h n

theorem actionFibre_eq_preimage (D : IndexedMassData L κ) (a : PosL1) :
    actionFibre D a = D.map ⁻¹' {a} := rfl

theorem IndexedMassProper.isCompact_preimage {D : IndexedMassData L κ} (h : IndexedMassProper D)
    {K : Set PosL1} (hK : IsCompact K) : IsCompact (D.map ⁻¹' K) := h K hK

/-- **Proper ⇒ every fibre is compact.** -/
theorem IndexedMassProper.isCompact_fibre {D : IndexedMassData L κ} (h : IndexedMassProper D) (a : PosL1) :
    IsCompact (actionFibre D a) :=
  h {a} isCompact_singleton

theorem IndexedMassProper.isCompact_preimage_of_finite {D : IndexedMassData L κ} (h : IndexedMassProper D)
    {K : Set PosL1} (hK : K.Finite) : IsCompact (D.map ⁻¹' K) :=
  h K hK.isCompact

/-- The DEF-014 chart binding `|w_n(u)|² = a_n(u)` is membership of `Φ u` in the DEF-019 torus `T_{a(u)}`. -/
theorem chartMasses_iff_mem_actionTorus_map (D : IndexedMassData L κ)
    (Φ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ) :
    ChartMasses Φ (fun n u => D.seq u n) ↔ ∀ u, Φ u ∈ actionTorus (D.map u) :=
  chartMasses_iff_mem_actionTorus Φ D.map

end QuantumNLS.IndexedMassProperness

#print axioms QuantumNLS.IndexedMassProperness.IndexedMassData.map
#print axioms QuantumNLS.IndexedMassProperness.mem_actionFibre_iff
#print axioms QuantumNLS.IndexedMassProperness.IndexedMassProper.isCompact_fibre
#print axioms QuantumNLS.IndexedMassProperness.IndexedMassProper.isCompact_preimage_of_finite
#print axioms QuantumNLS.IndexedMassProperness.chartMasses_iff_mem_actionTorus_map
