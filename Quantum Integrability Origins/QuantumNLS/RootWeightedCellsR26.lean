import QuantumNLS.RootMassScaling
import QuantumNLS.Prop026Bound

/-! Spectral-cell realization for R-A8F7B7B0, `thm:root-weighted-masses`.
The rounded boundary phase specifies the printed cell index. No regular-cut
set or separation property is used in any declaration in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootWeightedCellsR26
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]

def cellIndex (hκ : 0 < κ) (u : L2T L) (x : ℝ) : ℤ :=
  ⌊RootIndexedPhase.theta hκ u x / Real.pi + 1/2⌋

def momentum (L : ℝ) (n : ℤ) : ℝ := 2*Real.pi*(n : ℝ)/L

def cellMomentum (hκ : 0 < κ) (u : L2T L) (x : ℝ) : ℝ :=
  momentum L (cellIndex hκ u x)

def displacement (hκ : 0 < κ) (u : L2T L) : ℝ :=
  ∫ x, (x-cellMomentum hκ u x)^2 ∂PhysicalQuantumMeasure.measure hκ u

theorem measurable_cellIndex (hκ : 0 < κ) (u : L2T L) :
    Measurable (cellIndex hκ u) :=
  (((RootIndexedPhase.root_indexed_phase hκ u).2.2.1.measurable.div_const _).add_const _).floor

theorem measurable_cellMomentum (hκ : 0 < κ) (u : L2T L) :
    Measurable (cellMomentum hκ u) := by
  exact (Measurable.of_discrete (f := momentum L)).comp (measurable_cellIndex hκ u)

theorem cellIndex_of_integer (hκ : 0 < κ) (u : L2T L) {x : ℝ} {n : ℤ}
    (hn : RootIndexedPhase.theta hκ u x = (n : ℝ)*Real.pi) :
    cellIndex hκ u x = n := by
  unfold cellIndex
  rw [hn, mul_div_cancel_right₀ _ Real.pi_ne_zero]
  exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩

theorem ae_integer_phase (hκ : 0 < κ) (u : L2T L) :
    ∀ᵐ x ∂PhysicalQuantumMeasure.measure hκ u,
      RootIndexedPhase.theta hκ u x = (cellIndex hκ u x : ℝ)*Real.pi := by
  by_cases hu : u = 0
  · subst u
    simp [PhysicalQuantumMeasure.measure_zero]
  · filter_upwards [Prop026Bound.integer_ae hκ hu] with x hx
    obtain ⟨n, hn⟩ := hx
    rw [Prop026Bound.label_eq] at hn
    have he : RootIndexedPhase.theta hκ u x = (n : ℝ)*Real.pi :=
      (div_eq_iff Real.pi_ne_zero).mp hn
    rw [cellIndex_of_integer hκ u he]
    exact he

theorem ae_displacement_boundary (hκ : 0 < κ) (u : L2T L) :
    ∀ᵐ x ∂PhysicalQuantumMeasure.measure hκ u,
      x-cellMomentum hκ u x = (2*κ/L)*Prop026Bound.reG hκ u x := by
  filter_upwards [ae_integer_phase hκ u] with x hx
  unfold cellMomentum momentum Prop026Bound.reG
  change x-2*Real.pi*(cellIndex hκ u x : ℝ)/L =
    (2*κ/L)*((L*x/2-RootIndexedPhase.theta hκ u x)/κ)
  rw [hx]
  field_simp [hκ.ne', (Fact.out : 0 < L).ne']

theorem ae_cell_fiber (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    ∀ᵐ x ∂PhysicalQuantumMeasure.measure hκ u,
      cellIndex hκ u x = n ↔ x ∈ Ioo
        (RootIndexedPhase.separator hκ u (n-1)) (RootIndexedPhase.separator hκ u n) := by
  filter_upwards [ae_integer_phase hκ u] with x hx
  rw [mem_Ioo,
    (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_lt_iff,
    (PhysicalSourceFinal.sourceFacts hκ u).phase.lt_separator_iff]
  change cellIndex hκ u x = n ↔
    (((n-1 : ℤ) : ℝ)+1/2)*Real.pi < RootIndexedPhase.theta hκ u x ∧
    RootIndexedPhase.theta hκ u x < ((n : ℝ)+1/2)*Real.pi
  rw [hx]
  push_cast
  constructor
  · intro he
    rw [he]
    constructor <;> nlinarith [Real.pi_pos]
  · rintro ⟨h1,h2⟩
    have hlt : n-1 < cellIndex hκ u x := by
      have he : ((n-1 : ℤ) : ℝ) < (cellIndex hκ u x : ℝ) := by
        push_cast
        nlinarith [Real.pi_pos]
      exact_mod_cast he
    have hgt : cellIndex hκ u x < n+1 := by
      have he : (cellIndex hκ u x : ℝ) < ((n+1 : ℤ) : ℝ) := by
        push_cast
        nlinarith [Real.pi_pos]
      exact_mod_cast he
    omega

theorem mass_eq_fiber (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    (RootIndexedMasses.masses hκ u).1 n =
      ((PhysicalQuantumMeasure.measure hκ u) (cellIndex hκ u ⁻¹' {n})).toReal := by
  rw [(RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).1 n]
  congr 1
  exact measure_congr ((ae_cell_fiber hκ u n).mono fun x hx => propext hx.symm)

theorem displacement_nonneg (hκ : 0 < κ) (u : L2T L) :
    0 ≤ displacement hκ u := integral_nonneg (fun _ => sq_nonneg _)

end QuantumNLS.RootWeightedCellsR26
