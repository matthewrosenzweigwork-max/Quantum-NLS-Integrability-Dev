import NlsGge.Atomic.G1.G1104Host
import NlsGge.GK38.GradFundamentalODE
import NlsGge.GK38.NeumannChar

/-!
# G1-104 supporting module G1104ODE

* M1: for every `φ : PotPair` and `z`, each entry of the fundamental matrix `fundPair φ z`
  (extended from `[0,1]` by `Set.IccExtend`) is absolutely continuous on `[0,1]` and satisfies
  the ZS coefficient ODE `M' = zsCoeffPot38 φ z · M` almost everywhere.
* M3: the 2x2 characteristic matrix `charMatrix bc M = B0 bc + B1 bc * M` of a boundary
  condition, its literal vector relation `bcRelation`, and `det (charMatrix bc (M(1,z))) =
  k_bc * boundaryCharacteristic φ bc z` with `k_bc ≠ 0` (`-2i, -2i, -1, 1`).
-/

set_option autoImplicit false

open NlsGge.Atomic.Interval
open NlsGge.Pilot NlsGge.GK38 MeasureTheory Set
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1104ODE
noncomputable section

/-! ### M1 -/

theorem fundPair_ac (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z) t i j) 0 1 :=
  ac_fundContP_entry38 φ z i j

theorem fundPair_ae_hasDerivAt (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivAt
        (fun r : ℝ => Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z) r i j)
        ((zsCoeffPot38 φ z s *
          Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z) s) i j) s :=
  ae_hasDerivAt_fundContP_entry38 φ z i j

/-- Both halves of M1. -/
theorem fundPair_ac_and_ae_ode (φ : PotPair) (z : ℂ) :
    ∀ i j : Fin 2,
      AbsolutelyContinuousOnInterval
        (fun t : ℝ => Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z) t i j) 0 1 ∧
      ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        HasDerivAt
          (fun r : ℝ => Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z) r i j)
          ((zsCoeffPot38 φ z s *
            Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) (fundPair φ z) s) i j) s :=
  fun i j => ⟨fundPair_ac φ z i j, fundPair_ae_hasDerivAt φ z i j⟩

/-! ### M3 -/

/-- Rows of the boundary relation `B0 c + B1 (M c) = 0` at the left endpoint. -/
def charB0 : ZSBoundaryCondition → Matrix (Fin 2) (Fin 2) ℂ
  | .dirichlet => !![1, -1; 0, 0]
  | .neumann => !![1, 1; 0, 0]
  | .periodic => !![-1, 0; 0, -1]
  | .antiperiodic => !![1, 0; 0, 1]

/-- Rows of the boundary relation at the right endpoint. -/
def charB1 : ZSBoundaryCondition → Matrix (Fin 2) (Fin 2) ℂ
  | .dirichlet => !![0, 0; 1, -1]
  | .neumann => !![0, 0; 1, 1]
  | .periodic => !![1, 0; 0, 1]
  | .antiperiodic => !![1, 0; 0, 1]

/-- The characteristic matrix `D_bc = B0 + B1 M`. -/
def charMatrix (bc : ZSBoundaryCondition) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  charB0 bc + charB1 bc * M

/-- Literal endpoint relation for initial value `c` and final value `w` (component 0 and 1
of a pair), mirroring `HasZSBoundaryCondition`. -/
def bcRelation (bc : ZSBoundaryCondition) (c w : Fin 2 → ℂ) : Prop :=
  match bc with
  | .dirichlet => c 0 = c 1 ∧ w 0 = w 1
  | .neumann => c 0 = -c 1 ∧ w 0 = -w 1
  | .periodic => ∀ b : Fin 2, w b = c b
  | .antiperiodic => ∀ b : Fin 2, w b = -c b

theorem bcRelation_iff_charB (bc : ZSBoundaryCondition) (c w : Fin 2 → ℂ) :
    bcRelation bc c w ↔ (charB0 bc).mulVec c + (charB1 bc).mulVec w = 0 := by
  have key : ∀ r : Fin 2 → ℂ, r = 0 ↔ r 0 = 0 ∧ r 1 = 0 := by
    intro r
    constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1⟩
      funext i; fin_cases i <;> simpa
  rw [key]
  cases bc <;>
    simp [bcRelation, charB0, charB1, dotProduct, Fin.sum_univ_two,
      Fin.forall_fin_two] <;>
    constructor <;> rintro ⟨h0, h1⟩ <;> refine ⟨?_, ?_⟩ <;>
    first
      | linear_combination h0 | linear_combination -h0 | linear_combination h1

theorem bcRelation_iff_charMatrix (bc : ZSBoundaryCondition) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (c : Fin 2 → ℂ) :
    bcRelation bc c (M.mulVec c) ↔ (charMatrix bc M).mulVec c = 0 := by
  rw [bcRelation_iff_charB, charMatrix, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem det_charMatrix_dirichlet (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (charMatrix .dirichlet M).det =
      M 0 0 + M 0 1 - M 1 0 - M 1 1 := by
  rw [Matrix.det_fin_two]
  simp only [charMatrix, charB0, charB1, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem det_charMatrix_neumann (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (charMatrix .neumann M).det =
      M 0 1 + M 1 1 - M 0 0 - M 1 0 := by
  rw [Matrix.det_fin_two]
  simp only [charMatrix, charB0, charB1, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem det_charMatrix_periodic (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (charMatrix .periodic M).det = M.det - M.trace + 1 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two M]
  simp only [charMatrix, charB0, charB1, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.trace_fin_two]
  ring

theorem det_charMatrix_antiperiodic (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (charMatrix .antiperiodic M).det = M.det + M.trace + 1 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two M]
  simp only [charMatrix, charB0, charB1, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.trace_fin_two]
  ring

/-- The nonzero constant relating `det D_bc` to `boundaryCharacteristic`. -/
def charConstant : ZSBoundaryCondition → ℂ
  | .dirichlet => -(2 * Complex.I)
  | .neumann => -(2 * Complex.I)
  | .periodic => -1
  | .antiperiodic => 1

theorem charConstant_ne_zero (bc : ZSBoundaryCondition) : charConstant bc ≠ 0 := by
  cases bc <;> simp [charConstant, Complex.I_ne_zero]

theorem det_charMatrix_monodromy (φ : PotPair) (bc : ZSBoundaryCondition) (z : ℂ) :
    (charMatrix bc (monodromyPair φ z)).det =
      charConstant bc * boundaryCharacteristic φ bc z := by
  have h2I : (2 * Complex.I : ℂ) ≠ 0 := dirichlet_denominator_ne_zero38
  cases bc
  · rw [det_charMatrix_dirichlet]
    simp only [charConstant, boundaryCharacteristic, dirichletChar_eq]
    field_simp
    ring
  · rw [det_charMatrix_neumann]
    simp only [charConstant, boundaryCharacteristic, gkNeumannCharacteristic, neumannChar38_eq]
    field_simp
    ring
  · rw [det_charMatrix_periodic, det_monodromyPair]
    simp only [charConstant, boundaryCharacteristic, GK38.discrim]
    ring
  · rw [det_charMatrix_antiperiodic, det_monodromyPair]
    simp only [charConstant, boundaryCharacteristic, GK38.discrim]
    ring

/-- M3: `det D_bc(z) = k * boundaryCharacteristic φ bc z` with a nonzero constant `k`. -/
theorem det_charMatrix_eq_const_mul (bc : ZSBoundaryCondition) :
    ∃ k : ℂ, k ≠ 0 ∧ ∀ (φ : PotPair) (z : ℂ),
      (charMatrix bc (fundPair φ z ⟨1, by norm_num, le_rfl⟩)).det =
        k * boundaryCharacteristic φ bc z :=
  ⟨charConstant bc, charConstant_ne_zero bc, fun φ z => by
    rw [← monodromyPair_eq_fundPair]; exact det_charMatrix_monodromy φ bc z⟩

end
end NlsGge.Atomic.G1104ODE
