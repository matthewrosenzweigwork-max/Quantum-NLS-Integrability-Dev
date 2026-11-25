import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Batch 38, E07 base definitions (paper/v2.tex l.1870-1879, `D:sec:ALdefinition`).
Lattice `ZMod L` (`L = 2N+1 ≥ 5` in the source), coordinates `α j` in the open
unit disk, `r_j = |α_j|²`, transfer matrices
`A_j(z) = (1-r_j)^{-1/2} [[z, α_j], [conj α_j, z⁻¹]]`, monodromy
`M(z) = A_{L-1}(z) ⋯ A_0(z)`, discrete mass `M_d = -Σ_j log(1 - r_j)`.
Definitions only; no theorem is claimed in this file. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open scoped Matrix

/-- One AL transfer matrix `A(z) = (1-|a|²)^{-1/2} [[z, a], [conj a, z⁻¹]]`. -/
def alTransfer38 (a z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)⁻¹) • !![z, a; star a, z⁻¹]

/-- Partial products `M_0 = 1`, `M_{k+1} = A_k(z) M_k` (indices read in `ZMod L`). -/
def alPartial38 {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | k + 1 => alTransfer38 (α (k : ZMod L)) z * alPartial38 α z k

/-- The monodromy `M(z) = A_{L-1}(z) ⋯ A_0(z)`. -/
def alMonodromy38 {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  alPartial38 α z L

/-- Admissible lattice fields: every coordinate in the open unit disk. -/
def IsALField38 {L : ℕ} (α : ZMod L → ℂ) : Prop := ∀ j, ‖α j‖ < 1

/-- Discrete mass `M_d = -Σ_j log(1 - |α_j|²)`. -/
def alMass38 (L : ℕ) [NeZero L] (α : ZMod L → ℂ) : ℝ :=
  -∑ j : ZMod L, Real.log (1 - ‖α j‖ ^ 2)

/-- The `J`-form `F(v) = |v₀|² - |v₁|²`. -/
def alJForm38 (v : Fin 2 → ℂ) : ℝ := ‖v 0‖ ^ 2 - ‖v 1‖ ^ 2

end NlsGge.AblowitzLadik

end
