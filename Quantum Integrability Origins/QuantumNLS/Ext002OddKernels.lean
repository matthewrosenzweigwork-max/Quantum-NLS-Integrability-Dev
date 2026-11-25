import QuantumNLS.BetheTransferKernelAdjoint

/-! Source-faithful scalar kernels for Vlaar (2.4.2)-(2.4.3).
The creator variables `x` outnumber the annihilator variables `y` by one.
This file proves scalar ordering and phase identities only: no fixed-sector
field operator, Fock-space domain, or off-diagonal transfer identification
is postulated or claimed. -/
noncomputable section
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
namespace QuantumNLS.Ext002OddKernels
open BetheTransferKernelAdjoint

/-- The strict chamber `L > x₁ > y₁ > ... > yᵣ > xᵣ₊₁ > 0`.
The empty even block is admitted when `r = 0`. -/
def oddOrder {r : ℕ} (L : ℝ) (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) : Prop :=
  PlusOrder L (fun i => x i.castSucc) y ∧
    0 < x (Fin.last r) ∧ x (Fin.last r) < L ∧
    ∀ i : Fin r, x i.succ < y i

/-- The signed sum of odd and even variables of Vlaar's odd ordered tuple. -/
def oddDisplacement {r : ℕ} (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, x i - ∑ i, y i

/-- Source B phase after translating the interval to `(0,L)` and applying
`exp(i z L/2)` to the source monodromy. -/
def creationKernel {r : ℕ} (L : ℝ) (z : ℂ)
    (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) : ℂ := by
  classical
  exact if oddOrder L x y then Complex.exp (Complex.I * z * oddDisplacement x y) else 0

/-- Source C phase in the same gauge; its first argument is the r-tuple of
creation coordinates and its second is the (r+1)-tuple of annihilation coordinates. -/
def annihilationKernel {r : ℕ} (L : ℝ) (z : ℂ)
    (x : Fin r → ℝ) (y : Fin (r+1) → ℝ) : ℂ := by
  classical
  exact if oddOrder L y x then Complex.exp (Complex.I * z * (L - oddDisplacement y x)) else 0

/-- Translating every odd and even variable by `L/2` changes the odd sum
by `L/2`, because there is one extra odd variable. -/
theorem oddDisplacement_center {r : ℕ} (L : ℝ)
    (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) :
    oddDisplacement (fun i => x i - L/2) (fun i => y i - L/2) =
      oddDisplacement x y - L/2 := by
  simp only [oddDisplacement, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The scalar translation and transfer gauge for the source B entry. -/
theorem creation_phase_translation {r : ℕ} (L : ℝ) (z : ℂ)
    (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) :
    Complex.exp (Complex.I * z * L / 2) *
      Complex.exp (Complex.I * z *
        oddDisplacement (fun i => x i - L/2) (fun i => y i - L/2)) =
      Complex.exp (Complex.I * z * oddDisplacement x y) := by
  rw [oddDisplacement_center, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The corresponding source C phase carries a full `exp(i z L)` after
translation and transfer gauge. -/
theorem annihilation_phase_translation {r : ℕ} (L : ℝ) (z : ℂ)
    (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) :
    Complex.exp (Complex.I * z * L / 2) *
      Complex.exp (-Complex.I * z *
        oddDisplacement (fun i => x i - L/2) (fun i => y i - L/2)) =
      Complex.exp (Complex.I * z * (L - oddDisplacement x y)) := by
  rw [oddDisplacement_center, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Off-diagonal kernel conjugation with the exact gauge phase. -/
theorem creationKernel_conj_swap {r : ℕ} (L : ℝ) (z : ℂ)
    (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) :
    conj (creationKernel L z x y) =
      adjointPhase L z * annihilationKernel L (conj z) y x := by
  classical
  unfold creationKernel annihilationKernel adjointPhase
  by_cases h : oddOrder L x y
  · simp only [ite_eq_left h, ← Complex.exp_conj, map_mul, Complex.conj_I,
      Complex.conj_ofReal, ← Complex.exp_add]
    congr 1
    ring
  · simp [h]

/-- Scalar source B integrand on the centered interval. The order test is
written by translating back to `(0,L)`, so it encodes the same strict simplex. -/
def sourceCreationKernel {r : ℕ} (L : ℝ) (z : ℂ)
    (u : Fin (r+1) → ℝ) (v : Fin r → ℝ) : ℂ := by
  classical
  exact if oddOrder L (fun i => u i + L/2) (fun i => v i + L/2) then
    Complex.exp (Complex.I * z * oddDisplacement u v) else 0

/-- Scalar source C integrand, centered, with annihilators in odd positions. -/
def sourceAnnihilationKernel {r : ℕ} (L : ℝ) (z : ℂ)
    (u : Fin r → ℝ) (v : Fin (r+1) → ℝ) : ℂ := by
  classical
  exact if oddOrder L (fun i => v i + L/2) (fun i => u i + L/2) then
    Complex.exp (-Complex.I * z * oddDisplacement v u) else 0

/-- Exact B scalar-kernel comparison, including the strict simplex indicator. -/
theorem sourceCreationKernel_gauge {r : ℕ} (L : ℝ) (z : ℂ)
    (x : Fin (r+1) → ℝ) (y : Fin r → ℝ) :
    Complex.exp (Complex.I * z * L/2) *
      sourceCreationKernel L z (fun i => x i - L/2) (fun i => y i - L/2) =
        creationKernel L z x y := by
  classical
  unfold sourceCreationKernel creationKernel
  simp only [sub_add_cancel]
  split_ifs with h
  · exact creation_phase_translation L z x y
  · simp

/-- Exact C scalar-kernel comparison, including the strict simplex indicator. -/
theorem sourceAnnihilationKernel_gauge {r : ℕ} (L : ℝ) (z : ℂ)
    (x : Fin r → ℝ) (y : Fin (r+1) → ℝ) :
    Complex.exp (Complex.I * z * L/2) *
      sourceAnnihilationKernel L z (fun i => x i - L/2) (fun i => y i - L/2) =
        annihilationKernel L z x y := by
  classical
  unfold sourceAnnihilationKernel annihilationKernel
  simp only [sub_add_cancel]
  split_ifs with h
  · exact annihilation_phase_translation L z y x
  · simp

/-- At zero pairs, the odd chamber is the open interval. -/
theorem oddOrder_zero (L : ℝ) (x : Fin 1 → ℝ) (y : Fin 0 → ℝ) :
    oddOrder L x y ↔ 0 < x 0 ∧ x 0 < L := by
  simp [oddOrder, PlusOrder]

end QuantumNLS.Ext002OddKernels
#print axioms QuantumNLS.Ext002OddKernels.oddDisplacement_center
#print axioms QuantumNLS.Ext002OddKernels.creation_phase_translation
#print axioms QuantumNLS.Ext002OddKernels.annihilation_phase_translation
#print axioms QuantumNLS.Ext002OddKernels.creationKernel_conj_swap
#print axioms QuantumNLS.Ext002OddKernels.sourceCreationKernel_gauge
#print axioms QuantumNLS.Ext002OddKernels.sourceAnnihilationKernel_gauge
#print axioms QuantumNLS.Ext002OddKernels.oddOrder_zero
