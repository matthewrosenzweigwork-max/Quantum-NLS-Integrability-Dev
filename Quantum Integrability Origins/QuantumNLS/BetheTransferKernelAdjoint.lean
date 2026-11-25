import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
Literal raw transfer kernels from periodic_basis.tex:316–325 and the
input/output conjugation calculation at 385–389 (R-99FDE9B6).

These are pointwise kernel identities. The bounded integral operators,
symmetric compression, physical placement sum and on-shell transfer
eigenvector formula are subsequent obligations, not premises hidden here.
-/
noncomputable section
open scoped BigOperators ComplexConjugate

namespace QuantumNLS.BetheTransferKernelAdjoint
variable {m : ℕ}

/-- The strict alternating chamber L>x₁>y₁>...>xₘ>yₘ>0.
For zero particles it is harmlessly empty of constraints. -/
def PlusOrder (L : ℝ) (x y : Fin m → ℝ) : Prop :=
  (∀ j, 0 < y j ∧ y j < x j ∧ x j < L) ∧ ∀ i j, i < j → x j < y i

/-- Exactly the opposite alternating chamber, by swapping the coordinates. -/
def MinusOrder (L : ℝ) (x y : Fin m → ℝ) : Prop := PlusOrder L y x

/-- Removing the first pair leaves the same alternating chamber below y₁.
This identifies the all-pairs encoding with the literal printed chain. -/
theorem plusOrder_cons (L : ℝ) (x y : Fin (m+1) → ℝ) :
    PlusOrder L x y ↔
      0 < y 0 ∧ y 0 < x 0 ∧ x 0 < L ∧ PlusOrder (y 0) (Fin.tail x) (Fin.tail y) := by
  constructor
  · rintro ⟨h, hord⟩
    refine ⟨(h 0).1, (h 0).2.1, (h 0).2.2, ?_, ?_⟩
    · intro j
      exact ⟨(h j.succ).1, (h j.succ).2.1, hord 0 j.succ (Fin.succ_pos j)⟩
    · intro i j hij
      exact hord i.succ j.succ (Fin.succ_lt_succ_iff.2 hij)
  · rintro ⟨hy, hyx, hxL, h, hord⟩
    constructor
    · intro j
      refine Fin.cases ⟨hy, hyx, hxL⟩ (fun j => ?_) j
      exact ⟨(h j).1, (h j).2.1, ((h j).2.2.trans hyx).trans hxL⟩
    · intro i j hij
      refine Fin.cases (fun j hj => ?_) (fun i j hj => ?_) i j hij
      · refine Fin.cases (fun hh => False.elim ((lt_irrefl _) hh))
          (fun j _ => (h j).2.2) j hj
      · refine Fin.cases (fun hh => False.elim (Fin.not_lt_zero _ hh))
          (fun j hh => hord i j (Fin.succ_lt_succ_iff.1 hh)) j hj

/-- The signed sum in both printed phases. -/
def displacement (x y : Fin m → ℝ) : ℝ := ∑ j, (x j - y j)

theorem displacement_swap (x y : Fin m → ℝ) :
    displacement y x = -displacement x y := by
  simp only [displacement, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

/-- Literal raw upper kernel, including its strict chamber indicator. -/
def rawPlus (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) : ℂ := by
  classical
  exact if PlusOrder L x y then Complex.exp (Complex.I * z * displacement x y) else 0

/-- Literal raw lower kernel, with its full interval-length phase. -/
def rawMinus (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) : ℂ := by
  classical
  exact if MinusOrder L x y then
    Complex.exp (Complex.I * z * L - Complex.I * z * (∑ j, (y j - x j) : ℝ)) else 0

/-- The scalar in the printed adjoint formula. -/
def adjointPhase (L : ℝ) (z : ℂ) : ℂ := Complex.exp (-Complex.I * L * conj z)

/-- Swapping input/output and conjugating the actual upper kernel gives
the lower kernel with exactly the printed phase. -/
theorem rawPlus_adjoint (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) :
    conj (rawPlus L z y x) = adjointPhase L z * rawMinus L (conj z) x y := by
  classical
  unfold rawPlus rawMinus MinusOrder adjointPhase
  by_cases h : PlusOrder L y x
  · simp only [ite_eq_left h, ← Complex.exp_conj, map_mul, Complex.conj_I,
      Complex.conj_ofReal, ← Complex.exp_add]
    congr 1
    simp only [displacement, Complex.ofReal_sum, Complex.ofReal_sub]
    ring_nf
  · simp only [ite_eq_right h, map_zero, mul_zero]

/-- The other half of the source adjoint calculation. -/
theorem rawMinus_adjoint (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) :
    conj (rawMinus L z y x) = adjointPhase L z * rawPlus L (conj z) x y := by
  classical
  unfold rawPlus rawMinus MinusOrder adjointPhase
  by_cases h : PlusOrder L x y
  · simp only [ite_eq_left h, ← Complex.exp_conj, map_sub, map_mul, Complex.conj_I,
      Complex.conj_ofReal, ← Complex.exp_add]
    congr 1
    simp only [displacement, Complex.ofReal_sum, Complex.ofReal_sub]
    ring_nf
  · simp only [ite_eq_right h, map_zero, mul_zero]

/-- The uncompressed sum is the kernel used before Pₘ compression. -/
def rawKernel (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) : ℂ :=
  rawPlus L z x y + rawMinus L z x y

theorem rawKernel_adjoint (L : ℝ) (z : ℂ) (x y : Fin m → ℝ) :
    conj (rawKernel L z y x) = adjointPhase L z * rawKernel L (conj z) x y := by
  simp only [rawKernel, map_add, rawPlus_adjoint, rawMinus_adjoint]
  ring_nf

/-- Literal scalar gauge for the real-parameter self-adjoint kernel. -/
def realKernel (L a : ℝ) (x y : Fin m → ℝ) : ℂ :=
  Complex.exp (-Complex.I * L * a / 2) * rawKernel L a x y

theorem realKernel_conj_swap (L a : ℝ) (x y : Fin m → ℝ) :
    conj (realKernel L a y x) = realKernel L a x y := by
  simp only [realKernel, map_mul, rawKernel_adjoint, Complex.conj_ofReal,
    ← Complex.exp_conj, map_div₀, map_neg, Complex.conj_I, map_mul,
    map_ofNat, adjointPhase]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

end QuantumNLS.BetheTransferKernelAdjoint

#print axioms QuantumNLS.BetheTransferKernelAdjoint.PlusOrder
#print axioms QuantumNLS.BetheTransferKernelAdjoint.MinusOrder
#print axioms QuantumNLS.BetheTransferKernelAdjoint.plusOrder_cons
#print axioms QuantumNLS.BetheTransferKernelAdjoint.displacement
#print axioms QuantumNLS.BetheTransferKernelAdjoint.displacement_swap
#print axioms QuantumNLS.BetheTransferKernelAdjoint.rawPlus
#print axioms QuantumNLS.BetheTransferKernelAdjoint.rawMinus
#print axioms QuantumNLS.BetheTransferKernelAdjoint.adjointPhase
#print axioms QuantumNLS.BetheTransferKernelAdjoint.rawPlus_adjoint
#print axioms QuantumNLS.BetheTransferKernelAdjoint.rawMinus_adjoint
#print axioms QuantumNLS.BetheTransferKernelAdjoint.rawKernel
#print axioms QuantumNLS.BetheTransferKernelAdjoint.rawKernel_adjoint
#print axioms QuantumNLS.BetheTransferKernelAdjoint.realKernel
#print axioms QuantumNLS.BetheTransferKernelAdjoint.realKernel_conj_swap

/- Both source branches and the literal alternating chamber are required. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheTransferKernelAdjoint.realKernel_conj_swap,
    ``QuantumNLS.BetheTransferKernelAdjoint.plusOrder_cons]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus_adjoint,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus_adjoint,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawKernel_adjoint,
      ``QuantumNLS.BetheTransferKernelAdjoint.adjointPhase,
      ``QuantumNLS.BetheTransferKernelAdjoint.PlusOrder] do
    unless seen.contains n do
      throwError "Raw transfer route missed literal source ingredient: {n}"
  Lean.logInfo m!"Raw-transfer route PASS: {seen.size} transitive constants; literal alternating chamber, both ordered kernels, full interval phase, conjugate-swap identities and real half-phase gauge reached. Pointwise result only."
