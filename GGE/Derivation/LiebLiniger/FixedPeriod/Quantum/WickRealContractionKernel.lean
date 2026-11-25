import LiebLiniger.FixedPeriod.Quantum.WickHigherWirtinger

/-!
# Source-facing actual real derivative contraction kernel

The real derivative contraction is defined from independently constructed input
functional and output Riesz vector, without mentioning a target kernel. The
joint theorem characterizes both by literal iterated real extraction on every
mixed elementary free tensor and identifies their pairing with the source
three-block tensor composition and exact falling factorials. Natural degree
coverage retains every j ≤ min(p_b,q_c), including j=0 and vacuum degrees.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Explicit zero-order equation for the actual real input recursion. -/
@[simp] theorem wickIteratedRealWirtingerInput_zero (f : Lp ℂ 2 μ → ℂ)
    (h : Fin 0 → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerInput μ f 0 h = f := rfl

/-- Explicit successor equation: the next operator is the actual real extraction. -/
theorem wickIteratedRealWirtingerInput_succ (f : Lp ℂ 2 μ → ℂ)
    (j : ℕ) (h : Fin (j + 1) → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerInput μ f (j + 1) h =
      wickRealWirtingerInput μ (wickIteratedRealWirtingerInput μ f j (Fin.tail h)) (h 0) := rfl

/-- Explicit zero-order equation for the actual real output recursion. -/
@[simp] theorem wickIteratedRealWirtingerOutput_zero (f : Lp ℂ 2 μ → ℂ)
    (h : Fin 0 → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerOutput μ f 0 h = f := rfl

/-- Explicit output successor equation, with the actual plus-i extraction. -/
theorem wickIteratedRealWirtingerOutput_succ (f : Lp ℂ 2 μ → ℂ)
    (j : ℕ) (h : Fin (j + 1) → Lp ℂ 2 μ) :
    wickIteratedRealWirtingerOutput μ f (j + 1) h =
      wickRealWirtingerOutput μ (wickIteratedRealWirtingerOutput μ f j (Fin.tail h)) (h 0) := rfl

/-- The r+j/j+s parameterization covers exactly every source-admissible order,
without deleting zero degrees or adding a coefficient assumption. -/
theorem contractionDegrees_coverage (pb qc j : ℕ) :
    j ≤ min pb qc ↔ ∃ r s : ℕ, pb = r + j ∧ qc = j + s := by
  constructor
  · intro hj
    refine ⟨pb - j, qc - j, ?_, ?_⟩ <;> omega
  · rintro ⟨r, s, hpb, hqc⟩
    omega

variable [IsFiniteMeasure μ]

/-- The physical real derivative contraction, defined through derivative-slot
extensions before any tensor kernel representation is asserted. -/
def wickRealDerivativeContraction {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (u : Lp ℂ 2 μ) : ℂ :=
  wickInputDerivativeFunctional μ A1 u u (wickOutputDerivativeVector μ A2 u u)

/-- Exact source kernel representation of the actual derivative-slot pairing.
The target uses the same concrete kernels, without an assumed derivative identity. -/
theorem wickRealDerivativeContraction_kernel {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (u : Lp ℂ 2 μ) :
    wickRealDerivativeContraction μ A1 A2 u =
      wickKernelPolynomial μ (tensorDerivativeContraction μ A1 A2) u := by
  exact wickDerivativeDot_eq_tensorKernel μ A1 A2 u u

/-- Q2-025 assembled: the independent extensions are characterized by actual
real extractions on every free elementary family, and their scalar contraction
is represented by precisely the source symmetrized tensor composition. -/
theorem wickRealDerivativeContraction_source {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (u : Lp ℂ 2 μ) :
    (∀ h : Fin j → Lp ℂ 2 μ,
      wickIteratedRealWirtingerInput μ (wickKernelPolynomial μ A1) j h u =
        wickInputDerivativeFunctional μ A1 u u (mixedTensorL2 μ h)) ∧
    (∀ h : Fin j → Lp ℂ 2 μ,
      wickIteratedRealWirtingerOutput μ (wickKernelPolynomial μ A2) j h u =
        conj (inner ℂ (wickOutputDerivativeVector μ A2 u u) (mixedTensorL2 μ h))) ∧
    wickRealDerivativeContraction μ A1 A2 u =
      wickKernelPolynomial μ
        (((((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ) : ℝ) : ℂ) •
          unscaledTensorContraction μ A1 A2) u := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact (wickInputDerivativeFunctional_real_mixed μ A1 u h).symm
  · intro h
    exact (wickOutputDerivativeVector_real_mixed μ A2 u h).symm
  · exact wickRealDerivativeContraction_kernel μ A1 A2 u

/-- Literal source degree consumer. The only index transports are the proved
natural equalities pb=r+j and qc=j+s; the real extractions retain the original
A1 and A2. Thus the assembled result covers every j≤min(pb,qc). -/
theorem wickRealDerivativeContraction_source_degrees {pb qb pc qc j : ℕ}
    (hj : j ≤ min pb qc)
    (A1 : SymmetricSector μ pb →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ qc)
    (u : Lp ℂ 2 μ) :
    ∃ (r s : ℕ) (hpb : pb = r + j) (hqc : qc = j + s),
      let B1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb := hpb ▸ A1
      let B2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s) := hqc ▸ A2
      (∀ h : Fin j → Lp ℂ 2 μ,
        wickIteratedRealWirtingerInput μ (wickKernelPolynomial μ A1) j h u =
          wickInputDerivativeFunctional μ B1 u u (mixedTensorL2 μ h)) ∧
      (∀ h : Fin j → Lp ℂ 2 μ,
        wickIteratedRealWirtingerOutput μ (wickKernelPolynomial μ A2) j h u =
          conj (inner ℂ (wickOutputDerivativeVector μ B2 u u) (mixedTensorL2 μ h))) ∧
      wickRealDerivativeContraction μ B1 B2 u =
        wickKernelPolynomial μ
          (((((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ) : ℝ) : ℂ) •
            unscaledTensorContraction μ B1 B2) u := by
  obtain ⟨r, s, hpb, hqc⟩ := (contractionDegrees_coverage pb qc j).mp hj
  subst pb
  subst qc
  exact ⟨r, s, rfl, rfl, wickRealDerivativeContraction_source μ A1 A2 u⟩

end LiebLiniger.FixedPeriod.Quantum
