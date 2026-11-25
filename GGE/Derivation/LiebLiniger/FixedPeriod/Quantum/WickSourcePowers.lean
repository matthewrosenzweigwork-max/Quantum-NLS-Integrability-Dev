import LiebLiniger.FixedPeriod.Quantum.WickPhysicalModeCommutation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Actual source-power prefix, bounded from original Source1 up to and including
sourceWickAnnihilationPower_pure. One proof-only repair at the actual e459:270
sector-index associativity diagnostic; source-only, uncompiled. -/
/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickSourceRankOneNormalOrder; 37e6fb8897fbc72f824e86eefe8f5ec1d7e2a1c02c2f047cd21b8378ce9a5592 -/
section Q2024Source1

/-! Direct source-Wick pure-rank-one normal ordering on complete sectors.
The scalar falling-factorial calculation reuses the written mathematical proof
in frozen WickGeometricPowers303ba, but the operators here are LITERALLY repeated
sourceWickAnnihilation, and their adjoints LITERALLY repeated sourceWickCreation.
No geometric-mode transport chain or operator-product formula is imported.
All p/q/k=0 cases are retained. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

/-- Exact scalar attached to p successive annihilations with k spectators. -/
def sourceWickPowerCoefficient (epsilon : ℝ) (k p : ℕ) : ℝ :=
  epsilon ^ ((p : ℝ) / 2) * Real.sqrt ((k + p).descFactorial p : ℝ)

@[simp] theorem sourceWickPowerCoefficient_zero (epsilon : ℝ) (k : ℕ) :
    sourceWickPowerCoefficient epsilon k 0 = 1 := by
  simp [sourceWickPowerCoefficient]

/-- The closed source coefficient obeys the literal source successor step. -/
theorem sourceWickPowerCoefficient_succ (epsilon : ℝ) (hε : 0 < epsilon) (k p : ℕ) :
    sourceWickPowerCoefficient epsilon k (p + 1) =
      sourceWickPowerCoefficient epsilon k p *
        (Real.sqrt epsilon * Real.sqrt (k + p + 1 : ℕ)) := by
  have hpow : epsilon ^ (((p + 1 : ℕ) : ℝ) / 2) =
      epsilon ^ ((p : ℝ) / 2) * Real.sqrt epsilon := by
    rw [show (((p + 1 : ℕ) : ℝ) / 2) = (p : ℝ) / 2 + 1 / 2 by push_cast; ring,
      Real.rpow_add hε, ← Real.sqrt_eq_rpow]
  unfold sourceWickPowerCoefficient
  rw [show k + (p + 1) = (k + p) + 1 by omega,
    Nat.succ_descFactorial_succ, Nat.cast_mul,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k + p + 1 : ℕ)), hpow]
  ring

/-- The product of the p/q source elementary coefficients is precisely the source
sector Wick coefficient, including p=0, q=0 and k=0. -/
theorem sourceWickPowerCoefficient_mul (epsilon : ℝ) (hε : 0 < epsilon) (k p q : ℕ) :
    sourceWickPowerCoefficient epsilon k p * sourceWickPowerCoefficient epsilon k q =
      LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) := by
  rw [LLFPSectorCandidate.wickCoefficient_eq_falling epsilon p q (p + k)
    (Nat.le_add_right p k)]
  have hout : p + k + q - p = k + q := by omega
  rw [hout]
  unfold sourceWickPowerCoefficient
  rw [Nat.add_comm p k]
  calc
    _ = (epsilon ^ ((p : ℝ) / 2) * epsilon ^ ((q : ℝ) / 2)) *
        (Real.sqrt ((k + p).descFactorial p : ℝ) *
          Real.sqrt ((k + q).descFactorial q : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hε, ← Real.sqrt_mul (by positivity)]
      congr 2
      ring

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Actual successive elementary source annihilations, with k final spectators. -/
def sourceWickAnnihilationPower (epsilon : ℝ) (g : Lp ℂ 2 μ) (k : ℕ) :
    (p : ℕ) → SymmetricSector μ (k + p) →L[ℂ] SymmetricSector μ k
  | 0 => ContinuousLinearMap.id ℂ _
  | p + 1 => (sourceWickAnnihilationPower epsilon g k p).comp
      (sourceWickAnnihilation μ epsilon g (k + p))

/-- Actual repeated source creation, as the adjoint of actual repeated source
annihilation. Its explicit recursion below binds every factor to source creation. -/
def sourceWickCreationPower (epsilon : ℝ) (h : Lp ℂ 2 μ) (k p : ℕ) :
    SymmetricSector μ k →L[ℂ] SymmetricSector μ (k + p) :=
  (sourceWickAnnihilationPower μ epsilon h k p).adjoint

@[simp] theorem sourceWickCreationPower_zero (epsilon : ℝ) (h : Lp ℂ 2 μ) (k : ℕ) :
    sourceWickCreationPower μ epsilon h k 0 = ContinuousLinearMap.id ℂ _ := by
  simp only [sourceWickCreationPower, sourceWickAnnihilationPower,
    ContinuousLinearMap.adjoint_id]
  rfl

/-- Literal recursion in ACTUAL source creation maps, not an occupation action. -/
theorem sourceWickCreationPower_succ (epsilon : ℝ) (h : Lp ℂ 2 μ) (k p : ℕ) :
    sourceWickCreationPower μ epsilon h k (p + 1) =
      (sourceWickCreation μ epsilon h (k + p)).comp
        (sourceWickCreationPower μ epsilon h k p) := by
  simp only [sourceWickCreationPower, sourceWickAnnihilationPower,
    ContinuousLinearMap.adjoint_comp]
  rw [← sourceWickCreation_eq_adjoint_annihilation μ epsilon h (k + p)]

/-- Actual repeated annihilation acts with precisely the source falling
factorial and epsilon coefficient, on every pure physical input. -/
theorem sourceWickAnnihilationPower_pure (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g u : Lp ℂ 2 μ) (k p : ℕ) :
    sourceWickAnnihilationPower μ epsilon g k p (pureSymmetricTensor μ (k + p) u) =
      ((sourceWickPowerCoefficient epsilon k p : ℂ) * inner ℂ g u ^ p) •
        pureSymmetricTensor μ k u := by
  induction p with
  | zero => simp [sourceWickAnnihilationPower]
  | succ p ih =>
    rw [sourceWickAnnihilationPower, ContinuousLinearMap.comp_apply]
    calc
      _ = sourceWickAnnihilationPower μ epsilon g k p
          (((sourceWickElementaryCoefficient epsilon (k + p) : ℂ) * inner ℂ g u) •
            pureSymmetricTensor μ (k + p) u) :=
        congrArg (fun x : SymmetricSector μ (k + p) =>
          sourceWickAnnihilationPower μ epsilon g k p x)
          (sourceWickAnnihilation_pure μ epsilon g u (k + p))
      _ = _ := by
        rw [map_smul, ih, smul_smul,
          sourceWickPowerCoefficient_succ epsilon hepsilon, Complex.ofReal_mul,
          sourceWickElementaryCoefficient, Complex.ofReal_mul, pow_succ]
        apply congrArg (fun c : ℂ => c • pureSymmetricTensor μ k u)
        ring

end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source1
