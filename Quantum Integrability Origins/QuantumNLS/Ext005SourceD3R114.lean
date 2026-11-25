import QuantumNLS.Ext005SourceHypothesesR114
import QuantumNLS.Ext005OperatorD3R113

/-! One named EXT-005 uniqueness theorem in the owner D3 class. The
Hamiltonian is supplied algebraically; its bounded representation is proved
from the source inequalities. Competitors carry all three D3 conditions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005SourceD3R114
open Ext005OperatorFormR113 Ext005SourceHypothesesR114
open Ext005HilbertEnergyR112 Ext005AntidualWeakR113 Ext005OperatorD3R113
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- Source-native D3 wording: norm continuity, local essential Q(A) bound,
and the scalar weak equation for the actual algebraic H(t) coefficients. -/
def D3Solution (A : PositiveOperator H) (S : SourceHypotheses A) (x : ℝ → H) : Prop :=
  letI : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let i := (inclusion A).restrictScalars ℝ
  ContinuousOn x (Ico 0 1) ∧
    (∀ T ∈ Ioo (0 : ℝ) 1, EnergyBounded i (Icc 0 T) x) ∧
    ∀ (v : FormDomain A) (p : ℝ → ℝ), ContDiff ℝ ∞ p → HasCompactSupport p →
      tsupport p ⊆ Ioo (0 : ℝ) 1 →
      ∫ t, deriv p t * (⟪inclusion A v, x t⟫_ℂ).re =
        -(∫ t, p t * (S.hamiltonian t (lift i (x t)) v).im)

lemma D3Solution.energyWeak (A : PositiveOperator H) (S : SourceHypotheses A)
    (x : ℝ → H) (hx : D3Solution A S x) :
    EnergyWeakSolution A (sourceForm A S) x := by
  let : InnerProductSpace ℝ (FormDomain A) := InnerProductSpace.rclikeToReal ℂ (FormDomain A)
  let i := (inclusion A).restrictScalars ℝ
  rcases hx with ⟨hc, he, hw⟩
  refine ⟨hc, he, ?_⟩
  intro v p hp hcp hsup
  have hR : (fun t => p t * (((-Complex.I) • sourceForm A S t (lift i (x t))) v).re) =
      (fun t => p t * (S.hamiltonian t (lift i (x t)) v).im) := by
    funext t
    by_cases ht : t ∈ Ico (0 : ℝ) 1
    · change p t * ((-Complex.I) * sourceForm A S t (lift i (x t)) v).re = _
      rw [sourceForm_apply A S t ht]
      simp [Complex.mul_re]
    · have hpt : p t = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        ht ⟨(hsup h).1.le, (hsup h).2⟩)
      simp only [hpt, zero_mul]
  rw [hR]
  simpa only [ambient_apply] using hw v p hp hcp hsup

/-- EXT-005/D3 uniqueness on [0,1), from the source A,B,H(t) form
hypotheses. Every competitor must prove its own essential energy bounds. -/
theorem EXT005_D3_unique (A : PositiveOperator H) (S : SourceHypotheses A)
    (x y : ℝ → H) (hx : D3Solution A S x) (hy : D3Solution A S y)
    (hinit : x 0 = y 0) : ∀ t ∈ Ico (0 : ℝ) 1, x t = y t := by
  exact EXT005_D3_continuous_form_unique A (sourceForm A S) S.diagonalDerivative S.C
    S.constant_pos.le (sourceForm_symmetric A S) (sourceForm_derivative A S)
    S.derivative_bound x y (D3Solution.energyWeak A S x hx)
    (D3Solution.energyWeak A S y hy) hinit

end QuantumNLS.Ext005SourceD3R114
#print axioms QuantumNLS.Ext005SourceD3R114.EXT005_D3_unique

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SourceD3R114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SourceD3R114." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R114 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
