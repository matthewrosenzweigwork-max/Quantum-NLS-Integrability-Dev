import QuantumNLS.Ext006Blocks
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
FIN-CORE-BD-02, Fredholm determinant on the positive trace-class contraction
K* K. We use its standard trace-power definition
  det(1-T) = exp(-sum_{m>=1} Tr(T^m)/m).
The series is proved absolutely convergent in this domain. Its positivity and
positive fourth root are conclusions. No Fock norm identity is asserted here.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006FredholmTracePower
open TraceClass TraceCompact
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma traceNorm_power_bound (T : H →L[ℂ] H) (n : ℕ) :
    traceNorm (T^(n+1)) ≤ ENNReal.ofReal (‖T‖^n) * traceNorm T := by
  have hp : ‖T^n‖ ≤ ‖T‖^n := by
    cases n with
    | zero =>
      change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    | succ n => exact norm_pow_le' T (Nat.succ_pos n)
  rw [pow_succ]
  exact (traceNorm_mul_left_le (T^n) T).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) le_rfl)

lemma traceNorm_power_finite (T : H →L[ℂ] H) (hT : IsTraceClass T) (n : ℕ) :
    traceNorm (T^(n+1)) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.ne) (traceNorm_power_bound T n)

lemma trace_power_positive (T : H →L[ℂ] H) (hT : T.IsPositive) (n : ℕ) :
    (T^n).IsPositive := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  exact CStarAlgebra.pow_nonneg T n (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)

/-- Real trace-power coefficient. For positive T it is Tr(T^(n+1))/(n+1). -/
def tracePowerTerm (T : H →L[ℂ] H) (n : ℕ) : ℝ :=
  (traceNorm (T^(n+1))).toReal / (n+1 : ℕ)

lemma tracePowerTerm_nonneg (T : H →L[ℂ] H) (n : ℕ) : 0 ≤ tracePowerTerm T n := by
  unfold tracePowerTerm
  positivity

lemma tracePowerTerm_eq_posTrace (T : H →L[ℂ] H) (hT : T.IsPositive) (n : ℕ) :
    tracePowerTerm T n = (posTrace (T^(n+1))).toReal / (n+1 : ℕ) := by
  rw [tracePowerTerm, traceNorm_of_isPositive (trace_power_positive T hT (n+1))]

lemma tracePowerTerm_bound (T : H →L[ℂ] H) (hT : IsTraceClass T) (n : ℕ) :
    tracePowerTerm T n ≤ ‖T‖^n * (traceNorm T).toReal := by
  have hfin : ENNReal.ofReal (‖T‖^n) * traceNorm T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.ne
  have h := ENNReal.toReal_mono hfin (traceNorm_power_bound T n)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  exact (div_le_self ENNReal.toReal_nonneg hn).trans h

/-- Absolute convergence follows from the actual trace ideal bound and a
geometric majorant; no determinant or norm formula is a premise. -/
lemma tracePower_summable (T : H →L[ℂ] H) (hT : IsTraceClass T) (hn : ‖T‖ < 1) :
    Summable (tracePowerTerm T) := by
  apply Summable.of_nonneg_of_le (tracePowerTerm_nonneg T) (tracePowerTerm_bound T hT)
  exact (summable_geometric_of_lt_one (norm_nonneg T) hn).mul_right (traceNorm T).toReal

/-- The Fredholm determinant det(1-T), in its trace-power definition.
The supporting theorems use positive trace-class T of norm strictly below 1. -/
def fredholmDet (T : H →L[ℂ] H) : ℝ :=
  Real.exp (-(∑' n, tracePowerTerm T n))

lemma fredholmDet_pos (T : H →L[ℂ] H) : 0 < fredholmDet T := Real.exp_pos _

lemma fredholmDet_le_one (T : H →L[ℂ] H) : fredholmDet T ≤ 1 := by
  rw [fredholmDet, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (tsum_nonneg (tracePowerTerm_nonneg T))

/-- The positive normalization candidate, defined by the same convergent trace
series. Identifying it with the norm of a Fock vector remains a separate clause. -/
def fourthRoot (T : H →L[ℂ] H) : ℝ :=
  Real.exp (-(∑' n, tracePowerTerm T n)/4)

lemma fourthRoot_pos (T : H →L[ℂ] H) : 0 < fourthRoot T := Real.exp_pos _

lemma fourthRoot_pow_four (T : H →L[ℂ] H) : (fourthRoot T)^4 = fredholmDet T := by
  rw [fourthRoot, fredholmDet, ← Real.exp_nat_mul]
  congr 1
  ring

lemma fourthRoot_eq_rpow (T : H →L[ℂ] H) : fourthRoot T = (fredholmDet T)^(1/4 : ℝ) := by
  rw [fredholmDet, ← Real.exp_mul, fourthRoot]
  congr 1
  ring

lemma square_norm_lt_one (K : H →L[ℂ] H) (hK : ‖K‖ < 1) : ‖K.adjoint ∘L K‖ < 1 := by
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  nlinarith [norm_nonneg K]

/-- Fredholm determinant construction for every HS strict contraction K.
This proves convergence of the trace series, determinant positivity and the
exact positive fourth-root expression. It does not assert exponential-vector
convergence, its norm, or the number distribution. -/
theorem «FIN-CORE-BD-02-determinant-support» (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hHS : hsSq b K ≠ ⊤) (hK : ‖K‖ < 1) :
    IsTraceClass (K.adjoint ∘L K) ∧ Summable (tracePowerTerm (K.adjoint ∘L K)) ∧
      0 < fredholmDet (K.adjoint ∘L K) ∧
      0 < fourthRoot (K.adjoint ∘L K) ∧
      fourthRoot (K.adjoint ∘L K) = (fredholmDet (K.adjoint ∘L K))^(1/4 : ℝ) := by
  have ht := (Ext006Blocks.beta_adjoint_beta_traceClass b K hHS).1
  exact ⟨ht, tracePower_summable _ ht (square_norm_lt_one K hK), fredholmDet_pos _,
    fourthRoot_pos _, fourthRoot_eq_rpow _⟩

end QuantumNLS.Ext006FredholmTracePower

#print axioms QuantumNLS.Ext006FredholmTracePower.traceNorm_power_bound
#print axioms QuantumNLS.Ext006FredholmTracePower.traceNorm_power_finite
#print axioms QuantumNLS.Ext006FredholmTracePower.trace_power_positive
#print axioms QuantumNLS.Ext006FredholmTracePower.tracePowerTerm_nonneg
#print axioms QuantumNLS.Ext006FredholmTracePower.tracePowerTerm_eq_posTrace
#print axioms QuantumNLS.Ext006FredholmTracePower.tracePowerTerm_bound
#print axioms QuantumNLS.Ext006FredholmTracePower.tracePower_summable
#print axioms QuantumNLS.Ext006FredholmTracePower.fredholmDet_pos
#print axioms QuantumNLS.Ext006FredholmTracePower.fredholmDet_le_one
#print axioms QuantumNLS.Ext006FredholmTracePower.fourthRoot_pos
#print axioms QuantumNLS.Ext006FredholmTracePower.fourthRoot_pow_four
#print axioms QuantumNLS.Ext006FredholmTracePower.fourthRoot_eq_rpow
#print axioms QuantumNLS.Ext006FredholmTracePower.square_norm_lt_one
#print axioms QuantumNLS.Ext006FredholmTracePower.«FIN-CORE-BD-02-determinant-support»

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FredholmTracePower." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext006FredholmTracePower audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
