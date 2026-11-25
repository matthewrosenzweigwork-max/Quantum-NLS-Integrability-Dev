import QuantumNLS.Ext025B8BorelCalculus
import QuantumNLS.Ext025B7SpectralCompression

/-! GP-08, R-C17D95AA: the literal [1,M] square-root spectral truncation
and its M ||K|| bounded form compression, for an arbitrary PVM. Connection
to an unbounded physical Hamiltonian and the trace/form pairing remain
separate clauses, not premises asserting the desired application conclusion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B8EnergyCompression
open BetheChargeResolution Ext025B6PVM Ext025B8BorelCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

def rootSymbol (M : ℝ) (t : ℝ) : ℂ := (Set.Icc 1 M).indicator (fun u : ℝ => (Real.sqrt u : ℂ)) t

theorem rootSymbol_measurable (M : ℝ) : Measurable (rootSymbol M) :=
  (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).indicator measurableSet_Icc

theorem rootSymbol_bound (M : ℝ) (t : ℝ) : ‖rootSymbol M t‖ ≤ Real.sqrt M := by
  by_cases ht : t ∈ Set.Icc 1 M
  · simp only [rootSymbol,Set.indicator_of_mem ht,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t)]
    exact Real.sqrt_le_sqrt ht.2
  · simpa only [rootSymbol,Set.indicator_of_notMem ht,norm_zero] using Real.sqrt_nonneg M

theorem rootSymbol_square (M t : ℝ) :
    ‖rootSymbol M t‖^2 = (Set.Icc 1 M).indicator id t := by
  by_cases ht : t ∈ Set.Icc 1 M
  · simp only [rootSymbol,Set.indicator_of_mem ht,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t),id_eq]
    exact Real.sq_sqrt (zero_le_one.trans ht.1)
  · simp only [rootSymbol,Set.indicator_of_notMem ht,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]

/-- Constructed square-root cutoff, not a supplied bounded operator. -/
def rootCutoff (M : ℝ) : E →L[ℂ] E :=
  bounded P (rootSymbol M) (rootSymbol_measurable M) (Real.sqrt M) (Real.sqrt_nonneg M)
    (rootSymbol_bound M)

theorem rootCutoff_norm (M : ℝ) : ‖rootCutoff P M‖ ≤ Real.sqrt M :=
  bounded_norm P _ _ _ _ _

/-- The truncated scalar first moment is exactly the cutoff's squared norm. -/
theorem rootCutoff_square (M : ℝ) (x : E) :
    ‖rootCutoff P M x‖^2 = ∫ t, (Set.Icc 1 M).indicator id t ∂scalarMeasure P x := by
  change ‖vectorIntegral P (rootSymbol M) x _‖^2 = _
  rw [vectorIntegral_square]
  exact integral_congr_ae (.of_forall (rootSymbol_square M))

theorem rootCutoff_esquare (M : ℝ) (x : E) :
    ENNReal.ofReal (‖rootCutoff P M x‖^2) =
      ∫⁻ t, (Set.Icc 1 M).indicator (fun u => ENNReal.ofReal u) t ∂scalarMeasure P x := by
  change ENNReal.ofReal (‖vectorIntegral P (rootSymbol M) x _‖^2) = _
  rw [vectorIntegral_esquare]
  apply lintegral_congr
  intro t
  rw [rootSymbol_square]
  by_cases ht : t ∈ Set.Icc 1 M
  · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]
    rfl
  · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,ENNReal.ofReal_zero]

/-- The exact truncated-form operator norm used in R-C17D95AA. -/
theorem sandwich_norm (M : ℝ) (hM : 0 ≤ M) (K : E →L[ℂ] E) :
    ‖rootCutoff P M*K*rootCutoff P M‖ ≤ M*‖K‖ := by
  calc
    _ ≤ (‖rootCutoff P M‖*‖K‖)*‖rootCutoff P M‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Real.sqrt M*‖K‖)*Real.sqrt M :=
      mul_le_mul (mul_le_mul_of_nonneg_right (rootCutoff_norm P M) (norm_nonneg _))
        (rootCutoff_norm P M) (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ = (Real.sqrt M)^2*‖K‖ := by ring
    _ = M*‖K‖ := by rw [Real.sq_sqrt hM]

end QuantumNLS.Ext025B8EnergyCompression

#print axioms QuantumNLS.Ext025B8EnergyCompression.rootSymbol
#print axioms QuantumNLS.Ext025B8EnergyCompression.rootSymbol_measurable
#print axioms QuantumNLS.Ext025B8EnergyCompression.rootSymbol_bound
#print axioms QuantumNLS.Ext025B8EnergyCompression.rootSymbol_square
#print axioms QuantumNLS.Ext025B8EnergyCompression.rootCutoff
#print axioms QuantumNLS.Ext025B8EnergyCompression.rootCutoff_norm
#print axioms QuantumNLS.Ext025B8EnergyCompression.rootCutoff_square
#print axioms QuantumNLS.Ext025B8EnergyCompression.rootCutoff_esquare
#print axioms QuantumNLS.Ext025B8EnergyCompression.sandwich_norm

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B8EnergyCompression." then
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
  Lean.logInfo m!"Ext025B8EnergyCompression audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
