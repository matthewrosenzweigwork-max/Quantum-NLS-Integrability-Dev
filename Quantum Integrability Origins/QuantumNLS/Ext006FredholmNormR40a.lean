import QuantumNLS.Ext006ScalarNormR40a

/-! Exact Fredholm evaluation of the norm of the actual completed physical
pair-creation exponential, and its positive fourth-root normalization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006FredholmNormR40a
open Ext006KernelHilbertSchmidt
open TraceClass Ext006FredholmTracePower Ext006ScalarNormR40a
open Ext006PhysicalSeriesR39a Ext006PhysicalExponentialTerms
open Ext006PhysicalNormBridge.PairTensor Ext006PhysFockCoord Ext006CompressionR32a
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma actual_trace_summable (T : H →L[ℂ] H) (hT : IsTraceClass T) (hn : ‖T‖ < 1) :
    Summable (fun n : ℕ => (traceNorm (T^(n+1))).toReal/2) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (f := fun n : ℕ => ‖T‖^n * (traceNorm T).toReal/2)
  · intro n
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.ne) (traceNorm_power_bound T n)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hb
    linarith
  · exact ((summable_geometric_of_lt_one (norm_nonneg T) hn).mul_right
      (traceNorm T).toReal).div_const 2

lemma recurrence_weight_summable (c a : ℕ → ℝ) (hcs : Summable c) (has : Summable a)
    (hrec : ∀ n : ℕ, ((n:ℝ)+1)*c (n+1) = ∑ j ∈ Finset.range (n+1), a j*c (n-j)) :
    Summable (fun n : ℕ => (n:ℝ)*c n) := by
  have hs := (summable_norm_sum_mul_range_of_summable_norm has.norm hcs.norm).of_norm
  have ht : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)*c (n+1)) := by
    apply hs.congr
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using (hrec n).symm
  exact (summable_nat_add_iff 1).mp ht

variable {L : ℝ} [Fact (0 < L)]

/-- Evaluate the completed physical norm using the actual operator traces. -/
theorem physical_norm_sq_eq_exp (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    ‖physicalExponential K hSym hn hHS‖^2 =
      Real.exp ((∑' n, tracePowerTerm (K.adjoint ∘L K) n)/2) := by
  let c : ℕ → ℝ := fun n => ‖term (physicalPair (physicalBasis L) K hHS hSym) n‖^2
  let a : ℕ → ℝ := fun n => (traceNorm ((K.adjoint ∘L K)^(n+1))).toReal/2
  have hcs : Summable c := (all_degree_physical_norm_hasSum K hSym hn hHS).summable
  have has : Summable a := actual_trace_summable _
    (Ext006Blocks.beta_adjoint_beta_traceClass (physicalBasis L) K hHS).1 (square_norm_lt_one K hn)
  have hr : ∀ n : ℕ, ((n:ℝ)+1)*c (n+1) = ∑ j ∈ Finset.range (n+1), a j*c (n-j) := by
    intro n
    have h := Ext006ActualNormTraceR40a.actual_physical_trace_recurrence K hSym hHS (n+1)
    simp only [Nat.cast_add, Nat.cast_one] at h
    change 2*((n:ℝ)+1)*c (n+1) = ∑ j ∈ Finset.range (n+1), c (n-j)*(traceNorm ((K.adjoint ∘L K)^(j+1))).toReal at h
    calc
      _ = (2*((n:ℝ)+1)*c (n+1))/2 := by ring
      _ = _ := by
        rw [h, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [a]
        ring
  have h0 : c 0 = 1 := by
    dsimp only [c]
    rw [term_zero_norm]
    norm_num
  have he := total_eq_exp c a (fun n => sq_nonneg _) (fun n => by dsimp [a]; positivity)
    hcs has (recurrence_weight_summable c a hcs has hr) h0 hr
  rw [← (all_degree_physical_norm_hasSum K hSym hn hHS).tsum_eq]
  change (∑' n,c n) = _
  rw [he]
  congr 1
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  dsimp [a,tracePowerTerm]
  push_cast
  ring

/-- The actual squared norm is the inverse square root of det(1-K* K). -/
theorem physical_norm_sq_eq_det (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    ‖physicalExponential K hSym hn hHS‖^2 = (fredholmDet (K.adjoint ∘L K))^(-1/2:ℝ) := by
  rw [physical_norm_sq_eq_exp K hSym hn hHS,fredholmDet, ← Real.exp_mul]
  congr 1
  ring

/-- Strictly positive physical inverse norm is exactly the Fredholm fourth root. -/
theorem physical_inverse_norm_eq_fourthRoot
    (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    ‖physicalExponential K hSym hn hHS‖⁻¹ = fourthRoot (K.adjoint ∘L K) := by
  let t := ∑' n, tracePowerTerm (K.adjoint ∘L K) n
  have hn2 := physical_norm_sq_eq_exp K hSym hn hHS
  have he2 : (Real.exp (t/4))^2 = Real.exp (t/2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he : ‖physicalExponential K hSym hn hHS‖ = Real.exp (t/4) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
    exact hn2.trans he2.symm
  rw [he, ← Real.exp_neg, fourthRoot]
  congr 1
  dsimp [t]
  ring

/-- The normalized actual physical exponential has the exact det^(1/4) factor. -/
theorem physicalNormalized_eq_Fredholm
    (K : PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L)
    (hSym : ∀ i j, coordinates (physicalBasis L) K i j = coordinates (physicalBasis L) K j i)
    (hn : ‖K‖ < 1) (hHS : hsSq (physicalBasis L) K ≠ ⊤) :
    Ext006HSVacuumR32a.physicalNormalized K hSym hn hHS =
      (((fredholmDet (K.adjoint ∘L K))^(1/4:ℝ) : ℝ) : ℂ) • physicalExponential K hSym hn hHS := by
  rw [physicalNormalized_eq_exponential, ← Complex.ofReal_inv, physical_inverse_norm_eq_fourthRoot K hSym hn hHS, fourthRoot_eq_rpow]

end QuantumNLS.Ext006FredholmNormR40a
#print axioms QuantumNLS.Ext006FredholmNormR40a.physical_norm_sq_eq_det
#print axioms QuantumNLS.Ext006FredholmNormR40a.physical_inverse_norm_eq_fourthRoot
#print axioms QuantumNLS.Ext006FredholmNormR40a.physicalNormalized_eq_Fredholm

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FredholmNormR40a." then
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
  Lean.logInfo m!"Round40a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
