import QuantumNLS.TraceNormTopology
import QuantumNLS.EnergyMarginalTraceNets

/-! Compactness of the positive trace-one bounded kinetic-energy set
in the literal trace-norm topology, including closedness and completeness. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.EnergyMarginalCompactness
open Energy EnergyRealization TraceClass TraceNormTopology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positivity is closed for trace norm, as each quadratic form is continuous. -/
theorem isClosed_positive : IsClosed {A : Op H | A.val.IsPositive} := by
  have he : {A : Op H | A.val.IsPositive} =
      ⋂ x : H, {A : Op H |
        (((⟪A.val x, x⟫_ℂ).re : ℝ) : ℂ) = ⟪A.val x, x⟫_ℂ ∧
          0 ≤ (⟪A.val x, x⟫_ℂ).re} := by
    ext A; simp [ContinuousLinearMap.isPositive_iff_complex]
  rw [he]
  apply isClosed_iInter
  intro x
  have h : Continuous (fun A : Op H => ⟪A.val x, x⟫_ℂ) :=
    (continuous_val.clm_apply continuous_const).inner continuous_const
  exact (isClosed_eq (Complex.continuous_ofReal.comp (Complex.continuous_re.comp h)) h).inter
    (isClosed_le continuous_const (Complex.continuous_re.comp h))

variable (L : ℝ) [Fact (0 < L)] (k : ℕ)

/-- The source marginal set, on the full Fourier tensor carrier. -/
def states (E : ℝ) : Set (Op (L2 (Mom k))) :=
  {A | A.val.IsPositive ∧ posTrace A.val = 1 ∧ kinTrace L k A.val ≤ ENNReal.ofReal E}

omit [Fact (0 < L)] in
/-- The unbounded kinetic trace has closed sublevel sets. Each finite
diagonal sum is continuous; no continuity of the infinite sum is assumed. -/
theorem isClosed_energy (E : ℝ) :
    IsClosed {A : Op (L2 (Mom k)) | kinTrace L k A.val ≤ ENNReal.ofReal E} := by
  classical
  have he : {A : Op (L2 (Mom k)) | kinTrace L k A.val ≤ ENNReal.ofReal E} =
      ⋂ s : Finset (Mom k), {A : Op (L2 (Mom k)) |
        ∑ n ∈ s, ENNReal.ofReal (kinWeight L k n * (⟪ev n, A.val (ev n)⟫_ℂ).re)
          ≤ ENNReal.ofReal E} := by
    ext A
    simp only [mem_ofPred_eq, mem_iInter, kinTrace, ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
    rfl
  rw [he]
  apply isClosed_iInter
  intro s
  apply isClosed_le _ continuous_const
  apply continuous_finsetSum
  intro n _
  exact ENNReal.continuous_ofReal.comp (continuous_const.mul
    (Complex.continuous_re.comp (continuous_const.inner
      (continuous_val.clm_apply continuous_const))))

omit [Fact (0 < L)] in
/-- The trace-one condition is imposed on a closed positive set, where
positive trace equals trace norm and is therefore continuous. -/
theorem isClosed_states (E : ℝ) : IsClosed (states L k E) := by
  have he : states L k E = {A | A.val.IsPositive} ∩
      {A | traceNorm A.val = 1} ∩ {A | kinTrace L k A.val ≤ ENNReal.ofReal E} := by
    ext A
    simp only [states, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hp, ht, he⟩
      exact ⟨⟨hp, by rw [traceNorm_of_isPositive hp, ht]⟩, he⟩
    · rintro ⟨⟨hp, ht⟩, he⟩
      exact ⟨hp, by rwa [traceNorm_of_isPositive hp] at ht, he⟩
  rw [he]
  exact (isClosed_positive.inter (isClosed_eq continuous_traceNorm continuous_const)).inter
    (isClosed_energy L k E)

/-- The earlier actual Fourier compression nets give total boundedness
for this trace metric, without changing the set or its energy constraint. -/
theorem totallyBounded_states {E : ℝ} (hE : 0 ≤ E) : TotallyBounded (states L k E) := by
  classical
  apply EMetric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hδr : 0 < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨S, hS⟩ := EnergyMarginalTraceNets.finite_energy_trace_net L k hE (half_pos hδr)
  let t : Set (Op (L2 (Mom k))) := (fun C => (⟨C⟩ : Op (L2 (Mom k)))) '' (S : Set _)
  refine ⟨t, S.finite_toSet.image _, ?_⟩
  intro A hA
  obtain ⟨C, hCS, hC⟩ := hS A.val hA.1 hA.2.2
  apply mem_iUnion.2 ⟨⟨C⟩, ?_⟩
  apply mem_iUnion.2 ⟨mem_image_of_mem _ hCS, ?_⟩
  exact hC.trans_lt (lt_trans ((ENNReal.ofReal_lt_ofReal_iff hδr).mpr (by linarith)) (by simpa using hδε))

/-- Full trace-norm compactness of positive trace-one marginals with
additive kinetic trace at most E. -/
theorem isCompact_states {E : ℝ} (hE : 0 ≤ E) : IsCompact (states L k E) :=
  (totallyBounded_states L k hE).isCompact_of_isClosed (isClosed_states L k E)

end QuantumNLS.EnergyMarginalCompactness

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.EnergyMarginalCompactness.isClosed_positive
#print axioms QuantumNLS.EnergyMarginalCompactness.states
#print axioms QuantumNLS.EnergyMarginalCompactness.isClosed_energy
#print axioms QuantumNLS.EnergyMarginalCompactness.isClosed_states
#print axioms QuantumNLS.EnergyMarginalCompactness.totallyBounded_states
#print axioms QuantumNLS.EnergyMarginalCompactness.isCompact_states

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.EnergyMarginalCompactness." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
