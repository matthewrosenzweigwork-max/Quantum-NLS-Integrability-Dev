import QuantumNLS.TraceIdeal
import Mathlib.Topology.EMetricSpace.Basic

/-! The extended trace-norm metric on bounded operators is complete.
The underlying bounded operator remains available with its usual norm. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.TraceNormTopology
open TraceClass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded operators equipped below with extended trace distance. -/
@[ext] structure Op (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  val : H →L[ℂ] H

theorem traceNorm_neg (A : H →L[ℂ] H) : traceNorm (-A) = traceNorm A := by
  simpa using traceNorm_smul (-1 : ℂ) A

instance : EMetricSpace (Op H) where
  edist A B := traceNorm (A.val - B.val)
  edist_self A := by simp [traceNorm_eq_zero_iff]
  edist_comm A B := by rw [← neg_sub B.val A.val, traceNorm_neg]
  edist_triangle A B C := by
    calc
      _ = traceNorm ((A.val - B.val) + (B.val - C.val)) := by congr 1; abel
      _ ≤ _ := traceNorm_add_le _ _
  eq_of_edist_eq_zero := by
    intro A B h
    exact Op.ext (sub_eq_zero.mp ((traceNorm_eq_zero_iff _).mp h))

@[simp] theorem edist_eq (A B : Op H) : edist A B = traceNorm (A.val - B.val) := rfl

/-- Trace convergence implies operator norm convergence. -/
theorem forget_lipschitz : LipschitzWith 1 (Op.val : Op H → H →L[ℂ] H) := by
  intro A B
  simpa [edist_eq, edist_dist, dist_eq_norm, one_mul] using norm_le_traceNorm (A.val - B.val)

theorem continuous_val : Continuous (Op.val : Op H → H →L[ℂ] H) :=
  forget_lipschitz.continuous

/-- Trace norm sublevel sets are closed for operator norm convergence.
This is proved from finite dual tests, without assuming trace convergence. -/
theorem traceNorm_le_of_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {A : α → H →L[ℂ] H} {B : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (hA : Tendsto A l (𝓝 B))
    (hbound : ∀ᶠ i in l, traceNorm (A i) ≤ ENNReal.ofReal c) :
    traceNorm B ≤ ENNReal.ofReal c := by
  classical
  let b := refBasis H
  apply traceNorm_le_of_forall b
  intro X hX s
  have hlim : Tendsto (fun i => (∑ j ∈ s, ⟪X (b j), A i (b j)⟫_ℂ).re) l
      (𝓝 ((∑ j ∈ s, ⟪X (b j), B (b j)⟫_ℂ).re)) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.inner (((continuous_id.clm_apply continuous_const).tendsto B).comp hA)
  apply le_of_tendsto hlim
  filter_upwards [hbound] with i hi
  exact (Complex.re_le_norm _).trans ((norm_sum_inner_le_traceNorm b (A i) X hX
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi) s).trans
      (ENNReal.toReal_le_of_le_ofReal hc hi))

/-- The full extended trace metric is complete; different infinite-distance
components cause no problem for a Cauchy sequence. -/
instance : CompleteSpace (Op H) := by
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc : CauchySeq (fun n => (u n).val) := forget_lipschitz.uniformContinuous.comp_cauchySeq hu
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨⟨A⟩, EMetric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hδr : 0 < (δ : ℝ) := by exact_mod_cast hδ
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hu (ENNReal.ofReal (δ / 2))
    (ENNReal.ofReal_pos.mpr (half_pos hδr))
  refine ⟨N, fun n hn => ?_⟩
  have hb : traceNorm ((u n).val - A) ≤ ENNReal.ofReal (δ / 2) := by
    apply traceNorm_le_of_tendsto (half_pos hδr).le (tendsto_const_nhds.sub hA)
    exact eventually_atTop.2 ⟨N, fun m hm => (hN n hn m hm).le⟩
  exact hb.trans_lt (lt_trans ((ENNReal.ofReal_lt_ofReal_iff hδr).mpr (by linarith)) (by simpa using hδε))

/-- Trace norm itself is continuous for the extended trace metric. -/
theorem continuous_traceNorm : Continuous (fun A : Op H => traceNorm A.val) := by
  have h : (fun A : Op H => traceNorm A.val) = (fun A => edist A (⟨0⟩ : Op H)) := by
    funext A; simp
  rw [h]
  exact continuous_id.edist continuous_const

end QuantumNLS.TraceNormTopology

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.TraceNormTopology.Op
#print axioms QuantumNLS.TraceNormTopology.traceNorm_neg
#print axioms QuantumNLS.TraceNormTopology.edist_eq
#print axioms QuantumNLS.TraceNormTopology.forget_lipschitz
#print axioms QuantumNLS.TraceNormTopology.continuous_val
#print axioms QuantumNLS.TraceNormTopology.traceNorm_le_of_tendsto
#print axioms QuantumNLS.TraceNormTopology.continuous_traceNorm

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.TraceNormTopology." then
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
