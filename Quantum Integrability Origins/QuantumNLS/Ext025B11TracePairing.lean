import QuantumNLS.Ext025B10Bridges

/-! Complex trace pairing required for the physical compact-form passage.
The diagonal sum is proved absolutely summable for every trace-class input.
No self-adjointness of the observable is required. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025B11TracePairing
open TraceClass TraceIdeal TraceCompact
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Bounded sums over *all* finite subsets give unconditional real summability. -/
theorem real_summable {J : Type*} (f : J → ℝ) (c : ℝ)
    (h : ∀ s : Finset J, |∑ i ∈ s, f i| ≤ c) : Summable f := by
  classical
  have hp (g : J → ℝ) (hg : ∀ s : Finset J, |∑ i ∈ s, g i| ≤ c) :
      Summable (fun i => max (g i) 0) := by
    apply summable_of_sum_le (f := fun i => max (g i) (0 : ℝ)) (c := c) (fun _ => le_max_right _ _)
    intro s
    have he : ∑ i ∈ s, max (g i) 0 = ∑ i ∈ s.filter (fun i => 0 ≤ g i), g i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · exact max_eq_left hi
      · exact max_eq_right (le_of_not_ge hi)
    rw [he]
    exact (le_abs_self _).trans (hg _)
  have hn : ∀ s : Finset J, |∑ i ∈ s, -f i| ≤ c := by
    intro s
    simpa only [Finset.sum_neg_distrib,abs_neg] using h s
  convert (hp f h).sub (hp (fun i => -f i) hn) using 1
  funext i
  by_cases hi : 0 ≤ f i
  · rw [max_eq_left hi,max_eq_right (neg_nonpos.mpr hi),sub_zero]
  · rw [max_eq_right (le_of_not_ge hi),max_eq_left (neg_nonneg.mpr (le_of_not_ge hi))]
    ring

/-- Constructed complex trace in a specified complete Hilbert basis. -/
def trace (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) : ℂ :=
  ∑' i, ⟪b i,T (b i)⟫_ℂ

theorem diagonal_bound (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (hT : traceNorm T ≠ ⊤) (s : Finset ι) :
    ‖∑ i ∈ s, ⟪b i,T (b i)⟫_ℂ‖ ≤ (traceNorm T).toReal := by
  simpa only [one_apply_eq_self] using
    norm_sum_inner_le_traceNorm b T 1 ContinuousLinearMap.norm_id_le hT s

theorem diagonal_summable (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (hT : traceNorm T ≠ ⊤) : Summable (fun i => ⟪b i,T (b i)⟫_ℂ) := by
  have hr : Summable (fun i => (⟪b i,T (b i)⟫_ℂ).re) := by
    apply real_summable _ (traceNorm T).toReal
    intro s
    rw [← Complex.re_sum]
    exact (Complex.abs_re_le_norm _).trans (diagonal_bound b T hT s)
  have hi : Summable (fun i => (⟪b i,T (b i)⟫_ℂ).im) := by
    apply real_summable _ (traceNorm T).toReal
    intro s
    rw [← Complex.im_sum]
    exact (Complex.abs_im_le_norm _).trans (diagonal_bound b T hT s)
  have h := (Complex.ofRealCLM.summable hr).add
    ((Complex.ofRealCLM.summable hi).mul_right Complex.I)
  convert h using 1
  funext i
  exact (Complex.re_add_im _).symm

theorem norm_trace_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (hT : traceNorm T ≠ ⊤) : ‖trace b T‖ ≤ (traceNorm T).toReal :=
  le_of_tendsto (diagonal_summable b T hT).hasSum.norm
    (.of_forall (diagonal_bound b T hT))

theorem finite_left (K T : E →L[ℂ] E) (hT : traceNorm T ≠ ⊤) :
    traceNorm (K*T) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT)
    (traceNorm_mul_left_le K T)

/-- Complex trace duality bound, with its exact trace norm constant. -/
theorem pairing_bound (b : HilbertBasis ι ℂ E) (K T : E →L[ℂ] E)
    (hT : traceNorm T ≠ ⊤) :
    ‖trace b (K*T)‖ ≤ ‖K‖*(traceNorm T).toReal := by
  refine (norm_trace_le b (K*T) (finite_left K T hT)).trans ?_
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT) (traceNorm_mul_left_le K T)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (norm_nonneg K)] using h

theorem trace_sub (b : HilbertBasis ι ℂ E) (S T : E →L[ℂ] E)
    (hS : traceNorm S ≠ ⊤) (hT : traceNorm T ≠ ⊤) :
    trace b (S-T) = trace b S-trace b T := by
  simp only [trace,sub_apply,inner_sub_right]
  exact (diagonal_summable b S hS).tsum_sub (diagonal_summable b T hT)

/-- Cyclicity for a diagonal bounded multiplier. This exact identity is
sufficient for the physical kinetic spectral/root cutoffs. -/
theorem diagonal_cycle (b : HilbertBasis ι ℂ E) (D T : E →L[ℂ] E)
    (a : ι → ℂ) (ha : ∀ i, D (b i) = a i • b i) :
    trace b (D*T) = trace b (T*D) := by
  apply tsum_congr
  intro i
  rw [mul_apply_eq_comp,mul_apply_eq_comp,ha,map_smul,
    inner_smul_right]
  simpa only [HilbertBasis.repr_apply_apply] using
    BoundedBetheTransfer.diagonal_coord b D a ha (T (b i)) i
end QuantumNLS.Ext025B11TracePairing

#print axioms QuantumNLS.Ext025B11TracePairing.diagonal_summable
#print axioms QuantumNLS.Ext025B11TracePairing.pairing_bound
#print axioms QuantumNLS.Ext025B11TracePairing.diagonal_cycle
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B11TracePairing" then
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
  Lean.logInfo m!"Ext025B11TracePairing audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
