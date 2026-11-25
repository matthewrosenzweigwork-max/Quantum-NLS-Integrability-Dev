import QuantumNLS.Ext025A12Trace
import Mathlib.Analysis.Normed.Group.Tannery

/-! Trace-norm continuity, nuclear expansion, cyclicity and normality of the
constructed complex trace. These are proofs on the actual trace ideal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025A12Normal
open TraceClass TraceIdeal TraceCompact Fidelity Ext025B11TracePairing Ext025A12Trace
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem finite_frame (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (s : Finset ι) :
    IsTraceClass (frameSum b T s) := by
  rw [IsTraceClass,traceNorm_of_isPositive (isPositive_frameSum b T s),posTrace_frameSum]
  exact ENNReal.ofReal_lt_top

theorem finite_right (K T : E →L[ℂ] E) (ht : IsTraceClass T) : IsTraceClass (T*K) :=
  (traceNorm_mul_right_le T K).trans_lt (ENNReal.mul_lt_top ht ENNReal.ofReal_lt_top)

theorem frame_weights (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (hT : T.IsPositive) (ht : IsTraceClass T) :
    HasSum (fun i => ‖CFC.sqrt T (b i)‖^2) (posTrace T).toReal := by
  apply hasSum_of_tsum_ofReal (fun _ => sq_nonneg _) ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal (by rw [← traceNorm_of_isPositive hT];exact ht.ne)]
  exact (traceIn_eq_hsSq_sqrt b hT).symm.trans (posTrace_eq b hT).symm

theorem frame_tail (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (hT : T.IsPositive) (ht : IsTraceClass T) :
    Tendsto (fun s : Finset ι => traceNorm (T-frameSum b T s)) atTop (𝓝 0) := by
  have he (s : Finset ι) : traceNorm (T-frameSum b T s) =
      ENNReal.ofReal ((posTrace T).toReal-∑ i ∈ s, ‖CFC.sqrt T (b i)‖^2) := by
    have hp := isPositive_sub_frameSum b hT s
    have ha := posTrace_add (isPositive_frameSum b T s) hp
    rw [add_sub_cancel,posTrace_frameSum] at ha
    have hh : posTrace (T-frameSum b T s) = posTrace T-
        ENNReal.ofReal (∑ i ∈ s, ‖CFC.sqrt T (b i)‖^2) :=
      ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top (by rw [add_comm];exact ha.symm)
    rw [traceNorm_of_isPositive hp,hh,ENNReal.ofReal_sub _ (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      ENNReal.ofReal_toReal (by rw [← traceNorm_of_isPositive hT];exact ht.ne)]
  simp_rw [he]
  have hw : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖CFC.sqrt T (b i)‖^2) atTop
      (𝓝 (posTrace T).toReal) := by simpa only [HasSum,SummationFilter.unconditional_filter] using frame_weights b T hT ht
  have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (posTrace T).toReal)).sub hw)
  simpa only [sub_self,ENNReal.ofReal_zero] using h

/-- Trace is continuous for convergence in the repository's trace norm. -/
theorem trace_limit {J : Type*} {l : Filter J} (b : HilbertBasis ι ℂ E)
    (A : J → E →L[ℂ] E) (T : E →L[ℂ] E)
    (ha : ∀ j, IsTraceClass (A j)) (ht : IsTraceClass T)
    (h : Tendsto (fun j => traceNorm (T-A j)) l (𝓝 0)) :
    Tendsto (fun j => trace b (A j)) l (𝓝 (trace b T)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at hlim
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro j
  rw [norm_sub_rev,← trace_sub b T (A j) ht.ne (ha j).ne]
  exact norm_trace_le b _ (finite_sub ht (ha j)).ne

theorem trace_rankOne (b : HilbertBasis ι ℂ E) (x y : E) :
    trace b (InnerProductSpace.rankOne ℂ x y) = ⟪y,x⟫_ℂ := by
  unfold trace
  simp only [InnerProductSpace.rankOne_apply,inner_smul_right]
  simpa only [mul_comm] using (b.hasSum_inner_mul_inner y x).tsum_eq

theorem trace_rankOne_left (b : HilbertBasis ι ℂ E) (K : E →L[ℂ] E) (x y : E) :
    trace b (K*InnerProductSpace.rankOne ℂ x y) = ⟪y,K x⟫_ℂ := by
  rw [ContinuousLinearMap.mul_def,InnerProductSpace.comp_rankOne,trace_rankOne]

theorem trace_rankOne_right (b : HilbertBasis ι ℂ E) (K : E →L[ℂ] E) (x y : E) :
    trace b (InnerProductSpace.rankOne ℂ x y*K) = ⟪y,K x⟫_ℂ := by
  rw [ContinuousLinearMap.mul_def,InnerProductSpace.rankOne_comp,trace_rankOne,
    ContinuousLinearMap.adjoint_inner_left]

/-- The bounded observable functional, constructed from the complex diagonal
trace and the already proved ideal bound. -/
def pairing (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (ht : IsTraceClass T) :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun K => trace b (K*T)
      map_add' := fun K L => by
        rw [add_mul,trace_add b (lt_top_iff_ne_top.mpr (finite_left K T ht.ne))
          (lt_top_iff_ne_top.mpr (finite_left L T ht.ne))]
      map_smul' := fun a K => by simp only [smul_mul_assoc,trace_smul,smul_eq_mul,RingHom.id_apply] }
    (traceNorm T).toReal (fun K => by
      change ‖trace b (K*T)‖ ≤ (traceNorm T).toReal*‖K‖
      simpa only [mul_comm] using pairing_bound b K T ht.ne)

/-- Nuclear trace expansion for an arbitrary positive trace-class operator;
the basis can have any cardinality. -/
theorem trace_positive_series (b : HilbertBasis ι ℂ E) (K T : E →L[ℂ] E)
    (hT : T.IsPositive) (ht : IsTraceClass T) :
    HasSum (fun i => ⟪CFC.sqrt T (b i),K (CFC.sqrt T (b i))⟫_ℂ) (trace b (K*T)) := by
  have htail : Tendsto (fun s : Finset ι => traceNorm (K*T-K*frameSum b T s)) atTop (𝓝 0) := by
    simp only [← mul_sub]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ≥0∞)) (a := 0) tendsto_const_nhds
      (h := fun s => ENNReal.ofReal ‖K‖*traceNorm (T-frameSum b T s)) ?_
      (fun _ => zero_le) (fun s => traceNorm_mul_left_le K (T-frameSum b T s))
    simpa only [mul_zero] using (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖K‖)
      (frame_tail b T hT ht) (Or.inr ENNReal.ofReal_ne_top))
  have hlim := trace_limit b (fun s => K*frameSum b T s) (K*T)
    (fun s => lt_top_iff_ne_top.mpr (finite_left K _ (finite_frame b T s).ne))
    (lt_top_iff_ne_top.mpr (finite_left K T ht.ne)) htail
  have he (s : Finset ι) : trace b (K*frameSum b T s) =
      ∑ i ∈ s, ⟪CFC.sqrt T (b i),K (CFC.sqrt T (b i))⟫_ℂ := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [frameSum,trace]
    | insert i s hi ih =>
      let w := CFC.sqrt T (b i)
      have hwi : IsTraceClass (InnerProductSpace.rankOne ℂ w w) :=
        (traceNorm_rankOne_le w w).trans_lt ENNReal.ofReal_lt_top
      have heq : frameSum b T (insert i s) = InnerProductSpace.rankOne ℂ w w+frameSum b T s := by
        simp only [frameSum,Finset.sum_insert hi,w]
      rw [heq,mul_add,trace_add b (lt_top_iff_ne_top.mpr (finite_left K _ hwi.ne))
        (lt_top_iff_ne_top.mpr (finite_left K _ (finite_frame b T s).ne)),
        trace_rankOne_left,Finset.sum_insert hi,ih]
  simpa only [HasSum,SummationFilter.unconditional_filter,he] using hlim

/-- Bounded strong convergence of observables passes through a trace-class
pairing. This supplies the normality needed for infinite partial traces. -/
theorem pairing_strong {J : Type*} {l : Filter J} (b : HilbertBasis ι ℂ E)
    (K : J → E →L[ℂ] E) (A T : E →L[ℂ] E) (ht : IsTraceClass T)
    (hK : ∀ x, Tendsto (fun j => K j x) l (𝓝 (A x)))
    (M : ℝ) (hb : ∀ j, ‖K j‖ ≤ M) :
    Tendsto (fun j => trace b (K j*T)) l (𝓝 (trace b (A*T))) := by
  apply positive_span (fun T => Tendsto (fun j => trace b (K j*T)) l (𝓝 (trace b (A*T)))) _ _ _ T ht
  · intro S hs hts
    have hser (B : E →L[ℂ] E) := trace_positive_series b B S hs hts
    simp_rw [← (hser _).tsum_eq]
    apply tendsto_tsum_of_dominated_convergence ((frame_weights b S hs hts).summable.mul_left M)
    · intro i
      exact tendsto_const_nhds.inner (hK _)
    · exact .of_forall fun j i => (norm_inner_le_norm _ _).trans (by
        have h := ((K j).le_opNorm (CFC.sqrt S (b i))).trans
          (mul_le_mul_of_nonneg_right (hb j) (norm_nonneg _))
        nlinarith [norm_nonneg (CFC.sqrt S (b i))])
  · intro S R hs hr hp hq
    simp only [mul_add,trace_add b
      (lt_top_iff_ne_top.mpr (finite_left _ S hs.ne))
      (lt_top_iff_ne_top.mpr (finite_left _ R hr.ne))]
    exact hp.add hq
  · intro a S hs hp
    simp only [mul_smul_comm,trace_smul]
    exact tendsto_const_nhds.mul hp

/-- Cyclicity for every trace-class operator and every bounded operator. -/
theorem trace_cycle (b : HilbertBasis ι ℂ E) (K T : E →L[ℂ] E)
    (ht : IsTraceClass T) : trace b (K*T) = trace b (T*K) := by
  apply positive_span (fun T => trace b (K*T) = trace b (T*K)) _ _ _ T ht
  · intro S hs hts
    have htail : Tendsto (fun s : Finset ι => traceNorm (S*K-frameSum b S s*K)) atTop (𝓝 0) := by
      simp only [← sub_mul]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ≥0∞)) (a := 0) tendsto_const_nhds
        (h := fun s => traceNorm (S-frameSum b S s)*ENNReal.ofReal ‖K‖) ?_
        (fun _ => zero_le) (fun s => traceNorm_mul_right_le (S-frameSum b S s) K)
      simpa only [zero_mul] using (ENNReal.Tendsto.mul_const (b := ENNReal.ofReal ‖K‖)
        (frame_tail b S hs hts) (Or.inr ENNReal.ofReal_ne_top))
    have hlim := trace_limit b (fun s => frameSum b S s*K) (S*K)
      (fun s => finite_right K _ (finite_frame b S s)) (finite_right K S hts) htail
    have he (s : Finset ι) : trace b (frameSum b S s*K) =
        ∑ i ∈ s, ⟪CFC.sqrt S (b i),K (CFC.sqrt S (b i))⟫_ℂ := by
      classical
      induction s using Finset.induction_on with
      | empty => simp [frameSum,trace]
      | insert i s hi ih =>
        let w := CFC.sqrt S (b i)
        have hwi : IsTraceClass (InnerProductSpace.rankOne ℂ w w) :=
          (traceNorm_rankOne_le w w).trans_lt ENNReal.ofReal_lt_top
        have heq : frameSum b S (insert i s) = InnerProductSpace.rankOne ℂ w w+frameSum b S s := by
          simp only [frameSum,Finset.sum_insert hi,w]
        rw [heq,add_mul,trace_add b (finite_right K _ hwi)
          (finite_right K _ (finite_frame b S s)),trace_rankOne_right,Finset.sum_insert hi,ih]
    exact (trace_positive_series b K S hs hts).unique (by simpa only [HasSum,SummationFilter.unconditional_filter,he] using hlim)
  · intro S R hs hr hp hq
    rw [mul_add,add_mul,
      trace_add b (lt_top_iff_ne_top.mpr (finite_left _ S hs.ne))
        (lt_top_iff_ne_top.mpr (finite_left _ R hr.ne)),
      trace_add b (finite_right _ S hs) (finite_right _ R hr),hp,hq]
  · intro a S _ hp
    rw [mul_smul_comm,smul_mul_assoc,trace_smul,trace_smul,hp]

open scoped ComplexOrder in
/-- Positive inputs give positive bounded-observable expectations. -/
theorem pairing_nonneg (b : HilbertBasis ι ℂ E) (K T : E →L[ℂ] E)
    (hk : K.IsPositive) (hT : T.IsPositive) (ht : IsTraceClass T) :
    0 ≤ trace b (K*T) := by
  have h := trace_positive_series b K T hT ht
  rw [HasSum] at h
  exact ge_of_tendsto' h (fun s => Finset.sum_nonneg fun i _ => hk.inner_nonneg_right _)

end QuantumNLS.Ext025A12Normal

#print axioms QuantumNLS.Ext025A12Normal.frame_tail
#print axioms QuantumNLS.Ext025A12Normal.trace_positive_series
#print axioms QuantumNLS.Ext025A12Normal.pairing_strong
#print axioms QuantumNLS.Ext025A12Normal.trace_cycle
#print axioms QuantumNLS.Ext025A12Normal.pairing_nonneg
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A12Normal" then
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
  Lean.logInfo m!"Ext025A12Normal audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
