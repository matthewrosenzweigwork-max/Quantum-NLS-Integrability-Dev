import QuantumNLS.Ext025B6PVM
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.UniformSpace.Equicontinuity

/-! GP-08, R-C17D95AA: the spectral projection and compact-compression
steps for arbitrary PVMs, without an atomicity or compact-resolvent premise.
The identification with the spectral measure of an arbitrary unbounded
Hamiltonian remains a separate open clause. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext025B7SpectralCompression
open BetheChargeResolution Ext025B6PVM
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

theorem projection_error_sq (s : Set ℝ) (hs : MeasurableSet s) (x : E) :
    ‖x - P.toFun s x‖^2 = ‖x‖^2 - ‖P.toFun s x‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_self_project P s hs]
  change ‖x‖^2-2*‖P.toFun s x‖^2+‖P.toFun s x‖^2 = ‖x‖^2-‖P.toFun s x‖^2
  ring

theorem complement_norm_le (s : Set ℝ) (hs : MeasurableSet s) :
    ‖1 - P.toFun s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := projection_error_sq P s hs x
  change ‖x - P.toFun s x‖ ≤ 1 * ‖x‖
  nlinarith [sq_nonneg ‖P.toFun s x‖, norm_nonneg (x-P.toFun s x), norm_nonneg x]

/-- Increasing exhaustive measurable spectral windows converge strongly. -/
theorem exhaustion_strong (s : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (x : E) :
    Tendsto (fun n => P.toFun (s n) x) atTop (𝓝 x) := by
  have hμ := tendsto_measure_iUnion_atTop (μ := scalarMeasure P x) hm
  rw [hu,scalarMeasure_univ] at hμ
  have hr := (ENNReal.tendsto_toReal (by simp)).comp hμ
  have hr' : Tendsto (fun n => ‖P.toFun (s n) x‖^2) atTop (𝓝 (‖x‖^2)) := by
    simpa only [Function.comp_def,scalarMeasure_apply P x _ (hs _),
      ENNReal.toReal_ofReal (sq_nonneg _)] using hr
  have hh : Tendsto (fun n => ‖x - P.toFun (s n) x‖^2) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => ‖x‖^2) atTop (𝓝 (‖x‖^2)) := tendsto_const_nhds
    simpa only [projection_error_sq P _ (hs _),sub_self] using hc.sub hr'
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _),norm_sub_rev] using hn

/-- These windows cover the whole real line; no lower spectral bound is needed. -/
theorem upper_windows_strong (x : E) :
    Tendsto (fun n : ℕ => P.toFun (Set.Iic (n : ℝ)) x) atTop (𝓝 x) := by
  apply exhaustion_strong P _ (fun _ => measurableSet_Iic)
    (fun i j hij => Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hij)) _ x
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact Set.mem_iUnion.mpr ⟨n,hn⟩

/-- Literal [1,M] windows in the application, for a PVM supported in [1,∞). -/
theorem positive_windows_eq (hpos : P.toFun (Set.Ici 1) = 1) (n : ℕ) :
    P.toFun (Set.Icc 1 (n : ℝ)) = P.toFun (Set.Iic (n : ℝ)) := by
  have h := P.inter (Set.Ici 1) (Set.Iic (n : ℝ)) measurableSet_Ici measurableSet_Iic
  rw [hpos,one_mul] at h
  exact h.symm

theorem positive_windows_strong (hpos : P.toFun (Set.Ici 1) = 1) (x : E) :
    Tendsto (fun n : ℕ => P.toFun (Set.Icc 1 (n : ℝ)) x) atTop (𝓝 x) := by
  simpa only [positive_windows_eq P hpos] using upper_windows_strong P x

/-- The finite-net step, on the actual compact image of the vectors. -/
theorem exhaustion_uniform_compact (s : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (K : Set E) (hK : IsCompact K) :
    TendstoUniformly (fun n => fun x : K => P.toFun (s n) x.val) (fun x => x.val) atTop := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLip : ∀ n, LipschitzWith 1 (fun x : K => P.toFun (s n) x.val) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Subtype.dist_eq,dist_eq_norm,← map_sub,NNReal.coe_one,one_mul] using
      projection_norm_le P (s n) (hs n) (x.val-y.val)
  have heq := (LipschitzWith.uniformEquicontinuous _ 1 hLip).equicontinuous
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (heq.tendsto_uniformFun_iff_pi atTop (fun x : K => x.val)).2
  exact tendsto_pi_nhds.mpr fun x => exhaustion_strong P s hs hm hu x.val

/-- Strong spectral exhaustion converges in norm after a compact operator. -/
theorem compact_left (s : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) :
    Tendsto (fun n => (1 - P.toFun (s n)) * T) atTop (𝓝 0) := by
  obtain ⟨K,hK,hTK⟩ := hT.image_closedBall_subset_compact 1
  have hU := Metric.tendstoUniformly_iff.mp (exhaustion_uniform_compact P s hs hm hu K hK)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (norm_nonneg _)
  · intro ε hε
    filter_upwards [hU (ε/2) (by linarith)] with n hn
    have hb : ‖(1-P.toFun (s n))*T‖ ≤ ε/2 := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith)
      intro x hx
      have hxK : T x ∈ K := hTK ⟨x,by simp [Metric.mem_closedBall,dist_zero_right,hx],rfl⟩
      have hi := hn ⟨T x,hxK⟩
      change dist (T x) (P.toFun (s n) (T x)) < ε/2 at hi
      change ‖T x-P.toFun (s n) (T x)‖ ≤ ε/2
      simpa only [dist_eq_norm] using hi.le
    linarith

/-- The right compact tail follows from the left tail of T* T. This avoids
assuming norm convergence of the spectral projections themselves. -/
theorem compact_right (s : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) :
    Tendsto (fun n => T * (1 - P.toFun (s n))) atTop (𝓝 0) := by
  have hTT : IsCompactOperator (T.adjoint * T) := hT.clm_comp T.adjoint
  have hleft := compact_left P s hs hm hu (T.adjoint*T) hTT
  have hsq (n : ℕ) : ‖T*(1-P.toFun (s n))‖^2 ≤
      ‖(1-P.toFun (s n))*(T.adjoint*T)‖ := by
    let R := 1-P.toFun (s n)
    have hR : R.adjoint = R := by
      simp only [R,map_sub,ContinuousLinearMap.adjoint_one,P.selfAdjoint _ (hs n)]
    have he : (T*R).adjoint*(T*R) = (R*(T.adjoint*T))*R := by
      change star (T*R)*(T*R) = (R*(star T*T))*R
      rw [star_mul,show star R = R from hR]
      simp only [mul_assoc]
    calc
      ‖T*R‖^2 = ‖(T*R).adjoint*(T*R)‖ := by
        simpa only [ContinuousLinearMap.mul_def,pow_two] using
          (ContinuousLinearMap.norm_adjoint_comp_self (T*R)).symm
      _ = ‖(R*(T.adjoint*T))*R‖ := congrArg norm he
      _ ≤ ‖R*(T.adjoint*T)‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ ‖R*(T.adjoint*T)‖ * 1 :=
        mul_le_mul_of_nonneg_left (complement_norm_le P _ (hs n)) (norm_nonneg _)
      _ = _ := mul_one _
  have hz : Tendsto (fun n => ‖T*(1-P.toFun (s n))‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hsq (by simpa using hleft.norm)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hz

/-- The precise compact norm-compression step in R-C17D95AA. -/
theorem compact_compression (s : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hu : ⋃ n, s n = Set.univ) (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) :
    Tendsto (fun n => P.toFun (s n)*T*P.toFun (s n)) atTop (𝓝 T) := by
  have hleft := compact_left P s hs hm hu T hT
  have hright := compact_right P s hs hm hu T hT
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hleft.norm.add hright.norm)
  intro n
  have hP : ‖P.toFun (s n)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa only [one_mul] using projection_norm_le P _ (hs n) x)
  have he : T-P.toFun (s n)*T*P.toFun (s n) =
      (1-P.toFun (s n))*T+P.toFun (s n)*(T*(1-P.toFun (s n))) := by noncomm_ring
  rw [norm_sub_rev,he]
  apply (norm_add_le _ _).trans
  apply add_le_add (le_refl _)
  calc
    ‖P.toFun (s n)*(T*(1-P.toFun (s n)))‖ ≤
        ‖P.toFun (s n)‖*‖T*(1-P.toFun (s n))‖ := norm_mul_le _ _
    _ ≤ 1*‖T*(1-P.toFun (s n))‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ = _ := one_mul _

/-- Literal application windows; arbitrary spectral multiplicity is allowed. -/
theorem positive_compact_compression (hpos : P.toFun (Set.Ici 1) = 1)
    (T : E →L[ℂ] E) (hT : IsCompactOperator T) :
    Tendsto (fun n : ℕ => P.toFun (Set.Icc 1 (n : ℝ))*T*P.toFun (Set.Icc 1 (n : ℝ)))
      atTop (𝓝 T) := by
  simp only [positive_windows_eq P hpos]
  apply compact_compression P _ (fun _ => measurableSet_Iic)
    (fun i j hij => Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hij)) _ T hT
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact Set.mem_iUnion.mpr ⟨n,hn⟩

end QuantumNLS.Ext025B7SpectralCompression

#print axioms QuantumNLS.Ext025B7SpectralCompression.projection_error_sq
#print axioms QuantumNLS.Ext025B7SpectralCompression.complement_norm_le
#print axioms QuantumNLS.Ext025B7SpectralCompression.exhaustion_strong
#print axioms QuantumNLS.Ext025B7SpectralCompression.upper_windows_strong
#print axioms QuantumNLS.Ext025B7SpectralCompression.positive_windows_eq
#print axioms QuantumNLS.Ext025B7SpectralCompression.positive_windows_strong
#print axioms QuantumNLS.Ext025B7SpectralCompression.exhaustion_uniform_compact
#print axioms QuantumNLS.Ext025B7SpectralCompression.compact_left
#print axioms QuantumNLS.Ext025B7SpectralCompression.compact_right
#print axioms QuantumNLS.Ext025B7SpectralCompression.compact_compression
#print axioms QuantumNLS.Ext025B7SpectralCompression.positive_compact_compression

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B7SpectralCompression." then
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
  Lean.logInfo m!"Ext025B7SpectralCompression audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
