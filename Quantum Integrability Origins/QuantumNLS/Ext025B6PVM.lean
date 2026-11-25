import QuantumNLS.BetheChargeResolution
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! GP-08, arbitrary normalized strongly additive PVMs. The scalar spectral
measure is constructed from the PVM laws, with no atomicity or representation
hypothesis. This is a foundation for, not an assumption of, Borel integration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory InnerProductSpace Filter Topology Function
open scoped InnerProductSpace ComplexConjugate BigOperators
namespace QuantumNLS.Ext025B6PVM
open BetheChargeResolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

theorem idempotent (s : Set ℝ) (hs : MeasurableSet s) :
    P.toFun s * P.toFun s = P.toFun s := by simpa using P.inter s s hs hs

theorem inner_project (s : Set ℝ) (hs : MeasurableSet s) (x y : E) :
    ⟪P.toFun s x, y⟫_ℂ = ⟪x, P.toFun s y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, P.selfAdjoint s hs]

theorem inner_self_project (s : Set ℝ) (hs : MeasurableSet s) (x : E) :
    ⟪x, P.toFun s x⟫_ℂ = (‖P.toFun s x‖^2 : ℝ) := by
  have hi := congrArg (fun T : E →L[ℂ] E => T x) (idempotent P s hs)
  change P.toFun s (P.toFun s x) = P.toFun s x at hi
  calc
    ⟪x, P.toFun s x⟫_ℂ = ⟪x, P.toFun s (P.toFun s x)⟫_ℂ := congrArg (inner ℂ x) hi.symm
    _ = ⟪P.toFun s x, P.toFun s x⟫_ℂ := (inner_project P s hs x (P.toFun s x)).symm
    _ = _ := by simp [inner_self_eq_norm_sq_to_K]

theorem disjoint_inner (s t : Set ℝ) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hd : Disjoint s t) (x y : E) :
    ⟪P.toFun s x, P.toFun t y⟫_ℂ = 0 := by
  rw [inner_project P s hs]
  have hi := congrArg (fun T : E →L[ℂ] E => T y) (P.inter s t hs ht)
  change P.toFun s (P.toFun t y) = P.toFun (s ∩ t) y at hi
  rw [hi, Set.disjoint_iff_inter_eq_empty.mp hd, P.empty]
  simp

/-- Countable additivity of the squared projection norms is derived from
strong additivity by a scalar pairing. -/
theorem norm_sq_hasSum (s : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Disjoint on s)) (x : E) :
    HasSum (fun n => ‖P.toFun (s n) x‖^2) (‖P.toFun (⋃ n, s n) x‖^2) := by
  have h := (P.additive s hs hd x).mapL (innerSL ℂ x)
  have hr := Complex.hasSum_re h
  change HasSum (fun n => (⟪x,P.toFun (s n) x⟫_ℂ).re) (⟪x,P.toFun (⋃ n,s n) x⟫_ℂ).re at hr
  simpa only [inner_self_project P _ (MeasurableSet.iUnion hs),
    inner_self_project P _ (hs _), Complex.ofReal_re] using hr

/-- The scalar spectral measure at x, for an arbitrary PVM. -/
def scalarMeasure (x : E) : Measure ℝ :=
  Measure.ofMeasurable (fun s _ => ENNReal.ofReal (‖P.toFun s x‖^2))
    (by rw [P.empty]; simp)
    (by
      intro s hs hd
      have h := norm_sq_hasSum P s hs hd x
      rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable])

theorem scalarMeasure_apply (x : E) (s : Set ℝ) (hs : MeasurableSet s) :
    scalarMeasure P x s = ENNReal.ofReal (‖P.toFun s x‖^2) :=
  Measure.ofMeasurable_apply s hs

theorem scalarMeasure_univ (x : E) :
    scalarMeasure P x Set.univ = ENNReal.ofReal (‖x‖^2) := by
  rw [scalarMeasure_apply P x _ MeasurableSet.univ, P.univ]
  rfl

instance scalarMeasure_finite (x : E) : IsFiniteMeasure (scalarMeasure P x) :=
  ⟨by rw [scalarMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem scalarMeasure_zero_iff (x : E) (s : Set ℝ) (hs : MeasurableSet s) :
    scalarMeasure P x s = 0 ↔ P.toFun s x = 0 := by
  rw [scalarMeasure_apply P x s hs, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have hz : ‖P.toFun s x‖ = 0 := by nlinarith [norm_nonneg (P.toFun s x)]
    exact norm_eq_zero.mp hz
  · intro h
    simp [h]

/-- Every measurable projection is a contraction. -/
theorem projection_norm_le (s : Set ℝ) (hs : MeasurableSet s) (x : E) :
    ‖P.toFun s x‖ ≤ ‖x‖ := by
  have h := measure_mono (μ := scalarMeasure P x) (Set.subset_univ s)
  rw [scalarMeasure_apply P x s hs, scalarMeasure_univ] at h
  have hh := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖x‖)).mp h
  nlinarith [norm_nonneg x, norm_nonneg (P.toFun s x)]

/-- The scalar measure of a projected vector is restriction of its original
scalar measure. This is the PVM foundation of common-resolution laws. -/
theorem scalarMeasure_project (s : Set ℝ) (hs : MeasurableSet s) (x : E) :
    scalarMeasure P (P.toFun s x) = (scalarMeasure P x).restrict s := by
  apply Measure.ext
  intro t ht
  rw [scalarMeasure_apply P _ t ht, Measure.restrict_apply ht,
    scalarMeasure_apply P x (t ∩ s) (ht.inter hs)]
  have he := congrArg (fun T : E →L[ℂ] E => T x) (P.inter t s ht hs)
  exact congrArg (fun v : E => ENNReal.ofReal (‖v‖^2)) he

/-- Finite-step spectral integral on a disjoint measurable family. -/
def step {ι : Type*} (F : Finset ι) (s : ι → Set ℝ) (a : ι → ℂ) : E →L[ℂ] E :=
  ∑ i ∈ F, a i • P.toFun (s i)

theorem step_norm_sq {ι : Type*} (F : Finset ι) (s : ι → Set ℝ)
    (a : ι → ℂ) (hs : ∀ i ∈ F, MeasurableSet (s i))
    (hd : (F : Set ι).Pairwise (Disjoint on s)) (x : E) :
    ‖step P F s a x‖^2 = ∑ i ∈ F, ‖a i‖^2 * ‖P.toFun (s i) x‖^2 := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [step]
  | @insert i F hi ih =>
    have hsF : ∀ j ∈ F, MeasurableSet (s j) := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hdF : (F : Set ι).Pairwise (Disjoint on s) := fun j hj k hk hjk =>
      hd (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk
    have he : step P (insert i F) s a x = a i • P.toFun (s i) x + step P F s a x := by
      simp [step, Finset.sum_insert hi]
    have ho : ⟪a i • P.toFun (s i) x, step P F s a x⟫_ℂ = 0 := by
      simp only [step,sum_apply,smul_apply,inner_sum,inner_smul_left,inner_smul_right]
      apply Finset.sum_eq_zero
      intro j hj
      rw [disjoint_inner P (s i) (s j) (hs i (Finset.mem_insert_self i F)) (hsF j hj)
        (hd (Finset.mem_insert_self i F) (Finset.mem_insert_of_mem hj) (by
          intro hij; exact hi (hij.symm ▸ hj)))]
      simp
    have hp : ‖a i • P.toFun (s i) x + step P F s a x‖^2 =
        ‖a i • P.toFun (s i) x‖^2 + ‖step P F s a x‖^2 := by
      simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
    rw [he,hp,norm_smul,mul_pow,ih hsF hdF,Finset.sum_insert hi]

end QuantumNLS.Ext025B6PVM

#print axioms QuantumNLS.Ext025B6PVM.idempotent
#print axioms QuantumNLS.Ext025B6PVM.inner_project
#print axioms QuantumNLS.Ext025B6PVM.inner_self_project
#print axioms QuantumNLS.Ext025B6PVM.disjoint_inner
#print axioms QuantumNLS.Ext025B6PVM.norm_sq_hasSum
#print axioms QuantumNLS.Ext025B6PVM.scalarMeasure
#print axioms QuantumNLS.Ext025B6PVM.scalarMeasure_apply
#print axioms QuantumNLS.Ext025B6PVM.scalarMeasure_univ
#print axioms QuantumNLS.Ext025B6PVM.scalarMeasure_finite
#print axioms QuantumNLS.Ext025B6PVM.scalarMeasure_zero_iff
#print axioms QuantumNLS.Ext025B6PVM.projection_norm_le
#print axioms QuantumNLS.Ext025B6PVM.scalarMeasure_project
#print axioms QuantumNLS.Ext025B6PVM.step
#print axioms QuantumNLS.Ext025B6PVM.step_norm_sq

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B6PVM." then
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
  Lean.logInfo m!"Ext025B6PVM audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
