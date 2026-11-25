import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Group.Tannery

/-! Author: sol_ext_b. Exact contracts are copied in Ext025B.contracts.json.
GP-11--14 are stated over arbitrary fixed measure spaces, hence include the
real-line and Fourier counting-measure cases. Application narratives about the
physical hierarchy, cutoffs, and contours are descriptive prose; they do not
supply additional hypotheses about an already constructed physical object. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.Ext025BMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- GP-11: the nonnegative pointwise limit may have infinite integral. -/
theorem «FIN-EXT025-GP-11» (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hm : Monotone f) :
    (∫⁻ x, ⨆ n, f n x ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ :=
  lintegral_iSup hf hm

/-- GP-11 counting-measure wrapper, with no finiteness assumption. -/
theorem «FIN-EXT025-GP-11-counting» (a : ℕ → ℝ≥0∞) :
    ∑' k, a k = ⨆ n, ∑ k ∈ Finset.range n, a k :=
  ENNReal.tsum_eq_iSup_nat

/-- GP-12: Fatou's inequality for nonnegative measurable scalar functions. -/
theorem «FIN-EXT025-GP-12» (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤
      liminf (fun n => ∫⁻ x, f n x ∂μ) atTop :=
  lintegral_liminf_le hf

/-- GP-12 form wrapper: the supremum of continuous bounded truncation tests is
lower semicontinuous. The topology may in particular be the trace-norm topology;
continuity of each test must be established in that topology by the consumer. -/
theorem «FIN-EXT025-GP-12-truncations» {X : Type*} [TopologicalSpace X]
    (q : ℕ → X → ℝ≥0∞) (hq : ∀ n, Continuous (q n)) :
    LowerSemicontinuous (fun x => ⨆ n, q n x) :=
  lowerSemicontinuous_iSup (fun n => (hq n).lowerSemicontinuous)

/-- GP-13: complex scalar dominated convergence on the fixed measure space. -/
theorem «FIN-EXT025-GP-13» (f : ℕ → α → ℂ) (g : α → ℂ) (b : α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) :=
  tendsto_integral_of_dominated_convergence b hf hb hbound hlim

/-- GP-13 norm/square wrapper: convergence of the integrals of a dominated
nonnegative error density to zero. Choosing squared Fourier errors gives the
claimed squared norm convergence after its Parseval identification. -/
theorem «FIN-EXT025-GP-13-errors» (e : ℕ → α → ℝ) (b : α → ℝ)
    (he : ∀ n, AEStronglyMeasurable (e n) μ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖e n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => e n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, e n x ∂μ) atTop (𝓝 0) := by
  simpa using tendsto_integral_of_dominated_convergence b he hb hbound hlim

/-- GP-14: Tonelli and measurability of both inner nonnegative integrals. -/
theorem «FIN-EXT025-GP-14» [SigmaFinite μ] [SigmaFinite ν]
    (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x,y) ∂ν ∂μ ∧
    Measurable (fun x => ∫⁻ y, f (x,y) ∂ν) ∧
    Measurable (fun y => ∫⁻ x, f (x,y) ∂μ) :=
  ⟨lintegral_prod f hf.aemeasurable, hf.lintegral_prod_right', hf.lintegral_prod_left'⟩

/-- GP-14: Fubini, including almost-everywhere integrability of both sections. -/
theorem «FIN-EXT025-GP-14-integrable» [SigmaFinite μ] [SigmaFinite ν]
    (f : α × β → ℂ) (hf : Integrable f (μ.prod ν)) :
    (∫ z, f z ∂μ.prod ν) = ∫ x, ∫ y, f (x,y) ∂ν ∂μ ∧
    (∀ᵐ x ∂μ, Integrable (fun y => f (x,y)) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => f (x,y)) μ) :=
  ⟨integral_prod f hf, hf.prod_right_ae, hf.prod_left_ae⟩

/-- GP-14 tensor wrapper: product norms factor whenever the squared densities
are integrable. Spatial/contact constants belong to the consumer's definition. -/
theorem «FIN-EXT025-GP-14-tensor» [SigmaFinite μ] [SigmaFinite ν]
    (f : α → ℝ) (g : β → ℝ) (hf : Integrable f μ) (hg : Integrable g ν) :
    (∫ z, f z.1 * g z.2 ∂μ.prod ν) = (∫ x, f x ∂μ) * (∫ y, g y ∂ν) := by
  rw [integral_prod _ (hf.mul_prod hg)]
  simp_rw [integral_const_mul, integral_mul_const]

/-- GP-11 also explicitly states monotone convergence of the integrals. -/
theorem «FIN-EXT025-GP-11-limit» (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n)) (hm : Monotone f) :
    Monotone (fun n => ∫⁻ x, f n x ∂μ) ∧
      Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, ⨆ n, f n x ∂μ)) := by
  have hi : Monotone (fun n => ∫⁻ x, f n x ∂μ) :=
    fun n m hnm => lintegral_mono (hm hnm)
  rw [«FIN-EXT025-GP-11» f hf hm]
  exact ⟨hi, tendsto_atTop_iSup hi⟩

/-- GP-13 counting-measure wrapper with a fixed summable majorant. -/
theorem «FIN-EXT025-GP-13-Fourier» {ι : Type*} (f : ℕ → ι → ℂ)
    (g : ι → ℂ) (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ n k, ‖f n k‖ ≤ b k)
    (hlim : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) :=
  tendsto_tsum_of_dominated_convergence hb hlim (Filter.Eventually.of_forall hbound)

end QuantumNLS.Ext025BMeasure

#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-11»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-11-counting»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-12»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-12-truncations»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-13»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-13-errors»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-14»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-14-integrable»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-14-tensor»

#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-11-limit»
#print axioms QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-13-Fourier»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025BMeasure." then
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
  Lean.logInfo m!"Ext025BMeasure audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
