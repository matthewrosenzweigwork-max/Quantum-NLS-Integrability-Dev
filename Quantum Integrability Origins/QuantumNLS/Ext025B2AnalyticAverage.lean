import QuantumNLS.Ext025BIntegration
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! GP-16 scalar Taylor coefficient averaging. Only scalar evaluations are
measurable. The averaged multilinear maps are constructed by integrating these
evaluations, then currying the tangent variable. No Bochner measurability into
the normed dual or operator space is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.Ext025B2AnalyticAverage
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [hμ : IsProbabilityMeasure μ]

lemma scalar_integrable {n : ℕ}
    (a : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (D : ℝ) (hm : ∀ v, Measurable (fun x => a x v))
    (hb : ∀ x, ‖a x‖ ≤ D) (v : Fin n → E) :
    Integrable (fun x => a x v) μ := by
  apply Integrable.of_bound (hm v).aestronglyMeasurable (D * ∏ i, ‖v i‖)
  apply Eventually.of_forall
  intro x
  exact (a x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right (hb x) (Finset.prod_nonneg (fun i _ => norm_nonneg (v i))))

/-- Scalar multilinear average, defined from weak scalar measurability. -/
def scalarAverage {n : ℕ}
    (a : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (D : ℝ) (hm : ∀ v, Measurable (fun x => a x v))
    (hb : ∀ x, ‖a x‖ ≤ D) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  MultilinearMap.mkContinuous
    { toFun := fun v => ∫ x, a x v ∂μ
      map_update_add' := fun v i z w => by
        simp_rw [ContinuousMultilinearMap.map_update_add]
        exact integral_add (scalar_integrable μ a D hm hb _) (scalar_integrable μ a D hm hb _)
      map_update_smul' := fun v i c z => by
        simp_rw [ContinuousMultilinearMap.map_update_smul]
        exact integral_smul c _ }
    D (fun v => by
      simpa using norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall (fun x =>
        (a x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hb x)
          (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))))))

theorem norm_scalarAverage_le {n : ℕ}
    (a : X → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hm : ∀ v, Measurable (fun x => a x v))
    (hb : ∀ x, ‖a x‖ ≤ D) : ‖scalarAverage μ a D hm hb‖ ≤ D :=
  MultilinearMap.mkContinuous_norm_le _ hD _

/-- The dual-valued coefficients are actual bounded multilinear maps. -/
def averagedCoefficients
    (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => E) ℝ)
    (D : ℕ → ℝ) (hm : ∀ n v, Measurable (fun x => a n x v))
    (hb : ∀ n x, ‖a n x‖ ≤ D n) : FormalMultilinearSeries ℝ E (E →L[ℝ] ℝ) :=
  fun n => (scalarAverage μ (a n) (D n) (hm n) (hb n)).curryRight

include hμ in
@[simp] theorem averagedCoefficients_apply
    (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => E) ℝ)
    (D : ℕ → ℝ) (hm : ∀ n v, Measurable (fun x => a n x v))
    (hb : ∀ n x, ‖a n x‖ ≤ D n) (n : ℕ) (v : Fin n → E) (w : E) :
    averagedCoefficients μ a D hm hb n v w = ∫ x, a n x (Fin.snoc v w) ∂μ := by
  rw [averagedCoefficients, ContinuousMultilinearMap.curryRight_apply]
  rfl

/-- Uniform scalar coefficient bounds give a positive convergence radius in
the norm of the dual, including when the dual is nonseparable. -/
theorem «FIN-EXT025-GP-16-coefficient-analyticity»
    (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => E) ℝ)
    (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n)
    (hm : ∀ n v, Measurable (fun x => a n x v))
    (hb : ∀ n x, ‖a n x‖ ≤ D n)
    (r : ℝ≥0) (C : ℝ) (hbound : ∀ n, D n * (r : ℝ)^n ≤ C) :
    (r : ℝ≥0∞) ≤ (averagedCoefficients μ a D hm hb).radius ∧
    AnalyticOnNhd ℝ (averagedCoefficients μ a D hm hb).sum (Metric.eball 0 r) := by
  have hr : (r : ℝ≥0∞) ≤ (averagedCoefficients μ a D hm hb).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ C
    intro n
    have hn : ‖averagedCoefficients μ a D hm hb n‖ ≤ D n := by
      rw [averagedCoefficients, ContinuousMultilinearMap.curryRight_norm]
      exact norm_scalarAverage_le μ (a n) (D n) (hD n) (hm n) (hb n)
    exact (mul_le_mul_of_nonneg_right hn (by positivity)).trans (hbound n)
  exact ⟨hr, (averagedCoefficients μ a D hm hb).analyticOnNhd.mono
    (Metric.eball_subset_eball hr)⟩

/-- Scalar Taylor representations identify the constructed dual-valued series
with the original weak scalar average, on every strictly smaller ball. -/
theorem «FIN-EXT025-GP-16-analytic-average»
    (a : ∀ n, X → ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => E) ℝ)
    (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n)
    (hm : ∀ n v, Measurable (fun x => a n x v))
    (hb : ∀ n x, ‖a n x‖ ≤ D n)
    (r : ℝ≥0) (hr : 0 < r) (C : ℝ) (hbound : ∀ n, D n * (r : ℝ)^n ≤ C)
    (F : X → E → E → ℝ)
    (hTaylor : ∀ x z, ‖z‖ < r → ∀ w,
      HasSum (fun n => a n x (Fin.snoc (fun _ => z) w)) (F x z w)) :
    AnalyticOnNhd ℝ (averagedCoefficients μ a D hm hb).sum (Metric.eball 0 r) ∧
    ∀ z : E, ‖z‖ < r → ∀ w : E,
      (averagedCoefficients μ a D hm hb).sum z w = ∫ x, F x z w ∂μ := by
  refine ⟨(«FIN-EXT025-GP-16-coefficient-analyticity» μ a D hD hm hb r C hbound).2, ?_⟩
  intro z hz w
  have hr' : 0 < (r : ℝ) := hr
  have hC : 0 ≤ C := le_trans (by simpa using hD 0) (hbound 0)
  let q : ℝ := ‖z‖ / r
  have hq : |q| < 1 := by
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) r.coe_nonneg)]
    exact (div_lt_one hr').mpr hz
  have hs : Summable (fun n : ℕ => C * q^n * ‖w‖) :=
    ((summable_geometric_of_abs_lt_one hq).mul_left C).mul_right ‖w‖
  have hterm : ∀ n x, ‖a n x (Fin.snoc (fun _ => z) w)‖ ≤ C * q^n * ‖w‖ := by
    intro n x
    have hcoeff : D n * ‖z‖^n ≤ C * q^n := by
      calc
        D n * ‖z‖^n = (D n * (r : ℝ)^n) * q^n := by
          dsimp [q]
          rw [div_pow]
          field_simp [ne_of_gt hr']
        _ ≤ C * q^n := mul_le_mul_of_nonneg_right (hbound n) (by positivity)
    let v : Fin (n+1) → E := Fin.snoc (fun _ : Fin n => z) w
    have hprod : (∏ i, ‖v i‖) = ‖z‖^n * ‖w‖ := by
      dsimp [v]
      rw [Fin.prod_univ_castSucc]
      simp
    change ‖a n x v‖ ≤ C * q^n * ‖w‖
    calc
      ‖a n x v‖ ≤ ‖a n x‖ * ∏ i, ‖v i‖ := (a n x).le_opNorm v
      _ ≤ D n * ∏ i, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (hb n x)
          (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))
      _ = (D n * ‖z‖^n) * ‖w‖ := by rw [hprod]; ring
      _ ≤ C * q^n * ‖w‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  have hi : HasSum (fun n => ∫ x, a n x (Fin.snoc (fun _ => z) w) ∂μ)
      (∫ x, F x z w ∂μ) := by
    apply hasSum_integral_of_dominated_convergence (fun n _ => C * q^n * ‖w‖)
    · intro n
      exact (hm n _).aestronglyMeasurable
    · intro n
      exact Eventually.of_forall (hterm n)
    · exact Eventually.of_forall (fun _ => hs)
    · exact integrable_const _
    · exact Eventually.of_forall (fun x => hTaylor x z hz w)
  let p := averagedCoefficients μ a D hm hb
  have hrad : (r : ℝ≥0∞) ≤ p.radius :=
    («FIN-EXT025-GP-16-coefficient-analyticity» μ a D hD hm hb r C hbound).1
  have hzrad : z ∈ Metric.eball (0 : E) p.radius := by
    apply lt_of_lt_of_le _ hrad
    have hzNN : ‖z‖₊ < r := by exact_mod_cast hz
    simpa only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_eq_nnnorm] using
      (ENNReal.coe_lt_coe.mpr hzNN)
  have hp := p.hasSum hzrad
  have hpw : HasSum (fun n => p n (fun _ => z) w) (p.sum z w) :=
    (ContinuousLinearMap.apply ℝ ℝ w).hasSum hp
  simp only [p, averagedCoefficients_apply] at hpw
  exact hpw.unique hi

end QuantumNLS.Ext025B2AnalyticAverage

#print axioms QuantumNLS.Ext025B2AnalyticAverage.scalar_integrable
#print axioms QuantumNLS.Ext025B2AnalyticAverage.scalarAverage
#print axioms QuantumNLS.Ext025B2AnalyticAverage.norm_scalarAverage_le
#print axioms QuantumNLS.Ext025B2AnalyticAverage.averagedCoefficients
#print axioms QuantumNLS.Ext025B2AnalyticAverage.averagedCoefficients_apply
#print axioms QuantumNLS.Ext025B2AnalyticAverage.«FIN-EXT025-GP-16-coefficient-analyticity»
#print axioms QuantumNLS.Ext025B2AnalyticAverage.«FIN-EXT025-GP-16-analytic-average»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B2AnalyticAverage." then
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
  Lean.logInfo m!"Ext025B2AnalyticAverage audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
