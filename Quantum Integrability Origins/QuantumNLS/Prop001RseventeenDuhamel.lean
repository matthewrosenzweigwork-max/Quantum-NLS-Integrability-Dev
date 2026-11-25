import QuantumNLS.Prop001RsixteenDuhamel
import QuantumNLS.Prop001RfourteenIdentification
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Actual Bochner Duhamel formulas. Measurability follows from the proved
ordinary derivative; integrability follows from the proved uniform trace bound.
No integrability, hierarchy equation, or propagation estimate is assumed. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
open Filter Topology MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RseventeenDuhamel
open TraceClass TraceIdeal TensorCarrier Prop001 Prop001RthirteenSeries
  Prop001RfifteenRemainder Prop001RsixteenHierarchy Prop001RsixteenDuhamel
  Prop001RfourteenIdentification Prop001RsixteenSeries
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : NormedSpace ℝ (E →L[ℂ] E) := NormedSpace.restrictScalars ℝ ℂ (E →L[ℂ] E)

/-- A globally bounded actual derivative is integrable on every finite interval,
even when the ambient Hilbert space is not separable. -/
theorem bounded_derivative_integrable (F V : ℝ → E →L[ℂ] E) (B : ℝ)
    (h : ∀ t,HasDerivAt F (V t) t) (hB : 0 ≤ B)
    (hb : ∀ t,traceNorm (V t) ≤ ENNReal.ofReal B) (a b : ℝ) :
    IntervalIntegrable V volume a b := by
  have heq : V = deriv F := funext (fun t => (h t).deriv.symm)
  have hm : StronglyMeasurable V := heq ▸ stronglyMeasurable_deriv F
  apply (intervalIntegrable_const (c := B)).mono_fun' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t =>
    (ENNReal.ofReal_le_ofReal_iff hB).mp ((norm_le_traceNorm _).trans (hb t)))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Literal positive-rank right-hand side of the finite source hierarchy. -/
def finiteVelocity (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) : RankOperator H (k+1) :=
  (-Complex.I) • (collisionSeries D.A
    (fun j => extendedMarginal D.A ((k+1)+m) j t ψ)
    (extendedMarginal_isTraceClass D.A D.selfAdjoint ((k+1)+m) t ψ hψ) k+
    finiteCorrection D k m ψ hψ t)

def finiteBudget (D : ClassicalData H) (k m : ℕ) : ℝ :=
  2*((k+1 : ℕ) : ℝ)*(∑' n,((n+1 : ℕ) : ℝ)*‖D.A n‖)+
    errorSum D.A*((k+1 : ℕ) : ℝ)^2/((k+1)+m)

theorem finiteBudget_nonneg (D : ClassicalData H) (k m : ℕ) :
    0 ≤ finiteBudget D k m := by
  unfold finiteBudget
  have hc := errorSum_nonneg D.A
  have hs : 0 ≤ ∑' n,((n+1 : ℕ) : ℝ)*‖D.A n‖ := tsum_nonneg (fun _ => by positivity)
  positivity

theorem finiteVelocity_bound (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) :
    traceNorm (finiteVelocity D k m ψ hψ t) ≤ ENNReal.ofReal (finiteBudget D k m) := by
  have hc := (collisionSeries_converges D.A D.cubic
    (fun j => extendedMarginal D.A ((k+1)+m) j t ψ)
    (extendedMarginal_isTraceClass D.A D.selfAdjoint ((k+1)+m) t ψ hψ)
    1 zero_le_one (fun j => by simpa using
      extendedMarginal_traceNorm_le D.A D.selfAdjoint ((k+1)+m) t ψ hψ j) k).2.1
  simp only [mul_one] at hc
  have hr := finiteCorrection_bound_positive D k m ψ hψ t
  unfold finiteVelocity
  simp only [traceNorm_smul,norm_neg,Complex.norm_I,ENNReal.ofReal_one,one_mul]
  exact (traceNorm_add_le _ _).trans ((add_le_add hc hr).trans_eq
    (ENNReal.ofReal_add (by positivity) (by
      exact div_nonneg (mul_nonneg (errorSum_nonneg D.A) (sq_nonneg _)) (by positivity))).symm)

theorem finiteVelocity_integrable (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (a b : ℝ) :
    IntervalIntegrable (finiteVelocity D k m ψ hψ) volume a b :=
  bounded_derivative_integrable _ _ (finiteBudget D k m)
    (finite_marginal_hasDerivAt D k m ψ hψ) (finiteBudget_nonneg D k m)
    (finiteVelocity_bound D k m ψ hψ) a b

/-- Actual finite-marginal Duhamel formula, at arbitrary real endpoints. -/
theorem finite_marginal_Duhamel (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (a b : ℝ) :
    marginal D.A ((k+1)+m) (k+1) (by omega) b ψ-
      marginal D.A ((k+1)+m) (k+1) (by omega) a ψ =
        ∫ t in a..b,finiteVelocity D k m ψ hψ t :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => finite_marginal_hasDerivAt D k m ψ hψ t)
    (finiteVelocity_integrable D k m ψ hψ a b)).symm

/-- Literal product-hierarchy right-hand side. -/
def productVelocity (D : ClassicalData H) (u : Sphere H) (k : ℕ) (t : ℝ) :
    RankOperator H (k+1) :=
  (-Complex.I) • collisionSeries D.A
    (fun j => coherentProjector j (trajectory D u t))
    (coherent_isTraceClass _ ((trajectory_spec D u).2.2.1 t).1) k

theorem productVelocity_hasDerivAt (D : ClassicalData H) (u : Sphere H) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s => coherentProjector (k+1) (trajectory D u s))
      (productVelocity D u k t) t :=
  hasDerivAt_of_trace_derivative _ _ t (trajectory_collision_derivative D u k t)

theorem productVelocity_bound (D : ClassicalData H) (u : Sphere H) (k : ℕ) (t : ℝ) :
    traceNorm (productVelocity D u k t) ≤
      ENNReal.ofReal (2*((k+1 : ℕ) : ℝ)*(∑' n,((n+1 : ℕ) : ℝ)*‖D.A n‖)) := by
  unfold productVelocity
  simp only [traceNorm_smul,norm_neg,Complex.norm_I,ENNReal.ofReal_one,one_mul]
  have hc := (collisionSeries_converges D.A D.cubic
    (fun j => coherentProjector j (trajectory D u t))
    (coherent_isTraceClass _ ((trajectory_spec D u).2.2.1 t).1)
    1 zero_le_one (fun j => by
      rw [coherentProjector_traceNorm j _ ((trajectory_spec D u).2.2.1 t).1];norm_num) k).2.1
  simpa only [mul_one] using hc

theorem productVelocity_integrable (D : ClassicalData H) (u : Sphere H) (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (productVelocity D u k) volume a b :=
  bounded_derivative_integrable _ _ _ (productVelocity_hasDerivAt D u k)
    (by positivity) (productVelocity_bound D u k) a b

/-- Actual product-hierarchy Duhamel formula, at arbitrary real endpoints. -/
theorem product_Duhamel (D : ClassicalData H) (u : Sphere H) (k : ℕ) (a b : ℝ) :
    coherentProjector (k+1) (trajectory D u b)-coherentProjector (k+1) (trajectory D u a) =
      ∫ t in a..b,productVelocity D u k t :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => productVelocity_hasDerivAt D u k t)
    (productVelocity_integrable D u k a b)).symm

end QuantumNLS.Prop001RseventeenDuhamel

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RseventeenDuhamel" then
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
  Lean.logInfo m!"Prop001RseventeenDuhamel audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."





#print axioms QuantumNLS.Prop001RseventeenDuhamel.bounded_derivative_integrable
#print axioms QuantumNLS.Prop001RseventeenDuhamel.finiteVelocity
#print axioms QuantumNLS.Prop001RseventeenDuhamel.finiteBudget
#print axioms QuantumNLS.Prop001RseventeenDuhamel.finiteBudget_nonneg
#print axioms QuantumNLS.Prop001RseventeenDuhamel.finiteVelocity_bound
#print axioms QuantumNLS.Prop001RseventeenDuhamel.finiteVelocity_integrable
#print axioms QuantumNLS.Prop001RseventeenDuhamel.finite_marginal_Duhamel
#print axioms QuantumNLS.Prop001RseventeenDuhamel.productVelocity
#print axioms QuantumNLS.Prop001RseventeenDuhamel.productVelocity_hasDerivAt
#print axioms QuantumNLS.Prop001RseventeenDuhamel.productVelocity_bound
#print axioms QuantumNLS.Prop001RseventeenDuhamel.productVelocity_integrable
#print axioms QuantumNLS.Prop001RseventeenDuhamel.product_Duhamel
