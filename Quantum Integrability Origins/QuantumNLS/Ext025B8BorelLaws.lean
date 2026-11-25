import QuantumNLS.Ext025B8BorelCalculus

/-! GP-08 bounded arbitrary-PVM star calculus and form laws. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B8BorelLaws
open BetheChargeResolution Ext025B6PVM Ext025B8SimpleCalculus Ext025B8BorelCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

theorem approx_bounded (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (x : E) :
    Tendsto (fun n => simple P (approx f hf n) x) atTop (𝓝 (bounded P f hf C hC hb x)) :=
  approx_integral P f hf x _

theorem approx_pointwise (f : ℝ → ℂ) (hf : Measurable f) (t : ℝ) :
    Tendsto (fun n => approx f hf n t) atTop (𝓝 (f t)) :=
  SimpleFunc.tendsto_approxOn hf (s := Set.range f ∪ {0}) (by simp)
    (subset_closure (Set.mem_union_left _ ⟨t,rfl⟩))

theorem bounded_commutes (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) : Ext025B7PVMForms.Commutes P (bounded P f hf C hC hb) := by
  intro s hs
  apply ContinuousLinearMap.ext
  intro x
  change bounded P f hf C hC hb (P.toFun s x) = P.toFun s (bounded P f hf C hC hb x)
  have hl := approx_bounded P f hf C hC hb (P.toFun s x)
  have hr := (P.toFun s).continuous.continuousAt.tendsto.comp (approx_bounded P f hf C hC hb x)
  apply tendsto_nhds_unique hl
  convert hr using 1
  ext n
  exact congrArg (fun T : E →L[ℂ] E => T x) (simple_commutes P (approx f hf n) s hs).eq

/-- First multiply a constructed finite integral and a constructed Borel integral. -/
theorem simple_bounded_mul (f : SimpleFunc ℝ ℂ) (g : ℝ → ℂ) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) :
    bounded P (fun t => f t*g t) (f.measurable.mul hg) (C*D) (mul_nonneg hC hD)
      (fun t => by rw [norm_mul]; exact mul_le_mul (hb t) (hc t) (norm_nonneg _) hC) =
      simple P f*bounded P g hg D hD hc := by
  apply ContinuousLinearMap.ext
  intro x
  change _ = simple P f (bounded P g hg D hD hc x)
  have hl := bounded_strong P (fun n => fun t => f t*approx g hg n t)
    (fun t => f t*g t) (fun n => f.measurable.mul (approx g hg n).measurable)
    (f.measurable.mul hg) (C*D) (mul_nonneg hC hD)
    (fun n t => by rw [norm_mul]; exact mul_le_mul (hb t) (approx_bound g hg D hD hc n t) (norm_nonneg _) hC)
    (fun t => by rw [norm_mul]; exact mul_le_mul (hb t) (hc t) (norm_nonneg _) hC)
    (fun t => tendsto_const_nhds.mul (approx_pointwise g hg t)) x
  have hr := (simple P f).continuous.continuousAt.tendsto.comp (approx_bounded P g hg D hD hc x)
  apply tendsto_nhds_unique hl
  convert hr using 1
  ext n
  have he := bounded_simple P (f*approx g hg n) (C*D) (mul_nonneg hC hD)
    (fun t => by
      change ‖f t*approx g hg n t‖ ≤ C*D
      rw [norm_mul]
      exact mul_le_mul (hb t) (approx_bound g hg D hD hc n t) (norm_nonneg _) hC)
  change bounded P (fun t => f t*approx g hg n t) _ _ _ _ x = simple P f (simple P (approx g hg n) x)
  simp only [SimpleFunc.coe_mul] at he
  calc
    _ = simple P (f*approx g hg n) x := congrArg (fun T : E →L[ℂ] E => T x) he
    _ = _ := by rw [simple_mul]; rfl

/-- Multiplicativity for two arbitrary bounded Borel symbols. -/
theorem bounded_mul (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) :
    bounded P (f*g) (hf.mul hg) (C*D) (mul_nonneg hC hD)
      (fun t => by change ‖f t*g t‖ ≤ _; rw [norm_mul]; exact mul_le_mul (hb t) (hc t) (norm_nonneg _) hC) =
      bounded P f hf C hC hb*bounded P g hg D hD hc := by
  apply ContinuousLinearMap.ext
  intro x
  change _ = bounded P f hf C hC hb (bounded P g hg D hD hc x)
  have hl := bounded_strong P (fun n => fun t => approx f hf n t*g t)
    (f*g) (fun n => (approx f hf n).measurable.mul hg) (hf.mul hg)
    (C*D) (mul_nonneg hC hD)
    (fun n t => by rw [norm_mul]; exact mul_le_mul (approx_bound f hf C hC hb n t) (hc t) (norm_nonneg _) hC)
    (fun t => by change ‖f t*g t‖ ≤ _; rw [norm_mul]; exact mul_le_mul (hb t) (hc t) (norm_nonneg _) hC)
    (fun t => (approx_pointwise f hf t).mul_const (g t)) x
  have hr := approx_bounded P f hf C hC hb (bounded P g hg D hD hc x)
  apply tendsto_nhds_unique hl
  convert hr using 1
  ext n
  rw [simple_bounded_mul P (approx f hf n) g hg C D hC hD (approx_bound f hf C hC hb n) hc]
  rfl

/-- Complex adjoints follow by limits of the finite spectral pairing identities. -/
theorem bounded_star (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) :
    (bounded P f hf C hC hb).adjoint =
      bounded P (fun t => star (f t)) (continuous_star.measurable.comp hf) C hC (fun t => by simpa only [norm_star] using hb t) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hl := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := x)) (approx_bounded P f hf C hC hb y)
  have hr := (bounded_strong P (fun n => fun t => star (approx f hf n t))
    (fun t => star (f t)) (fun n => (continuous_star.measurable.comp (approx f hf n).measurable)) (continuous_star.measurable.comp hf)
    C hC (fun n t => by simpa only [norm_star] using approx_bound f hf C hC hb n t)
    (fun t => by simpa only [norm_star] using hb t)
    (fun t => continuous_star.continuousAt.tendsto.comp (approx_pointwise f hf t)) x).inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))
  apply tendsto_nhds_unique hl
  convert hr using 1
  ext n
  have he := bounded_simple P ((approx f hf n).map star) C hC
    (fun t => by simpa only [SimpleFunc.map_apply,norm_star] using approx_bound f hf C hC hb n t)
  simp only [SimpleFunc.coe_map,Function.comp_def] at he
  rw [he,← simple_star,ContinuousLinearMap.adjoint_inner_left]

/-- The form law is now applied to a constructed Borel operator. -/
theorem bounded_form_domain (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (w : ℝ → ℝ≥0∞) (x : E)
    (hx : Ext025B7PVMForms.FormDomain P w x) :
    Ext025B7PVMForms.FormDomain P w (bounded P f hf C hC hb x) :=
  Ext025B7PVMForms.bounded_form_domain P _ (bounded_commutes P f hf C hC hb) w x hx

theorem phase_norm (f : ℝ → ℂ) (hf : Measurable f) (hp : ∀ t, ‖f t‖ = 1) (x : E) :
    ‖bounded P f hf 1 zero_le_one (fun t => (hp t).le) x‖ = ‖x‖ := by
  have hs := vectorIntegral_square P f x
    (MemLp.of_bound hf.aestronglyMeasurable 1 (.of_forall fun t => (hp t).le))
  change ‖bounded P f hf 1 zero_le_one (fun t => (hp t).le) x‖^2 = _ at hs
  have hi : (∫ t, ‖f t‖^2 ∂scalarMeasure P x) = ‖x‖^2 := by
    calc
      _ = ∫ _ : ℝ, (1 : ℝ) ∂scalarMeasure P x :=
        integral_congr_ae (.of_forall fun t => by rw [hp t,one_pow])
      _ = _ := by simp [measureReal_def,scalarMeasure_univ]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hs.trans hi)

/-- A modulus-one Borel phase is a constructed isometry. -/
def phaseIsometry (f : ℝ → ℂ) (hf : Measurable f) (hp : ∀ t, ‖f t‖ = 1) : E →ₗᵢ[ℂ] E :=
  { (bounded P f hf 1 zero_le_one (fun t => (hp t).le)).toLinearMap with
    norm_map' := phase_norm P f hf hp }

/-- Exact extended form-energy conservation; no unbounded multiplier
preservation is inferred from this bounded phase law. -/
theorem phase_energy (f : ℝ → ℂ) (hf : Measurable f) (hp : ∀ t, ‖f t‖ = 1)
    (w : ℝ → ℝ≥0∞) (x : E) :
    Ext025B7PVMForms.energy P w (phaseIsometry P f hf hp x) = Ext025B7PVMForms.energy P w x := by
  apply Ext025B7PVMForms.isometry_energy
  intro s hs y
  exact congrArg (fun T : E →L[ℂ] E => T y)
    (bounded_commutes P f hf 1 zero_le_one (fun t => (hp t).le) s hs).eq

theorem phase_form_domain_iff (f : ℝ → ℂ) (hf : Measurable f) (hp : ∀ t, ‖f t‖ = 1)
    (w : ℝ → ℝ≥0∞) (x : E) :
    Ext025B7PVMForms.FormDomain P w (phaseIsometry P f hf hp x) ↔ Ext025B7PVMForms.FormDomain P w x := by
  simp only [Ext025B7PVMForms.FormDomain,phase_energy]

end QuantumNLS.Ext025B8BorelLaws

#print axioms QuantumNLS.Ext025B8BorelLaws.approx_bounded
#print axioms QuantumNLS.Ext025B8BorelLaws.approx_pointwise
#print axioms QuantumNLS.Ext025B8BorelLaws.bounded_commutes
#print axioms QuantumNLS.Ext025B8BorelLaws.simple_bounded_mul
#print axioms QuantumNLS.Ext025B8BorelLaws.bounded_mul
#print axioms QuantumNLS.Ext025B8BorelLaws.bounded_star
#print axioms QuantumNLS.Ext025B8BorelLaws.bounded_form_domain
#print axioms QuantumNLS.Ext025B8BorelLaws.phase_norm
#print axioms QuantumNLS.Ext025B8BorelLaws.phaseIsometry
#print axioms QuantumNLS.Ext025B8BorelLaws.phase_energy
#print axioms QuantumNLS.Ext025B8BorelLaws.phase_form_domain_iff

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B8BorelLaws." then
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
  Lean.logInfo m!"Ext025B8BorelLaws audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
