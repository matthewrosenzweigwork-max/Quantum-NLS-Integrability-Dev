import QuantumNLS.LOCAL017HaarPath
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# `thm:reset-moser` (LOCAL-017): the Haar principal-angle measure IS the source's angle-cube product measure

Source: `symplectic_correction.tex`, "A primitive in all angular directions, with full bounds": "Let `μ` be product normalized Lebesgue measure on `[−π, π]^ℤ`.  For `θ` in this product, let `Θh = (θ_n h_n)_n`
and `R_{tθ} h = (e^{itθ_n} h_n)_n` ... Set `f(z) = −∫∫₀¹ β_{R_{tθ}z}(iΘ R_{tθ} z) dt dμ(θ)`" (eq:reset-haar-primitive).

The frozen sol_ext_b module `LOCAL017HaarPath` defines the primitive through `pathMeasure`, the image of (infinite product Haar measure on `ℤ → Circle`) x (Lebesgue on `[0,1]`) under the principal-angle map `angleLift`.
This module proves (no change of any frozen module):

* `angleLeb` := normalized Lebesgue measure on `[−π, π]` (the measure `(2π)⁻¹ · volume`, on the closed interval as a subtype); `angleCube := infinitePi (fun _ => angleLeb)`, the product normalized Lebesgue measure on `[−π, π]^ℤ`;
* `haar_circle_map_angle` : the one-dimensional core, the image of normalized Haar measure of `Circle` under the principal argument is `angleLeb`  (via `Circle.exp : [−π,π] → Circle` pushes `angleLeb` to Haar, uniqueness of the normalized invariant measure GP-15);
* `map_angleLift` : `angleLift_*(productCircleHaar) = angleCube`;
* `pathMeasure_eq` : `pathMeasure = angleCube ⊗ Lebesgue[0,1]` as measures;
* `primitive_cube` : on a ball where `β` is continuous, `primitive β z = −∫_θ ∫_t β_{R_{tθ}z}(iΘ R_{tθ} z) dt dμ(θ)` with `μ = angleCube` and `R_{tθ}`, `Θ` the literal source operators
  (`Rot_apply`, `velocity_apply`), and `dt` the interval integral over `[0,1]` (`primitive_cube_interval`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace QuantumNLS.LOCAL017Haar
open Ext025B7LocalPath Ext025BHaar

/-- `[−π, π]` as a subtype (the factor of `AngleBox`). -/
abbrev Angle1 := Set.Icc (-Real.pi) Real.pi

/-- Normalized Lebesgue measure on `[−π, π]`: `(2π)⁻¹ · Lebesgue`. -/
def angleLeb : Measure Angle1 :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • Measure.comap (Subtype.val : Angle1 → ℝ) (volume : Measure ℝ)

/-- Product normalized Lebesgue measure on the closed angle cube `[−π, π]^ℤ` (the source's `μ`). -/
def angleCube : Measure AngleBox := Measure.infinitePi (fun _ : ℤ => angleLeb)

theorem comap_univ :
    (Measure.comap (Subtype.val : Angle1 → ℝ) (volume : Measure ℝ)) univ = ENNReal.ofReal (2 * Real.pi) := by
  have h := congrArg (fun m : Measure ℝ => m univ)
    (map_comap_subtype_coe (measurableSet_Icc (a := -Real.pi) (b := Real.pi)) (volume : Measure ℝ))
  simp only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc] at h
  rw [h]
  congr 1
  ring

instance angleLeb_prob : IsProbabilityMeasure angleLeb := by
  refine ⟨?_⟩
  change ((ENNReal.ofReal (2 * Real.pi))⁻¹ • Measure.comap (Subtype.val : Angle1 → ℝ) (volume : Measure ℝ)) univ = 1
  rw [Measure.smul_apply, comap_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top

instance : IsProbabilityMeasure angleCube := by unfold angleCube; infer_instance

/-- Lebesgue measure on `ℝ` restricted to `(−π, π]`, normalized. -/
def lebIoc : Measure ℝ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • (volume : Measure ℝ).restrict (Ioc (-Real.pi) Real.pi)

/-- The one-dimensional core: `θ ↦ e^{iθ}` pushes the normalized Lebesgue measure on `(−π, π]` to normalized Haar measure of the circle. -/
theorem map_exp_lebIoc : Measure.map (fun θ : ℝ => Circle.exp θ) lebIoc = (normalizedHaar : Measure Circle) := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  set e : AddCircle (2 * Real.pi) ≃ₜ Circle := AddCircle.homeomorphCircle' with he
  set μA : Measure (AddCircle (2 * Real.pi)) :=
    (ENNReal.ofReal (2 * Real.pi))⁻¹ • (volume : Measure (AddCircle (2 * Real.pi))) with hμA
  have hmk : Measure.map (((↑) : ℝ → AddCircle (2 * Real.pi))) lebIoc = μA := by
    have h1 := (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).map_eq
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [h2] at h1
    unfold lebIoc
    rw [Measure.map_smul _ (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).measurable.aemeasurable, h1]
  have hexp : (fun θ : ℝ => Circle.exp θ) = e ∘ (((↑) : ℝ → AddCircle (2 * Real.pi))) := by
    funext θ; exact (AddCircle.homeomorphCircle'_apply_mk θ).symm
  have hmeasMk : Measurable (((↑) : ℝ → AddCircle (2 * Real.pi))) := (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).measurable
  have hν : Measure.map (fun θ : ℝ => Circle.exp θ) lebIoc = Measure.map e μA := by
    rw [hexp, ← hmk, Measure.map_map e.continuous.measurable hmeasMk]
  rw [hν]
  have hprobA : IsProbabilityMeasure μA := by
    refine ⟨?_⟩
    rw [hμA, Measure.smul_apply, AddCircle.measure_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top
  haveI : Measure.IsAddLeftInvariant μA := by rw [hμA]; infer_instance
  haveI : IsProbabilityMeasure (Measure.map e μA) :=
    (Measure.isProbabilityMeasure_map_iff (μ := μA) e.continuous.measurable.aemeasurable).2 hprobA
  haveI : Measure.IsMulLeftInvariant (Measure.map e μA) := by
    constructor
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    have hadd : ∀ x : AddCircle (2 * Real.pi), e y * e x = e (y + x) := fun x =>
      (Real.Angle.toCircle_add y x).symm
    have hfun : (fun x : Circle => e y * x) ∘ e = e ∘ (fun x => y + x) := by
      funext x; exact hadd x
    rw [Measure.map_map (measurable_const_mul (e y)) e.continuous.measurable, hfun,
      ← Measure.map_map e.continuous.measurable (measurable_const_add y), map_add_left_eq_self]
  exact («FIN-EXT025-GP-15» (G := Circle)).unique ⟨inferInstance, inferInstance⟩
    ⟨inferInstance, inferInstance⟩

/-- The principal argument, as a map to the closed angle interval. -/
def angleLift1 (w : Circle) : Angle1 := ⟨Complex.arg w, (Complex.abs_arg_le_pi _ |> abs_le.mp)⟩

theorem angleLift1_measurable : Measurable angleLift1 :=
  (Complex.measurable_arg.comp measurable_subtype_coe).subtype_mk

/-- `θ ↦ e^{iθ}` on `[−π, π]`. -/
def expSub (θ : Angle1) : Circle := Circle.exp θ.val

theorem expSub_measurable : Measurable expSub := (Circle.exp.continuous.measurable).comp measurable_subtype_coe

theorem map_expSub : Measure.map expSub angleLeb = (normalizedHaar : Measure Circle) := by
  have hs : MeasurableSet (Icc (-Real.pi) Real.pi) := measurableSet_Icc
  have h1 : Measure.map expSub angleLeb =
      (ENNReal.ofReal (2 * Real.pi))⁻¹ •
        Measure.map (fun θ : ℝ => Circle.exp θ) ((volume : Measure ℝ).restrict (Icc (-Real.pi) Real.pi)) := by
    unfold angleLeb
    rw [Measure.map_smul _ expSub_measurable.aemeasurable]
    congr 1
    have : expSub = (fun θ : ℝ => Circle.exp θ) ∘ (Subtype.val : Angle1 → ℝ) := rfl
    rw [this, ← Measure.map_map Circle.exp.continuous.measurable measurable_subtype_coe,
      map_comap_subtype_coe hs]
  rw [h1, ← map_exp_lebIoc, lebIoc, Measure.map_smul _ Circle.exp.continuous.measurable.aemeasurable]
  congr 2
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]

theorem angleLeb_singleton (a : Angle1) : angleLeb {a} = 0 := by
  unfold angleLeb
  rw [Measure.smul_apply, smul_eq_mul,
    comap_subtype_coe_apply (measurableSet_Icc (a := -Real.pi) (b := Real.pi))]
  simp

/-- The one-dimensional identification: principal angles of Haar measure are normalized Lebesgue on `[−π, π]`. -/
theorem haar_circle_map_angle : Measure.map angleLift1 (normalizedHaar : Measure Circle) = angleLeb := by
  rw [← map_expSub, Measure.map_map angleLift1_measurable expSub_measurable]
  have hae : ∀ᵐ θ ∂angleLeb, θ ∉ ({(⟨-Real.pi, by simp [Real.pi_pos.le]⟩ : Angle1)} : Set Angle1) :=
    measure_eq_zero_iff_ae_notMem.1 (angleLeb_singleton _)
  have hid : (angleLift1 ∘ expSub) =ᵐ[angleLeb] id := by
    filter_upwards [hae] with θ hθ
    have hne : θ.val ≠ -Real.pi := fun h => hθ (by simpa using Subtype.ext h)
    have hlt : -Real.pi < θ.val := lt_of_le_of_ne θ.property.1 (Ne.symm hne)
    apply Subtype.ext
    exact Circle.arg_exp hlt θ.property.2
  rw [Measure.map_congr hid, Measure.map_id]

theorem map_angleLift : Measure.map angleLift (productCircleHaar : Measure (ℤ → Circle)) = angleCube := by
  have hf : ∀ _ : ℤ, Measurable angleLift1 := fun _ => angleLift1_measurable
  have := Measure.infinitePi_map_pi (μ := fun _ : ℤ => (normalizedHaar : Measure Circle)) (f := fun _ => angleLift1) hf
  unfold productCircleHaar angleCube
  have hl : (angleLift : (ℤ → Circle) → AngleBox) = fun x i => angleLift1 (x i) := rfl
  rw [hl, this]
  simp only [haar_circle_map_angle]

/-- The Haar path measure is the product of the source's angle-cube measure and Lebesgue measure on `[0,1]`. -/
theorem pathMeasure_eq : pathMeasure = angleCube.prod (volume : Measure unitInterval) := by
  unfold pathMeasure
  have hp : pathLift = Prod.map angleLift (id : unitInterval → unitInterval) := rfl
  rw [hp, ← Measure.map_prod_map _ _ angleLift_measurable measurable_id, map_angleLift, Measure.map_id]

/-- The literal source rotation `R_{tθ} z = (e^{itθ_n} z_n)_n`, for real `t`. -/
def Rot (θ : AngleBox) (t : ℝ) (z : H) : H := ActionTorus.rotate (fun n => Circle.exp (t * (θ n).val)) z

theorem Rot_apply (θ : AngleBox) (t : ℝ) (z : H) (n : ℤ) :
    Rot θ t z n = Complex.exp (Complex.I * ((t * (θ n).val : ℝ) : ℂ)) * z n := by
  simp only [Rot, ActionTorus.rotate_apply, Circle.coe_exp]
  rw [mul_comm Complex.I]

theorem rotation_eq_Rot (θ : AngleBox) (t : unitInterval) (z : H) : rotation (θ, t) z = Rot θ t.val z := rfl

/-- **The Haar primitive in the source's angle-cube form** (eq:reset-haar-primitive): `f(z) = −∫ ∫ β_{R_{tθ}z}(iΘ R_{tθ}z) dt dμ(θ)`, `μ` product normalized Lebesgue measure on `[−π,π]^ℤ`,
`dt` Lebesgue measure on `[0,1]`. -/
theorem primitive_cube {R : ℝ} (β : H → Cov) (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R) :
    primitive β z = -∫ θ, ∫ t : unitInterval,
      β (Rot θ t.val z) (velocity θ (Rot θ t.val z)) ∂volume ∂angleCube := by
  have h := primitive_haar β hβ hz
  unfold primitive at h ⊢
  have hint : Integrable (pathIntegrand β z) (angleCube.prod (volume : Measure unitInterval)) := by
    rw [← pathMeasure_eq]; exact path_integrable β hβ hz
  congr 1
  rw [pathMeasure_eq]
  exact integral_prod _ hint

/-- The same, with the time integral written as the interval integral over `[0,1]`. -/
theorem primitive_cube_interval {R : ℝ} (β : H → Cov) (hβ : ContinuousOn β (ball 0 R)) {z : H} (hz : z ∈ ball 0 R) :
    primitive β z = -∫ θ, (∫ t in (0 : ℝ)..1,
      β (Rot θ t z) (velocity θ (Rot θ t z))) ∂angleCube := by
  rw [primitive_cube β hβ hz]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact (integral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := (0 : ℝ)) (b := 1))
    (fun t : ℝ => β (Rot θ t z) (velocity θ (Rot θ t z))))

end QuantumNLS.LOCAL017Haar

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.LOCAL017Haar.map_exp_lebIoc
#print axioms QuantumNLS.LOCAL017Haar.haar_circle_map_angle
#print axioms QuantumNLS.LOCAL017Haar.map_angleLift
#print axioms QuantumNLS.LOCAL017Haar.pathMeasure_eq
#print axioms QuantumNLS.LOCAL017Haar.primitive_cube
#print axioms QuantumNLS.LOCAL017Haar.primitive_cube_interval
