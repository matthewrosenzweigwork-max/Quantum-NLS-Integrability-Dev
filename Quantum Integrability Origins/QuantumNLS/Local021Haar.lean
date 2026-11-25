import Mathlib
import QuantumNLS.LOCAL017HaarPath
import QuantumNLS.Local021Mono

/-!
# LOCAL-021, stage 2: the scalar Haar primitive is equivariant

Source: `local_covariance.tex:166-172`: "Conjugating a diagonal rotation by `U` permutes its angle sequence, and also changes its sign in the
antiunitary case.  These transformations preserve product Lebesgue measure on `[-π,π]^ℤ`.  Changing variables in the scalar path integral
defining `f` gives `f(Uz) = ε f(z)`."

`primitive_equivariant`: if `β_{Uy}(Uh) = ε β_y(h)` on `B_R` (`β` continuous there) then the LOCAL-017 Haar primitive
`f = LOCAL017Haar.primitive β` satisfies `f(Uz) = ε f(z)` on `B_R`.  The measure invariance is proved for the literal
`LOCAL017Haar.pathMeasure` (`pathMeasure_map_Tpath`): the angle permutation / sign change of the principal-angle cube preserves it;
the single seam (`arg = π`, a `productCircleHaar`-null set) is handled by `seam_ae`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
noncomputable section

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory

namespace QuantumNLS.Local021

open QuantumNLS.Ext025B7LocalPath QuantumNLS.LOCAL017Haar QuantumNLS.Ext025BHaar

theorem nebot_circle : (𝓝[≠] (1 : Circle)).NeBot := by
  have h : Tendsto (fun n : ℕ => Circle.exp (1 / ((n : ℝ) + 1))) atTop (𝓝[≠] (1 : Circle)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have := (Circle.exp.continuous.tendsto 0).comp h1
      simpa only [Function.comp_def, Circle.exp_zero] using this
    · refine Eventually.of_forall fun n => ?_
      intro h
      rw [Set.mem_singleton_iff, Circle.exp_eq_one] at h
      obtain ⟨k, hk⟩ := h
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hπ := Real.pi_gt_three
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk0
        nlinarith
      · subst hk0; simp at hk; linarith
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
        nlinarith
  exact h.neBot

theorem circle_singleton_null (x : Circle) : (normalizedHaar : Measure Circle) {x} = 0 := by
  have := nebot_circle
  exact measure_singleton x

/-- The seam of the principal angle. -/
theorem seam_ae : ∀ᵐ ψ ∂(productCircleHaar), ∀ m : ℤ, Complex.arg (ψ m : ℂ) ≠ Real.pi := by
  rw [ae_all_iff]
  intro m
  have h0 : productCircleHaar {ψ : Torus | Complex.arg (ψ m : ℂ) = Real.pi} = 0 := by
    have hsub : {ψ : Torus | Complex.arg (ψ m : ℂ) = Real.pi} ⊆
        (fun ψ : Torus => ψ m) ⁻¹' {Circle.exp Real.pi} := by
      intro ψ hψ
      simp only [mem_setOf_eq] at hψ
      simp only [mem_preimage, mem_singleton_iff]
      have h1 := Complex.arg_eq_pi_iff.1 hψ
      have h2 : ‖(ψ m : ℂ)‖ = 1 := Circle.norm_coe _
      have h3 : (ψ m : ℂ) = -1 := by
        apply Complex.ext
        · have : (ψ m : ℂ).re ^ 2 + (ψ m : ℂ).im ^ 2 = 1 := by
            have := Complex.sq_norm (ψ m : ℂ)
            rw [h2, Complex.normSq_apply] at this; nlinarith
          rw [h1.2] at this
          have : (ψ m : ℂ).re = -1 ∨ (ψ m : ℂ).re = 1 := by
            have : ((ψ m : ℂ).re + 1) * ((ψ m : ℂ).re - 1) = 0 := by nlinarith
            rcases mul_eq_zero.1 this with h | h
            · left; linarith
            · right; linarith
          rcases this with h | h
          · simpa using h
          · linarith [h1.1]
        · simpa using h1.2
      apply Circle.ext
      rw [h3]; simp
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply (measurable_pi_apply m) (measurableSet_singleton _)]
    show ((Measure.infinitePi fun _ : ℤ => (normalizedHaar : Measure Circle)).map (fun ψ => ψ m)) _ = 0
    rw [Measure.infinitePi_map_eval]
    exact circle_singleton_null _
  exact measure_eq_zero_iff_ae_notMem.1 h0

/-! ### the torus, angle and path maps attached to a monomial operator -/

/-- `ψ ↦ s(ψ ∘ σ)` on the torus. -/
def Ttor (U : Mono) (ψ : Torus) : Torus := fun m => if U.anti then (ψ (U.σ m))⁻¹ else ψ (U.σ m)

theorem measurable_Ttor (U : Mono) : Measurable (Ttor U) := by
  refine measurable_pi_iff.2 fun m => ?_
  unfold Ttor
  split_ifs
  · exact (measurable_pi_apply (U.σ m)).inv
  · exact measurable_pi_apply (U.σ m)

theorem Ttor_mp (U : Mono) : MeasurePreserving (Ttor U) productCircleHaar productCircleHaar := by
  have hperm : MeasurePreserving (fun ψ : Torus => fun m => ψ (U.σ m)) productCircleHaar productCircleHaar := by
    refine ⟨measurable_pi_iff.2 fun m => measurable_pi_apply (U.σ m), ?_⟩
    have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => (normalizedHaar : Measure Circle))
      (X := fun _ : ℤ => Circle) U.σ.symm
    have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => Circle) U.σ.symm) =
        fun (ψ : Torus) (m : ℤ) => ψ (U.σ m) := by
      funext ψ m
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
      simp
    rw [hfun] at h
    exact h
  unfold Ttor
  by_cases hA : U.anti
  · simp only [hA, if_true]
    have hinv : MeasurePreserving (fun ψ : Torus => fun m => (ψ m)⁻¹) productCircleHaar productCircleHaar := by
      refine ⟨measurable_pi_iff.2 fun m => (measurable_pi_apply m).inv, ?_⟩
      have h := Measure.infinitePi_map_pi (μ := fun _ : ℤ => (normalizedHaar : Measure Circle))
        (f := fun (_ : ℤ) (w : Circle) => w⁻¹) (fun _ => measurable_inv)
      have h2 : (normalizedHaar : Measure Circle).map (fun w : Circle => w⁻¹) = normalizedHaar :=
        (Measure.measurePreserving_inv (normalizedHaar : Measure Circle)).map_eq
      simp only [h2] at h
      exact h
    exact hinv.comp hperm
  · simp only [hA, if_false]
    exact hperm

theorem abs_eps (U : Mono) : |U.eps| = 1 := by
  unfold Mono.eps; split_ifs <;> simp

/-- the angle-cube map `θ ↦ ε θ∘σ`. -/
def Tang (U : Mono) (θ : AngleBox) : AngleBox := fun m =>
  ⟨U.eps * (θ (U.σ m)).val, by
    have h := (θ (U.σ m)).property
    have h1 := abs_eps U
    rw [Set.mem_Icc]
    have : |U.eps * (θ (U.σ m)).val| ≤ Real.pi := by
      rw [abs_mul, h1, one_mul]; exact abs_le.mpr h
    exact abs_le.mp this⟩

def Tpath (U : Mono) (p : PathParameter) : PathParameter := (Tang U p.1, p.2)

theorem measurable_Tang (U : Mono) : Measurable (Tang U) := by
  refine measurable_pi_iff.2 fun m => ?_
  refine Measurable.subtype_mk ?_
  exact (measurable_subtype_coe.comp (measurable_pi_apply (U.σ m))).const_mul _

theorem measurable_Tpath (U : Mono) : Measurable (Tpath U) :=
  ((measurable_Tang U).comp measurable_fst).prodMk measurable_snd

theorem angleLift_Ttor (U : Mono) {ψ : Torus} (h : ∀ m : ℤ, Complex.arg (ψ m : ℂ) ≠ Real.pi) :
    angleLift (Ttor U ψ) = Tang U (angleLift ψ) := by
  funext m
  apply Subtype.ext
  show Complex.arg ((Ttor U ψ m : Circle) : ℂ) = U.eps * Complex.arg (ψ (U.σ m) : ℂ)
  unfold Ttor Mono.eps
  cases hA : U.anti
  · simp
  · simp only [if_true]
    rw [Circle.coe_inv_eq_conj, Complex.arg_conj, if_neg (h (U.σ m))]; ring

theorem pathMeasure_map_Tpath (U : Mono) : pathMeasure.map (Tpath U) = pathMeasure := by
  have hm1 : Measurable (Prod.map (Ttor U) (id : unitInterval → unitInterval)) :=
    ((measurable_Ttor U).comp measurable_fst).prodMk measurable_snd
  unfold pathMeasure
  rw [Measure.map_map (measurable_Tpath U) pathLift_measurable]
  have hae : (Tpath U ∘ pathLift) =ᵐ[productCircleHaar.prod (volume : Measure unitInterval)]
      (pathLift ∘ Prod.map (Ttor U) id) := by
    have h1 : ∀ᵐ p ∂(productCircleHaar.prod (volume : Measure unitInterval)),
        ∀ m : ℤ, Complex.arg ((p.1 m : Circle) : ℂ) ≠ Real.pi :=
      Measure.quasiMeasurePreserving_fst.ae seam_ae
    filter_upwards [h1] with p hp
    simp only [Function.comp, pathLift, Tpath, Prod.map]
    rw [angleLift_Ttor U hp]; rfl
  rw [Measure.map_congr hae, ← Measure.map_map pathLift_measurable hm1,
    ← Measure.map_prod_map _ _ (measurable_Ttor U) measurable_id, (Ttor_mp U).map_eq, Measure.map_id]

/-! ### pointwise intertwining of rotation and velocity -/

theorem cj_exp (U : Mono) (x : ℝ) :
    U.cj (Complex.exp (((U.eps * x : ℝ) : ℂ) * Complex.I)) = Complex.exp ((x : ℂ) * Complex.I) := by
  unfold Mono.cj Mono.eps
  split_ifs
  · rw [← Complex.exp_conj]; simp
  · simp

theorem rotation_act (U : Mono) (p : PathParameter) (z : H) :
    rotation p (U.act z) = U.act (rotation (Tpath U p) z) := by
  refine lp.ext (funext fun n => ?_)
  show (rotationAngles p n : ℂ) * (U.c n * U.cj (z (U.σ.symm n))) =
    U.c n * U.cj ((rotationAngles (Tpath U p) (U.σ.symm n) : ℂ) * z (U.σ.symm n))
  rw [Mono.cj_mul]
  have : U.cj ((rotationAngles (Tpath U p) (U.σ.symm n) : ℂ)) = (rotationAngles p n : ℂ) := by
    simp only [rotationAngles, Tpath, Tang, Circle.coe_exp, Equiv.apply_symm_apply]
    have := cj_exp U ((p.2 : ℝ) * (p.1 n).val)
    rw [show ((p.2 : ℝ) * (U.eps * (p.1 n).val) : ℝ) = U.eps * ((p.2 : ℝ) * (p.1 n).val) by ring]
    simpa using this
  rw [this]; ring

theorem velocity_act (U : Mono) (θ : AngleBox) (w : H) :
    velocity θ (U.act w) = U.act (velocity (Tang U θ) w) := by
  refine lp.ext (funext fun n => ?_)
  show Complex.I * (((θ n).val : ℝ) : ℂ) * (U.c n * U.cj (w (U.σ.symm n))) =
    U.c n * U.cj (Complex.I * (((Tang U θ (U.σ.symm n)).val : ℝ) : ℂ) * w (U.σ.symm n))
  have e : (((Tang U θ (U.σ.symm n)).val : ℝ) : ℂ) = (U.eps : ℂ) * ((θ n).val : ℂ) := by
    simp [Tang]
  rw [e, show Complex.I * ((U.eps : ℂ) * ((θ n).val : ℂ)) * w (U.σ.symm n) =
      Complex.I * ((((U.eps * (θ n).val : ℝ)) : ℂ) * w (U.σ.symm n)) by push_cast; ring,
    Mono.cj_I, Mono.cj_real]
  have h2 : (U.eps : ℂ) * (U.eps : ℂ) = 1 := by exact_mod_cast U.eps_sq
  push_cast
  linear_combination (-(((θ n).val : ℂ) * Complex.I * U.c n * U.cj (w (U.σ.symm n)))) * h2

theorem pathIntegrand_act (U : Mono) (β : H → Cov) {R : ℝ}
    (hβ : ∀ y ∈ ball (0 : H) R, ∀ h, β (U.act y) (U.act h) = U.eps * β y h) {z : H}
    (hz : z ∈ ball (0 : H) R) (p : PathParameter) :
    pathIntegrand β (U.act z) p = U.eps * pathIntegrand β z (Tpath U p) := by
  unfold pathIntegrand
  rw [rotation_act, velocity_act]
  exact hβ _ (rotation_mem hz _) _

theorem primitive_equivariant (U : Mono) (β : H → Cov) {R : ℝ}
    (hβc : ContinuousOn β (ball (0 : H) R))
    (hβ : ∀ y ∈ ball (0 : H) R, ∀ h, β (U.act y) (U.act h) = U.eps * β y h) {z : H}
    (hz : z ∈ ball (0 : H) R) :
    primitive β (U.act z) = U.eps * primitive β z := by
  unfold primitive
  have h1 : ∫ p, pathIntegrand β (U.act z) p ∂pathMeasure =
      U.eps * ∫ p, pathIntegrand β z (Tpath U p) ∂pathMeasure := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun p => pathIntegrand_act U β hβ hz p)
  have h2 : ∫ p, pathIntegrand β z (Tpath U p) ∂pathMeasure = ∫ p, pathIntegrand β z p ∂pathMeasure := by
    have hmeas : AEStronglyMeasurable (pathIntegrand β z) (pathMeasure.map (Tpath U)) := by
      rw [pathMeasure_map_Tpath]
      exact (path_continuousOn β hβc hz).aestronglyMeasurable
    rw [← integral_map (measurable_Tpath U).aemeasurable hmeas, pathMeasure_map_Tpath]
  rw [h1, h2]; ring

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.pathMeasure_map_Tpath
#print axioms QuantumNLS.Local021.primitive_equivariant
