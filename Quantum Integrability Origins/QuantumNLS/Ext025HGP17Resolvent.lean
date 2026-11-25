import Mathlib
import QuantumNLS.Ext025HGP17Calculus

/-! # EXT-025 GP-17 operator part, G1 (haiku_inventory, 2026-11-17)

Repaired contract FIN-EXT025-GP-17 (corrected), operator part:
"A resolvent contour integral is an idempotent commuting with the operator."

Operator class (integrator ruling, 2026-11-17): CLOSED operators `T` given through their
resolvent. `T` is a partial linear map `T : E →ₗ.[ℂ] E` (domain `T.domain`) with closed graph.
A `ClosedResolvent T ρ R` is a family `R z`, `z ∈ ρ`, of bounded operators on an open set `ρ`
of the resolvent set, holomorphic on `ρ`, with `R z` mapping into `T.domain`, and with
`R z` the inverse of `z - T`. The resolvent identity is DERIVED from these axioms (not assumed).

Sign convention (recorded correspondence point): this module uses `(z - T) * R z = 1`, i.e.
`R z = (z - T)⁻¹`. With this convention the contour projection
`contourProj R c r = (2πi)⁻¹ • ∮_{|z-c|=r} R z dz` is the Riesz projection, and it is idempotent.
The integrator's stated relation `(T - z) R z = 1` gives `R z = -(z - T)⁻¹`; then the same
formula `(2πi)⁻¹ ∮ R` equals MINUS the Riesz projection and satisfies `P² = -P`, so it is NOT
idempotent. The idempotent claim therefore fixes the sign convention used here.

Main results:
* `contourProj_indep`: independence of the radius on an annulus contained in `ρ`
  (Mathlib Banach-valued Cauchy annulus theorem);
* `contour_projection_G1`: `P = P_{r'}`, `P * P = P`, `P` maps `T.domain` into itself, and
  `T P = P T` on `T.domain`; closedness of `T` is used through the closed graph;
* `contour_projection_bounded`: the bounded case as a corollary (`T : E →L E`, `D(T) = E`).

No `sorry`, no new axioms. Author: haiku_inventory (EXT-025 GP-17 packaging). -/

noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory intervalIntegral Complex Real Function
open QuantumNLS.Ext025HGP17Calculus

namespace QuantumNLS.Ext025HGP17Resolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Contour projection `(2πi)⁻¹ ∮_{|z-c|=r} R z dz` (convention `R z = (z - T)⁻¹`). -/
def contourProj (R : ℂ → E →L[ℂ] E) (c : ℂ) (r : ℝ) : E →L[ℂ] E :=
  (2 * π * Complex.I)⁻¹ • circleIntegral R c r

/-- A closed operator `T` (partial linear map with closed graph) with resolvent family `R` on the
open set `ρ`: `R z` is bounded, holomorphic on `ρ`, maps into `T.domain`, and inverts `z - T`. -/
structure ClosedResolvent (T : E →ₗ.[ℂ] E) (ρ : Set ℂ) (R : ℂ → E →L[ℂ] E) : Prop where
  isOpen : IsOpen ρ
  diff : DifferentiableOn ℂ R ρ
  closed : IsClosed (T.graph : Set (E × E))
  mem_dom : ∀ z ∈ ρ, ∀ v : E, R z v ∈ T.domain
  left : ∀ (z : ℂ) (hz : z ∈ ρ) (v : E), T.toFun ⟨R z v, mem_dom z hz v⟩ = z • R z v - v
  right : ∀ z ∈ ρ, ∀ (x : E) (hx : x ∈ T.domain), R z (T.toFun ⟨x, hx⟩) = z • R z x - x

/-! ## Elementary sphere and integrability lemmas -/

theorem circleMap_mem_sphere_of_pos {c : ℂ} {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    circleMap c r θ ∈ sphere c r := by
  simpa [abs_of_pos hr] using circleMap_mem_sphere' c r θ

theorem circleIntegrable_of_contOn {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : ℂ → G} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : ContinuousOn f (sphere c r)) :
    CircleIntegrable f c r :=
  (hf.comp_continuous (continuous_circleMap c r) (circleMap_mem_sphere_of_pos hr)).intervalIntegrable _ _

theorem sphere_inner_sub {c : ℂ} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    sphere c r₁ ⊆ closedBall c r₂ \ ball c r₁ := by
  intro z hz
  rw [mem_sphere] at hz
  exact ⟨mem_closedBall.2 (hz.le.trans h), fun hb => by rw [mem_ball] at hb; linarith⟩

theorem sphere_outer_sub {c : ℂ} {r₁ r₂ : ℝ} (h : r₁ < r₂) :
    sphere c r₂ ⊆ closedBall c r₂ \ ball c r₁ := by
  intro z hz
  rw [mem_sphere] at hz
  exact ⟨mem_closedBall.2 hz.le, fun hb => by rw [mem_ball] at hb; linarith⟩

theorem radii_sub_ne {c z w : ℂ} {r₁ r₂ : ℝ} (hz : z ∈ sphere c r₁) (hw : w ∈ sphere c r₂)
    (h : r₁ ≠ r₂) : w - z ≠ 0 := by
  intro h0
  rw [sub_eq_zero] at h0
  subst h0
  rw [mem_sphere] at hz hw
  exact h (hz.symm.trans hw)

/-- Joint continuity of the kernel `(w - z)⁻¹ • R w v` on the product of two circles of distinct radii. -/
theorem continuousOn_kernel {c : ℂ} {r₁ r₂ : ℝ} (h : r₁ ≠ r₂) {R : ℂ → E →L[ℂ] E}
    (hR2 : ContinuousOn R (sphere c r₂)) (v : E) :
    ContinuousOn (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹ • R p.2 v) (sphere c r₁ ×ˢ sphere c r₂) := by
  have hne : ∀ p ∈ sphere c r₁ ×ˢ sphere c r₂, p.2 - p.1 ≠ 0 :=
    fun p hp => radii_sub_ne hp.1 hp.2 h
  have hinv : ContinuousOn (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹) (sphere c r₁ ×ˢ sphere c r₂) :=
    ((continuous_snd.sub continuous_fst).continuousOn).inv₀ hne
  have hRv : ContinuousOn (fun p : ℂ × ℂ => R p.2 v) (sphere c r₁ ×ˢ sphere c r₂) :=
    (hR2.comp continuous_snd.continuousOn (fun p hp => hp.2)).clm_apply continuousOn_const
  exact hinv.smul hRv

/-- The circle integral in the outer variable of a kernel-type integrand is integrable. -/
theorem circleIntegrable_inner {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) {g : ℂ → ℂ → H}
    (hg : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (sphere c₁ r₁ ×ˢ sphere c₂ r₂)) :
    CircleIntegrable (fun z => circleIntegral (fun w => g z w) c₂ r₂) c₁ r₁ := by
  have hc1 : Continuous (fun p : ℝ × ℝ => (circleMap c₁ r₁ p.1, circleMap c₂ r₂ p.2)) :=
    ((continuous_circleMap c₁ r₁).comp continuous_fst).prodMk
      ((continuous_circleMap c₂ r₂).comp continuous_snd)
  have hmaps : MapsTo (fun p : ℝ × ℝ => (circleMap c₁ r₁ p.1, circleMap c₂ r₂ p.2))
      univ (sphere c₁ r₁ ×ˢ sphere c₂ r₂) :=
    fun p _ => ⟨circleMap_mem_sphere_of_pos h₁ p.1, circleMap_mem_sphere_of_pos h₂ p.2⟩
  have hgc : Continuous (fun p : ℝ × ℝ => g (circleMap c₁ r₁ p.1) (circleMap c₂ r₂ p.2)) :=
    continuousOn_univ.mp (hg.comp hc1.continuousOn hmaps)
  have hd2 : Continuous (fun p : ℝ × ℝ => deriv (circleMap c₂ r₂) p.2) := by
    simp only [deriv_circleMap]
    fun_prop
  have hpar : Continuous (fun θ₁ : ℝ =>
      ∫ θ₂ in (0 : ℝ)..2 * π, deriv (circleMap c₂ r₂) θ₂ • g (circleMap c₁ r₁ θ₁) (circleMap c₂ r₂ θ₂)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun θ₁ θ₂ =>
      deriv (circleMap c₂ r₂) θ₂ • g (circleMap c₁ r₁ θ₁) (circleMap c₂ r₂ θ₂))
      (hd2.smul hgc) 0 (2 * π)
  unfold CircleIntegrable
  apply Continuous.intervalIntegrable
  unfold circleIntegral
  exact hpar

/-! ## Calculus of `contourProj` -/

/-- Circle integrals of scalar multiples pull the scalar out. -/
theorem circleIntegral_const_smul' {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] (a : ℂ) (f : ℂ → G) (c : ℂ) (r : ℝ) :
    circleIntegral (fun z => a • f z) c r = a • circleIntegral f c r := by
  unfold circleIntegral
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext θ
  rw [smul_comm]

/-- Applying the contour projection to a vector. -/
theorem contourProj_apply {R : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hRc : ContinuousOn R (sphere c r)) (x : E) :
    contourProj R c r x = (2 * π * Complex.I)⁻¹ • circleIntegral (fun z => R z x) c r := by
  unfold contourProj
  rw [ContinuousLinearMap.smul_apply]
  congr 1
  have := circleIntegral_clm_apply (ContinuousLinearMap.apply ℂ E x) hr hRc
  simpa using this

/-- Radius independence on an annulus contained in the resolvent set (Mathlib's Banach-valued
Cauchy annulus theorem). -/
theorem contourProj_indep {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ ≤ r₂)
    (hann : closedBall c r₂ \ ball c r₁ ⊆ ρ) :
    contourProj R c r₁ = contourProj R c r₂ := by
  unfold contourProj
  congr 1
  have hc : ContinuousOn R (closedBall c r₂ \ ball c r₁) := hR.diff.continuousOn.mono hann
  have hd : ∀ z ∈ (ball c r₂ \ closedBall c r₁) \ (∅ : Set ℂ), DifferentiableAt ℂ R z := by
    intro z hz
    have hzann : z ∈ closedBall c r₂ \ ball c r₁ :=
      ⟨ball_subset_closedBall hz.1.1, fun h => hz.1.2 (ball_subset_closedBall h)⟩
    exact hR.diff.differentiableAt (hR.isOpen.mem_nhds (hann hzann))
  exact (circleIntegral_eq_of_differentiable_on_annulus_off_countable h₁ h₁₂
    countable_empty hc hd).symm

/-! ## The resolvent identity (derived from the axioms) -/

theorem resolvent_identity {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {z w : ℂ} (hz : z ∈ ρ) (hw : w ∈ ρ) (u : E) :
    R z u - R w u = (w - z) • R z (R w u) := by
  have h1 := hR.left w hw u
  have h2 := hR.right z hz (R w u) (hR.mem_dom w hw u)
  rw [h1, map_sub, map_smul] at h2
  rw [sub_smul]
  linear_combination (norm := module) -h2

/-! ## Pointwise identity on the inner circle and the vanishing of the cross term -/

/-- For `z` on the inner circle, the outer integral of the resolvent product is `(2πi) R z v`
minus the cross term `J z`. -/
theorem inner_identity {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (h₁₂ : r₁ < r₂)
    (hs2 : sphere c r₂ ⊆ ρ) (v : E) {z : ℂ} (hz : z ∈ sphere c r₁) (hzρ : z ∈ ρ) :
    circleIntegral (fun w => R z (R w v)) c r₂ =
      (2 * π * Complex.I) • R z v - circleIntegral (fun w => (w - z)⁻¹ • R w v) c r₂ := by
  have hne : r₁ ≠ r₂ := h₁₂.ne
  have hzball : z ∈ ball c r₂ := by
    rw [mem_sphere] at hz
    rw [mem_ball]
    linarith
  have hR2 : ContinuousOn R (sphere c r₂) := hR.diff.continuousOn.mono hs2
  have hRv2 : ContinuousOn (fun w => R w v) (sphere c r₂) := hR2.clm_apply continuousOn_const
  have hkey : circleIntegral (fun w => R z (R w v)) c r₂ =
      circleIntegral (fun w => (w - z)⁻¹ • (R z v - R w v)) c r₂ := by
    apply circleIntegral.integral_congr h₂.le
    intro w hw
    have hwz : w - z ≠ 0 := radii_sub_ne hz hw hne
    show R z (R w v) = (w - z)⁻¹ • (R z v - R w v)
    rw [resolvent_identity hR hzρ (hs2 hw) v, smul_smul, inv_mul_cancel₀ hwz, one_smul]
  have hcont_a : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere c r₂) :=
    ((continuous_id.sub continuous_const).continuousOn).inv₀
      (fun w hw => radii_sub_ne hz hw hne)
  have hint_a : CircleIntegrable (fun w => (w - z)⁻¹ • R z v) c r₂ :=
    circleIntegrable_of_contOn h₂ (hcont_a.smul continuousOn_const)
  have hint_b : CircleIntegrable (fun w => (w - z)⁻¹ • R w v) c r₂ :=
    circleIntegrable_of_contOn h₂ (hcont_a.smul hRv2)
  rw [hkey]
  simp only [smul_sub]
  rw [circleIntegral.integral_sub hint_a hint_b, circle_inv_inside hzball (R z v)]

/-- The cross term `∮_z ∮_w (w - z)⁻¹ • R w v` vanishes (Fubini and Cauchy for `w` outside). -/
theorem cross_term_zero {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) (h₁₂ : r₁ < r₂)
    (hs2 : sphere c r₂ ⊆ ρ) (v : E) :
    circleIntegral (fun z => circleIntegral (fun w => (w - z)⁻¹ • R w v) c r₂) c r₁ = 0 := by
  have hne : r₁ ≠ r₂ := h₁₂.ne
  have hR2 : ContinuousOn R (sphere c r₂) := hR.diff.continuousOn.mono hs2
  have hF := circle_fubini (c₁ := c) (c₂ := c) h₁ h₂ (g := fun z w => (w - z)⁻¹ • R w v)
    (continuousOn_kernel hne hR2 v)
  beta_reduce at hF
  rw [hF]
  have hout : ∀ w ∈ sphere c r₂, circleIntegral (fun z => (w - z)⁻¹ • R w v) c r₁ = 0 := by
    intro w hw
    apply circle_inv_outside h₁.le
    intro hmem
    rw [mem_sphere] at hw
    have := mem_closedBall.1 hmem
    linarith
  rw [circleIntegral.integral_congr h₂.le (fun w hw => hout w hw)]
  simp [circleIntegral]

/-! ## Idempotence -/

/-- `P_{r₁} P_{r₂} = P_{r₁}` for radii `0 < r₁ < r₂` with the closed annulus in `ρ`. -/
theorem contourProj_mul_eq {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hann : closedBall c r₂ \ ball c r₁ ⊆ ρ) :
    contourProj R c r₁ * contourProj R c r₂ = contourProj R c r₁ := by
  have h₂ : 0 < r₂ := h₁.trans h₁₂
  have hs1 : sphere c r₁ ⊆ ρ := fun z hz => hann (sphere_inner_sub h₁₂.le hz)
  have hs2 : sphere c r₂ ⊆ ρ := fun z hz => hann (sphere_outer_sub h₁₂ hz)
  have hR1 : ContinuousOn R (sphere c r₁) := hR.diff.continuousOn.mono hs1
  have hR2 : ContinuousOn R (sphere c r₂) := hR.diff.continuousOn.mono hs2
  have hc0 : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hne : r₁ ≠ r₂ := h₁₂.ne
  ext v
  have hRv2 : ContinuousOn (fun w => R w v) (sphere c r₂) := hR2.clm_apply continuousOn_const
  rw [ContinuousLinearMap.mul_apply]
  have hstep : ∀ z ∈ sphere c r₁, R z (contourProj R c r₂ v) =
      (2 * π * Complex.I)⁻¹ • circleIntegral (fun w => R z (R w v)) c r₂ := by
    intro z _
    rw [contourProj_apply h₂ hR2 v, map_smul, circleIntegral_clm_apply (R z) h₂ hRv2]
  have hI : circleIntegral (fun z => circleIntegral (fun w => R z (R w v)) c r₂) c r₁ =
      (2 * π * Complex.I) • circleIntegral (fun z => R z v) c r₁ := by
    have hEq : EqOn (fun z => circleIntegral (fun w => R z (R w v)) c r₂)
        (fun z => (2 * π * Complex.I) • R z v - circleIntegral (fun w => (w - z)⁻¹ • R w v) c r₂)
        (sphere c r₁) :=
      fun z hz => inner_identity hR h₁ h₂ h₁₂ hs2 v hz (hs1 hz)
    rw [circleIntegral.integral_congr h₁.le hEq]
    have hint1 : CircleIntegrable (fun z => (2 * π * Complex.I) • R z v) c r₁ :=
      circleIntegrable_of_contOn h₁ (hR1.clm_apply continuousOn_const |>.const_smul _)
    have hint2 : CircleIntegrable
        (fun z => circleIntegral (fun w => (w - z)⁻¹ • R w v) c r₂) c r₁ :=
      circleIntegrable_inner h₁ h₂ (g := fun z w => (w - z)⁻¹ • R w v)
        (continuousOn_kernel hne hR2 v)
    rw [circleIntegral.integral_sub hint1 hint2, circleIntegral_const_smul',
      cross_term_zero hR h₁ h₂ h₁₂ hs2 v, sub_zero]
  have hcongr : circleIntegral (fun z => R z (contourProj R c r₂ v)) c r₁ =
      circleIntegral (fun z => (2 * π * Complex.I)⁻¹ •
        circleIntegral (fun w => R z (R w v)) c r₂) c r₁ :=
    circleIntegral.integral_congr h₁.le (fun z hz => hstep z hz)
  rw [contourProj_apply h₁ hR1 (contourProj R c r₂ v), hcongr, circleIntegral_const_smul', hI,
    contourProj_apply h₁ hR1 v, smul_smul, smul_smul]
  have key : (2 * π * Complex.I)⁻¹ * (2 * π * Complex.I)⁻¹ * (2 * π * Complex.I) =
      (2 * π * Complex.I)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  rw [key]

/-! ## Domain and commutation, from the closed graph -/

/-- For `v`, the contour integral of `(R z v, z R z v - v)` lies in the closed graph of `T`, so the
integral `A = ∮ R z v` lies in `T.domain` and `T A = ∮ (z R z v - v)`. -/
theorem contour_domain {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r : ℝ} (h : 0 < r) (hs : sphere c r ⊆ ρ) (v : E) :
    ∃ hA : circleIntegral (fun z => R z v) c r ∈ T.domain,
      T.toFun ⟨circleIntegral (fun z => R z v) c r, hA⟩ =
        circleIntegral (fun z => z • R z v - v) c r := by
  have hR1 : ContinuousOn R (sphere c r) := hR.diff.continuousOn.mono hs
  have hpairC : ContinuousOn (fun z : ℂ => (R z v, z • R z v - v)) (sphere c r) :=
    (hR1.clm_apply continuousOn_const).prodMk
      ((continuousOn_id.smul (hR1.clm_apply continuousOn_const)).sub continuousOn_const)
  have hpairMem : ∀ z ∈ sphere c r, (R z v, z • R z v - v) ∈ T.graph := by
    intro z hz
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨R z v, hR.mem_dom z (hs hz) v⟩, rfl, hR.left z (hs hz) v⟩
  have hmemX : circleIntegral (fun z => (R z v, z • R z v - v)) c r ∈ T.graph := by
    have := integral_mem_of_closed_submodule T.graph hR.closed (a := 0) (b := 2 * π)
      (by positivity)
      (g := fun θ => deriv (circleMap c r) θ • (fun z : ℂ => (R z v, z • R z v - v)) (circleMap c r θ))
      (continuous_circleWeight h hpairC).continuousOn
      (fun θ _ => T.graph.smul_mem _ (hpairMem _ (circleMap_mem_sphere_of_pos h θ)))
    exact this
  have hfst : (circleIntegral (fun z => (R z v, z • R z v - v)) c r).1 =
      circleIntegral (fun z => R z v) c r := by
    have := circleIntegral_clm_apply (ContinuousLinearMap.fst ℂ E E) h hpairC
    simpa using this
  have hsnd : (circleIntegral (fun z => (R z v, z • R z v - v)) c r).2 =
      circleIntegral (fun z => z • R z v - v) c r := by
    have := circleIntegral_clm_apply (ContinuousLinearMap.snd ℂ E E) h hpairC
    simpa using this
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff T).1 hmemX
  have hAeq : circleIntegral (fun z => R z v) c r = (y : E) := by
    rw [← hfst, hy1]
  have hA : circleIntegral (fun z => R z v) c r ∈ T.domain := by
    rw [hAeq]
    exact y.2
  refine ⟨hA, ?_⟩
  have hsub : (⟨circleIntegral (fun z => R z v) c r, hA⟩ : T.domain) = y :=
    Subtype.ext hAeq
  rw [hsub]
  exact hy2.trans hsnd

/-! ## The main theorem (G1) -/

/-- G1: for a closed operator with contour-resolvent data, the contour projection is independent
of the radius, idempotent, maps `T.domain` into itself, and commutes with `T` on `T.domain`. -/
theorem contour_projection_G1 {T : E →ₗ.[ℂ] E} {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E}
    (hR : ClosedResolvent T ρ R) {c : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hann : closedBall c r₂ \ ball c r₁ ⊆ ρ) :
    contourProj R c r₁ = contourProj R c r₂ ∧
    contourProj R c r₁ * contourProj R c r₁ = contourProj R c r₁ ∧
    (∀ v, contourProj R c r₁ v ∈ T.domain) ∧
    (∀ v (hv : v ∈ T.domain) (hPv : contourProj R c r₁ v ∈ T.domain),
      T.toFun ⟨contourProj R c r₁ v, hPv⟩ = contourProj R c r₁ (T.toFun ⟨v, hv⟩)) := by
  have hs1 : sphere c r₁ ⊆ ρ := fun z hz => hann (sphere_inner_sub h₁₂.le hz)
  have hR1 : ContinuousOn R (sphere c r₁) := hR.diff.continuousOn.mono hs1
  have hP : contourProj R c r₁ = contourProj R c r₂ :=
    contourProj_indep hR h₁ h₁₂.le hann
  have hid : contourProj R c r₁ * contourProj R c r₁ = contourProj R c r₁ := by
    have := contourProj_mul_eq hR h₁ h₁₂ hann
    rwa [← hP] at this
  have hmem : ∀ v, contourProj R c r₁ v ∈ T.domain := by
    intro v
    obtain ⟨hA, _⟩ := contour_domain hR h₁ hs1 v
    rw [contourProj_apply h₁ hR1 v]
    exact T.domain.smul_mem _ hA
  refine ⟨hP, hid, hmem, ?_⟩
  intro v hv hPv
  obtain ⟨hA, hAT⟩ := contour_domain hR h₁ hs1 v
  have hsmul : (⟨contourProj R c r₁ v, hPv⟩ : T.domain) =
      (2 * π * Complex.I)⁻¹ • (⟨circleIntegral (fun z => R z v) c r₁, hA⟩ : T.domain) := by
    exact Subtype.ext (contourProj_apply h₁ hR1 v)
  rw [hsmul, map_smul, hAT, contourProj_apply h₁ hR1 (T.toFun ⟨v, hv⟩)]
  congr 1
  apply circleIntegral.integral_congr h₁.le
  intro z hz
  exact (hR.right z (hs1 hz) v hv).symm

/-! ## The bounded case (corollary) -/

/-- Bounded case: `T : E →L E` (domain `E`), resolvent `R z` inverting `z - T` on the open set `ρ`.
The contour projection is an idempotent commuting with `T`. -/
theorem contour_projection_bounded {ρ : Set ℂ} {R : ℂ → E →L[ℂ] E} (T : E →L[ℂ] E)
    (hρ : IsOpen ρ) (hdiff : DifferentiableOn ℂ R ρ)
    (hleft : ∀ z ∈ ρ, ∀ v, T (R z v) = z • R z v - v)
    (hright : ∀ z ∈ ρ, ∀ x, R z (T x) = z • R z x - x)
    {c : ℂ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) (hann : closedBall c r₂ \ ball c r₁ ⊆ ρ) :
    contourProj R c r₁ * contourProj R c r₁ = contourProj R c r₁ ∧
      ∀ v, T (contourProj R c r₁ v) = contourProj R c r₁ (T v) := by
  let T' : E →ₗ.[ℂ] E := LinearMap.toPMap T.toLinearMap ⊤
  have hgr : (T'.graph : Set (E × E)) = {p | T p.1 = p.2} := by
    ext p
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨y, h1, h2⟩
      rw [Set.mem_setOf_eq, ← h1, ← h2]
      rfl
    · intro h
      exact ⟨⟨p.1, Submodule.mem_top⟩, rfl, h⟩
  have hcl : IsClosed (T'.graph : Set (E × E)) := by
    rw [hgr]
    exact isClosed_eq (T.continuous.comp continuous_fst) continuous_snd
  have hR' : ClosedResolvent T' ρ R :=
    { isOpen := hρ
      diff := hdiff
      closed := hcl
      mem_dom := fun _ _ _ => Submodule.mem_top
      left := fun z hz v => hleft z hz v
      right := fun z hz x _ => hright z hz x }
  have main := contour_projection_G1 hR' h₁ h₁₂ hann
  refine ⟨main.2.1, fun v => ?_⟩
  exact main.2.2.2 v Submodule.mem_top (main.2.2.1 v)

end QuantumNLS.Ext025HGP17Resolvent
