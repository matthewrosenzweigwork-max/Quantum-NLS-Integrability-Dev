import QuantumNLS.ProductTorusSecondVariation

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T7a: the averaged primitive `ᾱ` — definition, measurability,
# bound, torus invariance, anti-symplectic covariance

Source: `chapters/global/product_torus.tex`, the setup (`α_u(h) = Im⟪u,h⟫`), eq:global-averaged-primitive
`ᾱ_u(h) = ∫_{𝕋^ℤ} α_{T_θ u}(DT_θ(u)h) dθ` (normalized product Haar measure), and the proof section
"Averaging the primitive": "The integrand ... is a measurable scalar function and is linear in `h`. The uniform
derivative bound and mass conservation give `|ᾱ_u(h)| ≤ ‖u‖ exp((π/2)A₂(𝒞))‖h‖`. It therefore defines a bounded
one-form." "The group law and invariance of product Haar measure give `T_η^*ᾱ = ᾱ`." "Finally, for the stated
anti-symplectic involution, `X_θ(Cu) = −CX_θ(u)`. Flow uniqueness gives `T_θC = CT_{−θ}`. Since `C^*α = −α`,
changing the Haar variable from `θ` to `−θ` proves `C^*ᾱ = −ᾱ`."

Hypotheses `PHyp I DI`: T2b `Hyp`, T4a `Nonneg`/`Proper`/`Periodic` and `D𝓘 ∈ C²` (the source assumes `𝓘` real
analytic). Measure: EXT-025 `productCircleHaar` on `Torus = ℤ → Circle`; the action is T4b `act`.

Proved:
* `alpha`, `alphaBar` (the literal eq:global-averaged-primitive); `continuous_integrand` (Borel measurability from
  continuity: T4b `act_continuous`, T5b `act_fderiv_continuous`); `measurable_alpha_fderiv2` (the second-derivative
  integrand, as a pointwise limit of difference quotients of T5b-continuous functions; no GP-14 clause);
* `local_fibre_bound`/`local_bounds` (bounds uniform over the fibres of all points near `u`, from properness),
  `norm_fderiv_act_le`, `norm_fderiv2_act_le` (uniform over the whole product group);
* `integrable_integrand`, `alphaBar_add`, `alphaBar_smul`, `alphaBarCLM` (a bounded one-form at each point),
  **`alphaBar_bound`** (`|ᾱ_u(h)| ≤ ‖u‖ exp((π/2)A₂)‖h‖`);
* **`alphaBar_invariant`** (`ᾱ_{T_φ u}(DT_φ(u)h) = ᾱ_u(h)` for every `φ ∈ 𝕋^ℤ`);
* `X_C`, `flow_C`, `act_C`, **`alphaBar_C`** (`C^*ᾱ = −ᾱ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusPrimitive

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusVariational
  QuantumNLS.ProductTorusCommute QuantumNLS.ProductTorusContinuity QuantumNLS.ProductTorusAction
  QuantumNLS.ProductTorusFixedVector QuantumNLS.ProductTorusSecondVariation
open QuantumNLS.Ext025B6TorusCoordinates (Torus inversion_haar)
open QuantumNLS.Ext025BHaar (productCircleHaar)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- The hypotheses of the primitive stage (source hypotheses 1–4 and `C²` regularity of `D𝓘`). -/
structure PHyp (I : E → L1 ℝ) (DI : E → (E →L[ℝ] L1 ℝ)) : Prop where
  hyp : Hyp I DI
  nonneg : Nonneg I
  proper : Proper I
  periodic : Periodic DI
  contDiff2 : ContDiff ℝ 2 DI

/-! ## 1. The primitive `α_u(h) = Im⟪u,h⟫` -/

/-- `α_u(h) = Im⟪u, h⟫`. -/
def alpha (u h : E) : ℝ := (inner ℂ u h).im

omit [CompleteSpace E] in
theorem alpha_eq (a b : E) : alpha a b = omega a b / 2 := by unfold alpha omega; ring

theorem alpha_eq_J : ∃ J : E →L[ℝ] E →L[ℝ] ℝ, ∀ a b, alpha a b = J a b / 2 := by
  obtain ⟨J, hJ, -⟩ := QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := E)
  refine ⟨(J : E →L[ℝ] E →L[ℝ] ℝ), fun a b => ?_⟩
  simp only [ContinuousLinearEquiv.coe_coe]
  rw [hJ, alpha]
  ring

omit [CompleteSpace E] in
theorem abs_alpha_le (a b : E) : |alpha a b| ≤ ‖a‖ * ‖b‖ :=
  (Complex.abs_im_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) a b)

theorem alpha_add_right (a b c : E) : alpha a (b + c) = alpha a b + alpha a c := by
  obtain ⟨J, hJ⟩ := alpha_eq_J (E := E)
  rw [hJ, hJ, hJ, map_add]
  ring

theorem alpha_smul_right (a b : E) (c : ℝ) : alpha a (c • b) = c * alpha a b := by
  obtain ⟨J, hJ⟩ := alpha_eq_J (E := E)
  rw [hJ, hJ, map_smul, smul_eq_mul]
  ring

theorem alpha_zero_right (a : E) : alpha a 0 = 0 := by
  obtain ⟨J, hJ⟩ := alpha_eq_J (E := E)
  rw [hJ, map_zero, zero_div]

omit [CompleteSpace E] in
theorem alpha_sub_swap (p q : E) : alpha p q - alpha q p = omega p q := by
  rw [alpha_eq, alpha_eq, omega_antisymm q p]
  ring

theorem continuous_alpha : Continuous (fun p : E × E => alpha p.1 p.2) := by
  obtain ⟨J, hJ⟩ := alpha_eq_J (E := E)
  have : (fun p : E × E => alpha p.1 p.2) = fun p => J p.1 p.2 / 2 := funext fun p => hJ _ _
  rw [this]
  exact ((J.continuous.comp continuous_fst).clm_apply continuous_snd).div_const 2

theorem continuous_alpha_comp {α : Type*} [TopologicalSpace α] {f g : α → E} (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun x => alpha (f x) (g x)) :=
  continuous_alpha.comp (hf.prodMk hg)

/-- Derivative of `t ↦ α_{f t}(g t)`. -/
theorem hasDerivAt_alpha {f g : ℝ → E} {f' g' : E} {t : ℝ} (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => alpha (f s) (g s)) (alpha f' (g t) + alpha (f t) g') t := by
  obtain ⟨J, hJ⟩ := alpha_eq_J (E := E)
  have h1 : HasDerivAt (fun s => J (f s) (g s) / 2) ((J f' (g t) + J (f t) g') / 2) t :=
    ((J.hasFDerivAt.comp_hasDerivAt t hf).clm_apply hg).div_const 2
  have e1 : (fun s => alpha (f s) (g s)) = fun s => J (f s) (g s) / 2 := funext fun s => hJ _ _
  rw [e1, hJ, hJ, ← add_div]
  exact h1

/-! ## 2. The action: derivatives, fibres, continuity in the group parameter -/

theorem act_def (ψ : Torus) : act DI ψ = flow DI (lift ψ) 1 := rfl

theorem act_mem_fibre (H : PHyp I DI) (ψ : Torus) (x : E) : act DI ψ x ∈ I ⁻¹' {I x} :=
  mem_fibre_flow H.hyp (lift ψ) (Set.mem_singleton (I x)) 1

theorem hasFDerivAt_act (H : PHyp I DI) (ψ : Torus) (x : E) :
    HasFDerivAt (act DI ψ) (fderiv ℝ (act DI ψ) x) x := by
  rw [act_def]
  exact (differentiableAt_flow H.hyp (lift ψ) 1 x).hasFDerivAt

theorem hasFDerivAt_fderiv_act (H : PHyp I DI) (ψ : Torus) (x : E) :
    HasFDerivAt (fderiv ℝ (act DI ψ)) (fderiv ℝ (fderiv ℝ (act DI ψ)) x) x := by
  rw [act_def]
  exact (differentiableAt_fderiv_flow H.hyp H.contDiff2 (lift ψ) 1 x).hasFDerivAt

theorem continuous_act (H : PHyp I DI) (x : E) : Continuous (fun ψ : Torus => act DI ψ x) :=
  (act_continuous H.hyp H.nonneg H.proper H.periodic).comp (continuous_id.prodMk continuous_const)

theorem continuous_fderiv_act (H : PHyp I DI) (x k : E) : Continuous (fun ψ : Torus => fderiv ℝ (act DI ψ) x k) :=
  act_fderiv_continuous H.hyp H.nonneg H.proper H.periodic x k

/-- The integrand of eq:global-averaged-primitive is continuous on the product torus (hence Borel measurable). -/
theorem continuous_integrand (H : PHyp I DI) (u h : E) :
    Continuous (fun ψ : Torus => alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h)) :=
  continuous_alpha_comp (continuous_act H u) (continuous_fderiv_act H u h)

/-- Measurability of the second-derivative integrand `ψ ↦ α_{T_ψ x}(D²T_ψ(x)[a,b])`: a pointwise limit of difference
quotients of functions continuous on the product torus (T5b). -/
theorem measurable_alpha_fderiv2 (H : PHyp I DI) (x a b : E) :
    Measurable (fun ψ : Torus => alpha (act DI ψ x) (fderiv ℝ (fderiv ℝ (act DI ψ)) x a b)) := by
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (ψ : Torus) => alpha (act DI ψ x)
    (((n : ℝ) + 1)⁻¹⁻¹ • (fderiv ℝ (act DI ψ) (x + ((n : ℝ) + 1)⁻¹ • a) b - fderiv ℝ (act DI ψ) x b)))
    (fun n => ?_) ?_
  · exact (continuous_alpha_comp (continuous_act H x)
      (((continuous_fderiv_act H _ b).sub (continuous_fderiv_act H x b)).const_smul _)).measurable
  · rw [tendsto_pi_nhds]
    intro ψ
    have hl : HasDerivAt (fun s : ℝ => x + s • a) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
    have hD : HasFDerivAt (fderiv ℝ (act DI ψ)) (fderiv ℝ (fderiv ℝ (act DI ψ)) x) (x + (0 : ℝ) • a) := by
      rw [zero_smul, add_zero]
      exact hasFDerivAt_fderiv_act H ψ x
    have hd : HasDerivAt (fun s : ℝ => fderiv ℝ (act DI ψ) (x + s • a) b)
        (fderiv ℝ (fderiv ℝ (act DI ψ)) x a b) 0 := by
      have := (hD.comp_hasDerivAt (0 : ℝ) hl).clm_apply (hasDerivAt_const (0 : ℝ) b)
      simpa using this
    have hs := hd.tendsto_slope_zero
    have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Eventually.of_forall fun n => ?_)
      · simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      · exact Set.mem_compl_singleton_iff.2 (inv_ne_zero (by positivity))
    have hα : Continuous (fun v : E => alpha (act DI ψ x) v) := continuous_alpha_comp continuous_const continuous_id
    refine ((hα.tendsto _).comp (hs.comp hseq)).congr fun n => ?_
    simp only [Function.comp_apply, zero_add, zero_smul, add_zero]

/-! ## 3. Bounds uniform over the product group and over nearby fibres -/

/-- Properness gives bounds of a continuous function on the fibres of all points near `u`. -/
theorem local_fibre_bound (H : PHyp I DI) {g : E → ℝ} (hg : Continuous g) (u : E) :
    ∃ ρ > (0 : ℝ), ∃ M, ∀ x ∈ ball u ρ, ∀ w ∈ I ⁻¹' {I x}, g w ≤ M := by
  have hIc : Continuous I := continuous_iff_continuousAt.2 fun v => (H.hyp.hasFDerivAt v).continuousAt
  by_contra hcon
  push Not at hcon
  choose x hx w hw hgw using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity) n
  have hxt : Tendsto x atTop (𝓝 u) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (mem_ball.1 (hx n)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨B, hB⟩ := (compact_preimage H.nonneg H.proper hIc hxt).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hmem : w n ∈ I ⁻¹' insert (I u) (Set.range fun j => I (x j)) := by
    have h0 : I (w n) = I (x n) := hw n
    show I (w n) ∈ insert (I u) (Set.range fun j => I (x j))
    rw [h0]
    exact Set.mem_insert_of_mem _ ⟨n, rfl⟩
  have h1 := hB (w n) hmem
  have h2 := hgw n
  have h3 := le_abs_self (g (w n))
  rw [Real.norm_eq_abs] at h1
  linarith

theorem local_bounds (H : PHyp I DI) (u : E) :
    ∃ ρ > (0 : ℝ), ∃ M, 0 ≤ M ∧ ∀ x ∈ ball u ρ, ∀ w ∈ I ⁻¹' {I x},
      ‖w‖ ≤ M ∧ ‖fderiv ℝ DI w‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ DI) w‖ ≤ M := by
  have hc1 : ContDiff ℝ 1 (fderiv ℝ DI) := H.contDiff2.fderiv_right (le_of_eq one_add_one_eq_two)
  have hg : Continuous (fun w => ‖w‖ + ‖fderiv ℝ DI w‖ + ‖fderiv ℝ (fderiv ℝ DI) w‖) :=
    (continuous_norm.add hc1.continuous.norm).add (hc1.continuous_fderiv one_ne_zero).norm
  obtain ⟨ρ, hρ, M, hM⟩ := local_fibre_bound H hg u
  have hM0 : 0 ≤ M := by
    have := hM u (mem_ball_self hρ) u (Set.mem_singleton (I u))
    have a1 := norm_nonneg u
    have a2 := norm_nonneg (fderiv ℝ DI u)
    have a3 := norm_nonneg (fderiv ℝ (fderiv ℝ DI) u)
    linarith
  refine ⟨ρ, hρ, M, hM0, fun x hx w hw => ?_⟩
  have := hM x hx w hw
  have a1 := norm_nonneg w
  have a2 := norm_nonneg (fderiv ℝ DI w)
  have a3 := norm_nonneg (fderiv ℝ (fderiv ℝ DI) w)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem norm_fderiv_X_lift_le (H : PHyp I DI) (ψ : Torus) {x : E} {M : ℝ}
    (hM : ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ DI w‖ ≤ M) :
    ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ (X DI (lift ψ)) w‖ ≤ Real.pi * M / 2 + 1 := fun w hw => by
  have h1 := norm_fderiv_X_le H.hyp (lift ψ) w
  have h2 := mul_le_mul (norm_lift_le ψ) (hM w hw) (norm_nonneg _) Real.pi_pos.le
  linarith

/-- `‖DT_ψ(x)‖ ≤ exp(πM/2 + 1)` uniformly over the product group. -/
theorem norm_fderiv_act_le (H : PHyp I DI) (ψ : Torus) (x : E) {M : ℝ}
    (hM : ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ DI w‖ ≤ M) :
    ‖fderiv ℝ (act DI ψ) x‖ ≤ Real.exp (Real.pi * M / 2 + 1) := by
  have := norm_fderiv_flow_le_nonneg H.hyp (lift ψ) x (norm_fderiv_X_lift_le H ψ hM) zero_le_one
  rw [mul_one] at this
  rw [act_def]
  exact this

/-- `‖D²T_ψ(x)‖` is bounded uniformly over the product group. -/
theorem norm_fderiv2_act_le (H : PHyp I DI) (ψ : Torus) (x : E) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ DI w‖ ≤ M) (hM3 : ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ (fderiv ℝ DI) w‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ (act DI ψ)) x‖ ≤ Real.pi * M / 2 * Real.exp (Real.pi * M / 2 + 1) *
      Real.exp (Real.pi * M / 2 + 1) / (Real.pi * M / 2 + 1) * Real.exp (Real.pi * M / 2 + 1) := by
  have hK₂ : ∀ w ∈ I ⁻¹' {I x}, ‖fderiv ℝ (fderiv ℝ (X DI (lift ψ))) w‖ ≤ Real.pi * M / 2 := fun w hw => by
    have h1 := norm_fderiv2_X_le H.hyp H.contDiff2 (lift ψ) w
    have h2 := mul_le_mul (norm_lift_le ψ) (hM3 w hw) (norm_nonneg _) Real.pi_pos.le
    linarith
  have hK0 : (0 : ℝ) < Real.pi * M / 2 + 1 := by positivity
  have := norm_fderiv2_flow_le H.hyp H.contDiff2 (lift ψ) x hK0 (norm_fderiv_X_lift_le H ψ hM) hK₂ zero_le_one
  rw [mul_one] at this
  rw [act_def]
  exact this

/-! ## 4. The averaged primitive -/

/-- **eq:global-averaged-primitive**: `ᾱ_u(h) = ∫_{𝕋^ℤ} α_{T_θ u}(DT_θ(u)h) dθ`. -/
def alphaBar (DI : E → (E →L[ℝ] L1 ℝ)) (u h : E) : ℝ :=
  ∫ ψ, alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h) ∂productCircleHaar

theorem integrable_integrand (H : PHyp I DI) (u h : E) :
    Integrable (fun ψ : Torus => alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h)) productCircleHaar := by
  obtain ⟨ρ, hρ, M, hM0, hM⟩ := local_bounds H u
  have hu : u ∈ ball u ρ := mem_ball_self hρ
  refine Integrable.of_bound (continuous_integrand H u h).aestronglyMeasurable
    (M * (Real.exp (Real.pi * M / 2 + 1) * ‖h‖)) (Eventually.of_forall fun ψ => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_alpha_le _ _).trans (mul_le_mul (hM u hu _ (act_mem_fibre H ψ u)).1 ?_ (norm_nonneg _) hM0)
  exact ((fderiv ℝ (act DI ψ) u).le_opNorm h).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_act_le H ψ u fun w hw => (hM u hu w hw).2.1) (norm_nonneg _))

theorem alphaBar_add (H : PHyp I DI) (u h k : E) : alphaBar DI u (h + k) = alphaBar DI u h + alphaBar DI u k := by
  unfold alphaBar
  rw [← integral_add (integrable_integrand H u h) (integrable_integrand H u k)]
  congr 1
  funext ψ
  rw [map_add, alpha_add_right]

theorem alphaBar_smul (c : ℝ) (u h : E) : alphaBar DI u (c • h) = c * alphaBar DI u h := by
  unfold alphaBar
  rw [← integral_const_mul]
  congr 1
  funext ψ
  rw [map_smul, alpha_smul_right]

theorem alphaBar_zero_right (u : E) : alphaBar DI u 0 = 0 := by
  unfold alphaBar
  simp [alpha_zero_right]

theorem alphaBar_bound_exists (H : PHyp I DI) (u : E) : ∃ C, ∀ h, ‖alphaBar DI u h‖ ≤ C * ‖h‖ := by
  obtain ⟨ρ, hρ, M, hM0, hM⟩ := local_bounds H u
  have hu : u ∈ ball u ρ := mem_ball_self hρ
  refine ⟨M * Real.exp (Real.pi * M / 2 + 1), fun h => ?_⟩
  unfold alphaBar
  have := norm_integral_le_of_norm_le_const (μ := productCircleHaar)
    (f := fun ψ => alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h)) (C := M * Real.exp (Real.pi * M / 2 + 1) * ‖h‖)
    (Eventually.of_forall fun ψ => by
      rw [Real.norm_eq_abs]
      refine (abs_alpha_le _ _).trans ?_
      have e1 := (hM u hu _ (act_mem_fibre H ψ u)).1
      have e2 := ((fderiv ℝ (act DI ψ) u).le_opNorm h).trans (mul_le_mul_of_nonneg_right
        (norm_fderiv_act_le H ψ u fun w hw => (hM u hu w hw).2.1) (norm_nonneg _))
      calc ‖act DI ψ u‖ * ‖fderiv ℝ (act DI ψ) u h‖ ≤ M * (Real.exp (Real.pi * M / 2 + 1) * ‖h‖) :=
            mul_le_mul e1 e2 (norm_nonneg _) hM0
        _ = M * Real.exp (Real.pi * M / 2 + 1) * ‖h‖ := by ring)
  rwa [probReal_univ, mul_one] at this

/-- `ᾱ_u` as a bounded one-form. -/
def alphaBarCLM (H : PHyp I DI) (u : E) : E →L[ℝ] ℝ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := alphaBar DI u
      map_add' := alphaBar_add H u
      map_smul' := fun c h => by rw [alphaBar_smul, smul_eq_mul, RingHom.id_apply] }
    (alphaBar_bound_exists H u)

theorem alphaBarCLM_apply (H : PHyp I DI) (u h : E) : alphaBarCLM H u h = alphaBar DI u h := rfl

/-- **The bound of the source**: `|ᾱ_u(h)| ≤ ‖u‖ exp((π/2)A₂)‖h‖` when `‖D²𝓘‖ ≤ A₂` on the fibre of `u` (in
particular on any compact `𝒞 = 𝓘⁻¹(K)` containing `u`). Uses mass conservation (source hypothesis 1). -/
theorem alphaBar_bound (H : PHyp I DI) (hmass : ∀ u, ∑' n, (I u : ℤ → ℝ) n = ‖u‖ ^ 2) (u : E) {A₂ : ℝ}
    (hA : ∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ DI w‖ ≤ A₂) (h : E) :
    |alphaBar DI u h| ≤ ‖u‖ * Real.exp (Real.pi / 2 * A₂) * ‖h‖ := by
  have hA0 : 0 ≤ A₂ := (norm_nonneg _).trans (hA u (Set.mem_singleton (I u)))
  unfold alphaBar
  have := norm_integral_le_of_norm_le_const (μ := productCircleHaar)
    (f := fun ψ => alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h)) (C := ‖u‖ * Real.exp (Real.pi / 2 * A₂) * ‖h‖)
    (Eventually.of_forall fun ψ => by
      rw [Real.norm_eq_abs]
      refine (abs_alpha_le _ _).trans ?_
      have hn : ‖act DI ψ u‖ = ‖u‖ := norm_flow H.hyp hmass (lift ψ) u 1
      have hK : ∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ (X DI (lift ψ)) w‖ ≤ ‖lift ψ‖ / 2 * A₂ := fun w hw => by
        have h1 := norm_fderiv_X_le H.hyp (lift ψ) w
        have h2 := mul_le_mul_of_nonneg_left (hA w hw) (norm_nonneg (lift ψ))
        linarith
      have hD := norm_fderiv_flow_le_nonneg H.hyp (lift ψ) u hK zero_le_one
      rw [mul_one] at hD
      have hD' : ‖fderiv ℝ (act DI ψ) u‖ ≤ Real.exp (Real.pi / 2 * A₂) := by
        rw [act_def]
        refine hD.trans (Real.exp_le_exp.2 ?_)
        have := norm_lift_le ψ
        nlinarith
      rw [hn]
      calc ‖u‖ * ‖fderiv ℝ (act DI ψ) u h‖ ≤ ‖u‖ * (Real.exp (Real.pi / 2 * A₂) * ‖h‖) :=
            mul_le_mul_of_nonneg_left (((fderiv ℝ (act DI ψ) u).le_opNorm h).trans
              (mul_le_mul_of_nonneg_right hD' (norm_nonneg _))) (norm_nonneg _)
        _ = ‖u‖ * Real.exp (Real.pi / 2 * A₂) * ‖h‖ := by ring)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

/-! ## 5. Torus invariance `T_φ^*ᾱ = ᾱ` -/

/-- **`T_φ^*ᾱ = ᾱ`** for every element `φ` of the product group. -/
theorem alphaBar_invariant (H : PHyp I DI) (φ : Torus) (u h : E) :
    alphaBar DI (act DI φ u) (fderiv ℝ (act DI φ) u h) = alphaBar DI u h := by
  unfold alphaBar
  have key : ∀ ψ : Torus, alpha (act DI ψ (act DI φ u)) (fderiv ℝ (act DI ψ) (act DI φ u) (fderiv ℝ (act DI φ) u h)) =
      alpha (act DI (φ * ψ) u) (fderiv ℝ (act DI (φ * ψ)) u h) := by
    intro ψ
    have hcomp : act DI (φ * ψ) = act DI ψ ∘ act DI φ := by
      funext v
      rw [Function.comp_apply, mul_comm, act_mul H.hyp H.nonneg H.proper H.periodic]
    have hd : fderiv ℝ (act DI (φ * ψ)) u = (fderiv ℝ (act DI ψ) (act DI φ u)).comp (fderiv ℝ (act DI φ) u) := by
      rw [hcomp]
      exact fderiv_comp u (hasFDerivAt_act H ψ _).differentiableAt (hasFDerivAt_act H φ u).differentiableAt
    have hv : act DI (φ * ψ) u = act DI ψ (act DI φ u) := congrFun hcomp u
    rw [hd, hv, ContinuousLinearMap.comp_apply]
  simp_rw [key]
  exact integral_mul_left_eq_self (fun ψ => alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h)) φ

/-! ## 6. Covariance under an anti-symplectic involution -/

omit [CompleteSpace E] in
theorem omega_neg_left (a k : E) : omega (-a) k = -omega a k := by
  unfold omega
  rw [inner_neg_left, Complex.neg_im]
  ring

section Involution

variable {C : E →L[ℝ] E}

theorem DI_C (H : PHyp I DI) (hCC : ∀ v, C (C v) = v) (hCI : ∀ v, I (C v) = I v) (v k : E) :
    DI (C v) k = DI v (C k) := by
  have h1 : HasFDerivAt (fun y => I (C y)) ((DI (C v)).comp C) v := (H.hyp.hasFDerivAt (C v)).comp v C.hasFDerivAt
  have h2 : HasFDerivAt (fun y => I (C y)) (DI v) v := by
    have : (fun y => I (C y)) = I := funext hCI
    rw [this]
    exact H.hyp.hasFDerivAt v
  have := congrArg (fun L : E →L[ℝ] L1 ℝ => L (C k)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, hCC] at this
  exact this

/-- `X_θ(Cu) = −C X_θ(u)`. -/
theorem X_C (H : PHyp I DI) (hCC : ∀ v, C (C v) = v) (hCω : ∀ a b, omega (C a) (C b) = -omega a b)
    (hCI : ∀ v, I (C v) = I v) (θ : Linf) (v : E) : X DI θ (C v) = -C (X DI θ v) := by
  refine sub_eq_zero.1 (omega_nondeg fun k => ?_)
  rw [omega_sub_left, omega_neg_left, omega_X, DI_C H hCC hCI]
  have e : omega (C (X DI θ v)) k = -omega (X DI θ v) (C k) := by
    have := hCω (X DI θ v) (C k)
    rwa [hCC] at this
  rw [e, omega_X]
  ring

/-- Flow uniqueness: `φ_θ^t(Cu) = C φ_θ^{−t}(u)`. -/
theorem flow_C (H : PHyp I DI) (hCC : ∀ v, C (C v) = v) (hCω : ∀ a b, omega (C a) (C b) = -omega a b)
    (hCI : ∀ v, I (C v) = I v) (θ : Linf) (u : E) (t : ℝ) : flow DI θ t (C u) = C (flow DI θ (-t) u) := by
  have hα : ∀ s, HasDerivAt (fun s => C (flow DI θ (-s) u)) (X DI θ (C (flow DI θ (-s) u))) s := by
    intro s
    have h1 : HasDerivAt (fun s => flow DI θ (-s) u) ((-1 : ℝ) • X DI θ (flow DI θ (-s) u)) s :=
      (hasDerivAt_flow H.hyp θ u (-s)).scomp s (hasDerivAt_neg s)
    have h2 := C.hasFDerivAt.comp_hasDerivAt s h1
    rw [X_C H hCC hCω hCI, ← map_neg, ← neg_one_smul ℝ (X DI θ (flow DI θ (-s) u))]
    exact h2
  exact flow_eq_of_sol H.hyp θ (α := fun s => C (flow DI θ (-s) u)) (by simp [flow_zero H.hyp]) hα t

theorem act_inv_eq (H : PHyp I DI) (ψ : Torus) : act DI ψ⁻¹ = T DI (-lift ψ) :=
  act_eq_T H.hyp H.nonneg H.proper H.periodic (fun n => by
    rw [lp.coeFn_neg, Pi.neg_apply, Circle.exp_neg, exp_lift, Pi.inv_apply])

/-- `T_θ C = C T_{−θ}` on the product torus: `act ψ (Cu) = C (act ψ⁻¹ u)`. -/
theorem act_C (H : PHyp I DI) (hCC : ∀ v, C (C v) = v) (hCω : ∀ a b, omega (C a) (C b) = -omega a b)
    (hCI : ∀ v, I (C v) = I v) (ψ : Torus) (u : E) : act DI ψ (C u) = C (act DI ψ⁻¹ u) := by
  rw [act_inv_eq H ψ]
  show flow DI (lift ψ) 1 (C u) = C (flow DI (-lift ψ) 1 u)
  rw [flow_C H hCC hCω hCI, flow_neg_angle H.hyp]

theorem fderiv_act_C (H : PHyp I DI) (hCC : ∀ v, C (C v) = v) (hCω : ∀ a b, omega (C a) (C b) = -omega a b)
    (hCI : ∀ v, I (C v) = I v) (ψ : Torus) (u h : E) :
    fderiv ℝ (act DI ψ) (C u) (C h) = C (fderiv ℝ (act DI ψ⁻¹) u h) := by
  have hfun : act DI ψ ∘ C = C ∘ act DI ψ⁻¹ := funext fun v => act_C H hCC hCω hCI ψ v
  have h1 : fderiv ℝ (act DI ψ ∘ C) u = (fderiv ℝ (act DI ψ) (C u)).comp C := by
    rw [fderiv_comp u (hasFDerivAt_act H ψ (C u)).differentiableAt C.differentiableAt, C.fderiv]
  have h2 : fderiv ℝ (C ∘ act DI ψ⁻¹) u = C.comp (fderiv ℝ (act DI ψ⁻¹) u) := by
    rw [fderiv_comp u C.differentiableAt (hasFDerivAt_act H ψ⁻¹ u).differentiableAt, C.fderiv]
  have := congrArg (fun L : E →L[ℝ] E => L h) (h1.symm.trans ((congrArg (fun f => fderiv ℝ f u) hfun).trans h2))
  simpa using this

omit [CompleteSpace E] in
theorem alpha_C (hCω : ∀ a b, omega (C a) (C b) = -omega a b) (a b : E) : alpha (C a) (C b) = -alpha a b := by
  rw [alpha_eq, alpha_eq, hCω]
  ring

/-- **`C^*ᾱ = −ᾱ`** for a bounded real-linear involution `C` with `C^*ω = −ω` and `I_n(Cu) = I_n(u)`. -/
theorem alphaBar_C (H : PHyp I DI) (hCC : ∀ v, C (C v) = v) (hCω : ∀ a b, omega (C a) (C b) = -omega a b)
    (hCI : ∀ v, I (C v) = I v) (u h : E) : alphaBar DI (C u) (C h) = -alphaBar DI u h := by
  unfold alphaBar
  have key : ∀ ψ : Torus, alpha (act DI ψ (C u)) (fderiv ℝ (act DI ψ) (C u) (C h)) =
      -alpha (act DI ψ⁻¹ u) (fderiv ℝ (act DI ψ⁻¹) u h) := by
    intro ψ
    rw [act_C H hCC hCω hCI, fderiv_act_C H hCC hCω hCI, alpha_C hCω]
  simp_rw [key]
  rw [integral_neg]
  congr 1
  exact inversion_haar.integral_comp (MeasurableEquiv.inv Torus).measurableEmbedding
    (fun ψ => alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h))

end Involution

end QuantumNLS.ProductTorusPrimitive

#print axioms QuantumNLS.ProductTorusPrimitive.continuous_integrand
#print axioms QuantumNLS.ProductTorusPrimitive.measurable_alpha_fderiv2
#print axioms QuantumNLS.ProductTorusPrimitive.local_bounds
#print axioms QuantumNLS.ProductTorusPrimitive.norm_fderiv2_act_le
#print axioms QuantumNLS.ProductTorusPrimitive.integrable_integrand
#print axioms QuantumNLS.ProductTorusPrimitive.alphaBarCLM
#print axioms QuantumNLS.ProductTorusPrimitive.alphaBar_bound
#print axioms QuantumNLS.ProductTorusPrimitive.alphaBar_invariant
#print axioms QuantumNLS.ProductTorusPrimitive.alphaBar_C
