import NlsGge.Ramer.RamerStep4
import NlsGge.Ramer.RamerLemma52

/-!
# Ramer Step 4, local form (R10-P2)

`ramer_step4_local` is `ramer_step4_core` for the local map `y ↦ y + i (K y)`, with no global
homeomorphism `T`.  `Tt`, `B`, `hv` are hypotheses (outputs of P1(a)).
`injOn_T'_local` is injectivity of `y ↦ y + i (K2 y)` on a closed ball, via R6 `injOn_add_image`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Set

namespace NlsGge.Ramer

section GenericLocal

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] (i : H →L[ℝ] E)

theorem K2_identity_local (K : E → H)
    (Tt : E ≃L[ℝ] E) (B : E →L[ℝ] H) (hTt : ∀ y, Tt.symm y = y + i (B y)) (e₁ e₂ : H) (y : E) :
    Tt.symm ((y - i e₁) + i (K (y - i e₁))) - i e₂ = y + i (K2 i K B e₁ e₂ y) := by
  rw [hTt]
  simp only [K2, map_add, map_sub, map_neg]
  abel

theorem K2_eq_Gmap_local (K : E → H) (B : E →L[ℝ] H) (x₀ : E) (e₁ : H) :
    K2 i K B e₁ (-e₁ + K x₀ + B (x₀ + i (K x₀))) = fun y => Gmap i K B x₀ (y - i e₁) := by
  funext y
  simp only [K2, Gmap]
  abel

/-- Injectivity of `y ↦ y + i (Φ y)` on closed balls of radius `< ε`, from the 1/8 bound. -/
theorem injOn_T'_local_generic (Φ : E → H) {ε ε' : ℝ} (hε' : ε' < ε)
    (hd : ∀ y : E, ‖y‖ < ε → DifferentiableAt ℝ Φ y)
    (hb : ∀ y : E, ‖y‖ < ε → ∀ h : H, ‖fderiv ℝ Φ y (i h)‖ ≤ 1 / 8 * ‖h‖) :
    InjOn (fun y => y + i (Φ y)) (closedBall (0 : E) ε') := by
  have hm : ∀ y ∈ closedBall (0 : E) ε', ‖y‖ < ε := fun y hy => by
    rw [mem_closedBall, dist_zero_right] at hy; linarith
  refine injOn_add_image i Φ (fun y hy => hd y (hm y hy)) (fun y hy => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
  have := hb y (hm y hy) h
  simp only [ContinuousLinearMap.comp_apply]
  linarith [norm_nonneg h]

end GenericLocal

section ConcreteLocal

variable {lower upper : ℝ}

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

/-- **Ramer Step 4, local form.**  No global `T`; the local map is `y ↦ y + i (K y)`. -/
theorem ramer_step4_local (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 1 K) (x₀ : FullWeightedHilbert c s)
    (Tt : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (B : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (hTts : ∀ y, Tt.symm y = y + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
        (B y))
    (hv : ∀ u, fderiv ℝ K x₀ u + B (u + cmToFullWeightedHilbert c s
        (le_of_lt (by linarith : 0 < s)) (fderiv ℝ K x₀ u)) = 0) :
  ∃ ε : ℝ, 0 < ε ∧ ∃ d : ℝ, 0 < d ∧ ∃ e₁ e₂ : ActualCM c,
        e₂ = -e₁ + K x₀ + B (x₀ + cmToFullWeightedHilbert c s
          (le_of_lt (by linarith : 0 < s)) (K x₀)) ∧
        (∀ y, Tt.symm ((y - cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) e₁) +
              cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
                (K (y - cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) e₁)))
            - cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) e₂ =
          y + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
            (K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K
              B e₁ e₂ y)) ∧
        (∀ y, ‖y‖ < ε →
          ‖K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K
              B e₁ e₂ y‖ < d) ∧
        (∀ y, ‖y‖ < ε →
          ‖hsDerivH c s hs (K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K
              B e₁ e₂) y‖ < d) ∧
        (∀ y, ‖y‖ < ε →
          ‖hsDerivH c s hs (K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K
              B e₁ e₂) y‖ < 1 / 8) ∧
        (∀ y, ‖y‖ < ε → ∀ h : ActualCM c,
          ‖fderiv ℝ (K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K
              B e₁ e₂) y
              (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h)‖ ≤ 1 / 8 * ‖h‖) ∧
        ‖x₀ + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) e₁‖ < ε / 2 ∧
        K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K
          B e₁ e₂
          (x₀ + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) e₁) = 0 := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith : 0 < s)
  set i := cmToFullWeightedHilbert c s hs0 with hi
  have hdense : DenseRange i := cmToFullWeightedHilbert_denseRange c s hs0
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  set G := Gmap i K B x₀ with hG
  have hG0 : G x₀ = 0 := Gmap_self i K B x₀
  have hGc : ContDiff ℝ 1 G := contDiff_Gmap i K B x₀ hK
  have hH0 : hsDerivH c s hs G x₀ = 0 := by
    apply HilbertSchmidt.ext
    intro v
    have := congrArg (fun f => f v) (hsDerivH_toCLM c s hs G x₀)
    rw [this]
    exact fderiv_Gmap_comp_zero i K B x₀ (hKd x₀) hv v
  have hcont := continuous_hsDerivH c s hs G hGc
  have ev1 : ∀ᶠ z in 𝓝 x₀, ‖hsDerivH c s hs G z‖ < 1 / 8 :=
    (continuous_norm.comp hcont).continuousAt.eventually
      (gt_mem_nhds (by simp [hH0]))
  have ev2 : ∀ᶠ z in 𝓝 x₀, ‖G z‖ < 1 :=
    (continuous_norm.comp hGc.continuous).continuousAt.eventually
      (gt_mem_nhds (by show ‖G x₀‖ < 1; rw [hG0]; simp))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (ev1.and ev2)
  set ε := 2 * r / 3 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨e₁, he₁⟩ := hdense.exists_dist_lt (-x₀) (by positivity : 0 < ε / 2)
  have hy0 : ‖x₀ + i e₁‖ < ε / 2 := by
    rw [dist_eq_norm] at he₁
    have : x₀ + i e₁ = -(-x₀ - i e₁) := by abel
    rw [this, norm_neg]; exact he₁
  have hnear : ∀ y : FullWeightedHilbert c s, ‖y‖ < ε → dist (y - i e₁) x₀ < r := by
    intro y hy
    rw [dist_eq_norm]
    have h2 : y - i e₁ - x₀ = y - (x₀ + i e₁) := by abel
    rw [h2]
    calc ‖y - (x₀ + i e₁)‖ ≤ ‖y‖ + ‖x₀ + i e₁‖ := norm_sub_le _ _
      _ < r := by rw [hε] at hy hy0; linarith
  have hKeq := K2_eq_Gmap_local i K B x₀ e₁
  have hsT : ∀ y, hsDerivH c s hs (K2 i K B e₁ (-e₁ + K x₀ + B (x₀ + i (K x₀)))) y =
      hsDerivH c s hs G (y - i e₁) := by
    intro y
    unfold hsDerivH
    congr 1
    exact (congrArg (fun F => fderiv ℝ F y) hKeq).trans (fderiv_comp_sub (f := G) (x := y) (i e₁))
  refine ⟨ε, hεpos, 1, one_pos, e₁, -e₁ + K x₀ + B (x₀ + i (K x₀)), rfl,
    fun y => K2_identity_local i K Tt B hTts e₁ _ y, ?_, ?_, ?_, ?_, hy0, ?_⟩
  · intro y hy
    exact (congrArg (fun v => ‖v‖) (congrFun hKeq y)).trans_lt (hball (hnear y hy)).2
  · intro y hy
    have h1 := hsT y
    rw [h1]
    exact lt_trans (hball (hnear y hy)).1 (by norm_num)
  · intro y hy
    have h1 := hsT y
    rw [h1]
    exact (hball (hnear y hy)).1
  · intro y hy h
    have h1 := hsT y
    have h2 : (hsDerivH c s hs (K2 i K B e₁ (-e₁ + K x₀ + B (x₀ + i (K x₀)))) y).toCLM h =
        fderiv ℝ (K2 i K B e₁ (-e₁ + K x₀ + B (x₀ + i (K x₀)))) y (i h) :=
      congrArg (fun f => f h) (hsDerivH_toCLM c s hs
        (K2 i K B e₁ (-e₁ + K x₀ + B (x₀ + i (K x₀)))) y)
    rw [← h2]
    have h3 := hs_apply_le (hsDerivH c s hs
      (K2 i K B e₁ (-e₁ + K x₀ + B (x₀ + i (K x₀)))) y) h
    have h4 : ‖hsDerivH c s hs (K2 i K B e₁ (-e₁ + K x₀ + B (x₀ + i (K x₀)))) y‖ < 1 / 8 := by
      rw [h1]; exact (hball (hnear y hy)).1
    calc _ ≤ _ := h3
      _ ≤ 1 / 8 * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right h4.le (norm_nonneg _)
  · have e : x₀ + i e₁ - i e₁ = x₀ := by abel
    exact (congrFun hKeq (x₀ + i e₁)).trans ((congrArg (Gmap i K B x₀) e).trans
      (Gmap_self i K B x₀))

/-- Injectivity of `T' y = y + i (K2 y)` on `closedBall 0 ε'`, for any `ε' < ε`, where `ε` is
the radius of the `1/8` fibre bound of `ramer_step4_local`.  Uses R6 only (no global `T`). -/
theorem injOn_T'_local (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 1 K) (B : FullWeightedHilbert c s →L[ℝ] ActualCM c) (e₁ e₂ : ActualCM c)
    {ε ε' : ℝ} (hε' : ε' < ε)
    (hb : ∀ y : FullWeightedHilbert c s, ‖y‖ < ε → ∀ h : ActualCM c,
        ‖fderiv ℝ (K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K
              B e₁ e₂) y
              (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h)‖ ≤ 1 / 8 * ‖h‖) :
    InjOn (fun y => y + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
        (K2 (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) K B e₁ e₂ y))
      (closedBall (0 : FullWeightedHilbert c s) ε') := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith : 0 < s)
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hd : Differentiable ℝ (K2 (cmToFullWeightedHilbert c s hs0) K B e₁ e₂) := by
    intro y
    unfold K2
    have h1 : DifferentiableAt ℝ (fun y => K (y - cmToFullWeightedHilbert c s hs0 e₁)) y :=
      (hKd _).comp y (differentiableAt_id.sub_const _)
    exact ((differentiableAt_const _).add h1).add
      (B.differentiableAt.comp y ((differentiableAt_id.sub_const _).add
        ((cmToFullWeightedHilbert c s hs0).differentiableAt.comp y h1)))
  exact injOn_T'_local_generic (cmToFullWeightedHilbert c s hs0) _ hε' (fun y _ => hd y) hb

end ConcreteLocal

end NlsGge.Ramer
