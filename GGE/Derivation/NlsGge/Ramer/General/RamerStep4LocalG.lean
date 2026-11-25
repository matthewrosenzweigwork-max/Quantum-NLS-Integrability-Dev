import NlsGge.Ramer.General.RamerStep4G
import NlsGge.Ramer.RamerLemma52

/-!
# Ramer Step 4, local form, over a `RamerSetting` (GD5)

Adapted from `NlsGge/Ramer/RamerStep4Local.lean`.  `ramer_step4_local` is `ramer_step4_core` for
the local map `y ↦ y + i (K y)`, with no global homeomorphism `T`.  `Tt`, `B`, `hv` are
hypotheses.  `injOn_T'_local` is injectivity of `y ↦ y + i (K2 y)` on a closed ball, via
`injOn_add_image` (generic, imported from `RamerLemma52`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Set

namespace NlsGge.Ramer.Gen

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
end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Analysis.RegularizedDeterminant

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- **Ramer Step 4, local form over `S`.**  No global `T`; the local map is `y ↦ y + i (K y)`.
(Old: `ramer_step4_local`; the hypothesis `hs` is gone.) -/
theorem ramer_step4_local
    (K : S.E → S.H)
    (hK : ContDiff ℝ 1 K) (x₀ : S.E)
    (Tt : S.E ≃L[ℝ] S.E)
    (B : S.E →L[ℝ] S.H)
    (hTts : ∀ y, Tt.symm y = y + S.incl (B y))
    (hv : ∀ u, fderiv ℝ K x₀ u + B (u + S.incl (fderiv ℝ K x₀ u)) = 0) :
  ∃ ε : ℝ, 0 < ε ∧ ∃ d : ℝ, 0 < d ∧ ∃ e₁ e₂ : S.H,
        e₂ = -e₁ + K x₀ + B (x₀ + S.incl (K x₀)) ∧
        (∀ y, Tt.symm ((y - S.incl e₁) + S.incl (K (y - S.incl e₁))) - S.incl e₂ =
          y + S.incl (Gen.K2 S.incl K B e₁ e₂ y)) ∧
        (∀ y, ‖y‖ < ε → ‖Gen.K2 S.incl K B e₁ e₂ y‖ < d) ∧
        (∀ y, ‖y‖ < ε → ‖S.hsDerivH (Gen.K2 S.incl K B e₁ e₂) y‖ < d) ∧
        (∀ y, ‖y‖ < ε → ‖S.hsDerivH (Gen.K2 S.incl K B e₁ e₂) y‖ < 1 / 8) ∧
        (∀ y, ‖y‖ < ε → ∀ h : S.H,
          ‖fderiv ℝ (Gen.K2 S.incl K B e₁ e₂) y (S.incl h)‖ ≤ 1 / 8 * ‖h‖) ∧
        ‖x₀ + S.incl e₁‖ < ε / 2 ∧
        Gen.K2 S.incl K B e₁ e₂ (x₀ + S.incl e₁) = 0 := by
  have hdense : DenseRange S.incl := S.incl_denseRange
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  set G := Gen.Gmap S.incl K B x₀ with hG
  have hG0 : G x₀ = 0 := Gen.Gmap_self S.incl K B x₀
  have hGc : ContDiff ℝ 1 G := Gen.contDiff_Gmap S.incl K B x₀ hK
  have hH0 : S.hsDerivH G x₀ = 0 := by
    apply HilbertSchmidt.ext
    intro v
    have := congrArg (fun f => f v) (S.hsDerivH_toCLM G x₀)
    rw [this]
    exact Gen.fderiv_Gmap_comp_zero S.incl K B x₀ (hKd x₀) hv v
  have hcont := S.continuous_hsDerivH G hGc
  have ev1 : ∀ᶠ z in 𝓝 x₀, ‖S.hsDerivH G z‖ < 1 / 8 :=
    (continuous_norm.comp hcont).continuousAt.eventually
      (gt_mem_nhds (by simp [hH0]))
  have ev2 : ∀ᶠ z in 𝓝 x₀, ‖G z‖ < 1 :=
    (continuous_norm.comp hGc.continuous).continuousAt.eventually
      (gt_mem_nhds (by show ‖G x₀‖ < 1; rw [hG0]; simp))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (ev1.and ev2)
  set ε := 2 * r / 3 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨e₁, he₁⟩ := hdense.exists_dist_lt (-x₀) (by positivity : 0 < ε / 2)
  have hy0 : ‖x₀ + S.incl e₁‖ < ε / 2 := by
    rw [dist_eq_norm] at he₁
    have : x₀ + S.incl e₁ = -(-x₀ - S.incl e₁) := by abel
    rw [this, norm_neg]; exact he₁
  have hnear : ∀ y : S.E, ‖y‖ < ε → dist (y - S.incl e₁) x₀ < r := by
    intro y hy
    rw [dist_eq_norm]
    have h2 : y - S.incl e₁ - x₀ = y - (x₀ + S.incl e₁) := by abel
    rw [h2]
    calc ‖y - (x₀ + S.incl e₁)‖ ≤ ‖y‖ + ‖x₀ + S.incl e₁‖ := norm_sub_le _ _
      _ < r := by rw [hε] at hy hy0; linarith
  have hKeq := Gen.K2_eq_Gmap_local S.incl K B x₀ e₁
  have hsT : ∀ y, S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (x₀ + S.incl (K x₀)))) y =
      S.hsDerivH G (y - S.incl e₁) := by
    intro y
    unfold hsDerivH
    congr 1
    exact (congrArg (fun F => fderiv ℝ F y) hKeq).trans
      (fderiv_comp_sub (f := G) (x := y) (S.incl e₁))
  refine ⟨ε, hεpos, 1, one_pos, e₁, -e₁ + K x₀ + B (x₀ + S.incl (K x₀)), rfl,
    fun y => Gen.K2_identity_local S.incl K Tt B hTts e₁ _ y, ?_, ?_, ?_, ?_, hy0, ?_⟩
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
    have h2 : (S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (x₀ + S.incl (K x₀)))) y).toCLM h =
        fderiv ℝ (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (x₀ + S.incl (K x₀)))) y (S.incl h) :=
      congrArg (fun f => f h) (S.hsDerivH_toCLM
        (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (x₀ + S.incl (K x₀)))) y)
    rw [← h2]
    have h3 := Gen.hs_apply_le (S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (x₀ + S.incl (K x₀)))) y) h
    have h4 : ‖S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (x₀ + S.incl (K x₀)))) y‖ < 1 / 8 := by
      rw [h1]; exact (hball (hnear y hy)).1
    calc _ ≤ _ := h3
      _ ≤ 1 / 8 * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right h4.le (norm_nonneg _)
  · have e : x₀ + S.incl e₁ - S.incl e₁ = x₀ := by abel
    exact (congrFun hKeq (x₀ + S.incl e₁)).trans ((congrArg (Gen.Gmap S.incl K B x₀) e).trans
      (Gen.Gmap_self S.incl K B x₀))

/-- Injectivity of `T' y = y + i (K2 y)` on `closedBall 0 ε'`, for any `ε' < ε`, where `ε` is
the radius of the `1/8` fibre bound of `ramer_step4_local`.  (Old: `injOn_T'_local`.) -/
theorem injOn_T'_local
    (K : S.E → S.H)
    (hK : ContDiff ℝ 1 K) (B : S.E →L[ℝ] S.H) (e₁ e₂ : S.H)
    {ε ε' : ℝ} (hε' : ε' < ε)
    (hb : ∀ y : S.E, ‖y‖ < ε → ∀ h : S.H,
        ‖fderiv ℝ (Gen.K2 S.incl K B e₁ e₂) y (S.incl h)‖ ≤ 1 / 8 * ‖h‖) :
    InjOn (fun y => y + S.incl (Gen.K2 S.incl K B e₁ e₂ y))
      (closedBall (0 : S.E) ε') := by
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hd : Differentiable ℝ (Gen.K2 S.incl K B e₁ e₂) := by
    intro y
    unfold Gen.K2
    have h1 : DifferentiableAt ℝ (fun y => K (y - S.incl e₁)) y :=
      (hKd _).comp y (differentiableAt_id.sub_const _)
    exact ((differentiableAt_const _).add h1).add
      (B.differentiableAt.comp y ((differentiableAt_id.sub_const _).add
        (S.incl.differentiableAt.comp y h1)))
  exact Gen.injOn_T'_local_generic S.incl _ hε' (fun y _ => hd y) hb

end NlsGge.Ramer.General.RamerSetting
