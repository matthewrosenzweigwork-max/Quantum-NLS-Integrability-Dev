import NlsGge.Ramer.General.SpaceTransferG
import NlsGge.Ramer.General.HypothesisBridgeG
import NlsGge.Ramer.General.RamerDensityG
import NlsGge.Ramer.General.RamerStep5G

/-!
# Ramer Steps 3-4 (v2 simplification of Lemma 5.1), over a `RamerSetting` (GD5)

Adapted from `NlsGge/Ramer/RamerStep4.lean`.  With `T = I + i∘K`, `T⁻¹ = I + i∘K'`,
`T̃ := DT(x₀) = I + i∘D K(x₀)` is a continuous linear equivalence of `S.E` with inverse
`I + i∘B`, `B = D K'(T x₀)`.  With `T₁ = τ_{e₁}`, `T₂ = T̃ ∘ τ_{e₂}` we get
`T₂⁻¹ (T (T₁⁻¹ y)) = y + i (K'' y)`.

The generic part (any `i : H →L E`) is copied into `NlsGge.Ramer.Gen`; the concrete part is over
`S : RamerSetting`, with `i = S.incl` and the Hilbert-Schmidt derivative `S.hsDerivH`.
No hypothesis `hs` is needed: `S.incl` is injective with dense range and Hilbert-Schmidt by G0.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace NlsGge.Ramer.Gen

section Generic

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] (i : H →L[ℝ] E)

/-- Lemma 5.1 (trivial form), together with the vanishing `A + B (I + iA) = 0`. -/
theorem exists_linearization (hinj : Function.Injective i)
    (T : E ≃ₜ E) (K K' : E → H)
    (hT : ∀ x, T x = x + i (K x)) (hTs : ∀ y, T.symm y = y + i (K' y))
    (hK : Differentiable ℝ K) (hK' : Differentiable ℝ K') (x₀ : E) :
    ∃ Tt : E ≃L[ℝ] E,
      (∀ x, Tt x = x + i (fderiv ℝ K x₀ x)) ∧
      (∀ y, Tt.symm y = y + i (fderiv ℝ K' (T x₀) y)) ∧
      ∀ u, fderiv ℝ K x₀ u + fderiv ℝ K' (T x₀) (u + i (fderiv ℝ K x₀ u)) = 0 := by
  have hTf : (T : E → E) = fun y => y + i (K y) := funext hT
  have hTsf : (T.symm : E → E) = fun y => y + i (K' y) := funext hTs
  set A := fderiv ℝ K x₀
  set B := fderiv ℝ K' (T x₀)
  have dT : HasFDerivAt (T : E → E) (ContinuousLinearMap.id ℝ E + i.comp A) x₀ := by
    rw [hTf]
    exact (hasFDerivAt_id x₀).add (i.hasFDerivAt.comp x₀ (hK x₀).hasFDerivAt)
  have dTs : HasFDerivAt (T.symm : E → E) (ContinuousLinearMap.id ℝ E + i.comp B) (T x₀) := by
    rw [hTsf]
    exact (hasFDerivAt_id (T x₀)).add (i.hasFDerivAt.comp (T x₀) (hK' (T x₀)).hasFDerivAt)
  have h1 : (ContinuousLinearMap.id ℝ E + i.comp B).comp
      (ContinuousLinearMap.id ℝ E + i.comp A) = ContinuousLinearMap.id ℝ E := by
    have hc := dTs.comp x₀ dT
    have hid : HasFDerivAt ((T.symm : E → E) ∘ T) (ContinuousLinearMap.id ℝ E) x₀ := by
      have : ((T.symm : E → E) ∘ T) = id := by funext y; simp
      rw [this]; exact hasFDerivAt_id x₀
    exact hc.unique hid
  have h2 : (ContinuousLinearMap.id ℝ E + i.comp A).comp
      (ContinuousLinearMap.id ℝ E + i.comp B) = ContinuousLinearMap.id ℝ E := by
    have dT' : HasFDerivAt (T : E → E) (ContinuousLinearMap.id ℝ E + i.comp A)
        (T.symm (T x₀)) := by simpa using dT
    have hc := dT'.comp (T x₀) dTs
    have hid : HasFDerivAt ((T : E → E) ∘ T.symm) (ContinuousLinearMap.id ℝ E) (T x₀) := by
      have : ((T : E → E) ∘ T.symm) = id := by funext y; simp
      rw [this]; exact hasFDerivAt_id (T x₀)
    exact hc.unique hid
  refine ⟨ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.id ℝ E + i.comp A) (ContinuousLinearMap.id ℝ E + i.comp B)
    (fun u => congrArg (fun L : E →L[ℝ] E => L u) h1)
    (fun u => congrArg (fun L : E →L[ℝ] E => L u) h2),
    fun x => rfl, fun y => rfl, ?_⟩
  intro u
  apply hinj
  have := congrArg (fun L : E →L[ℝ] E => L u) h1
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, map_add] at this
  rw [← sub_eq_zero] at this
  simp only [map_add, map_zero]
  convert this using 1
  abel

/-- The map `G z = K z + B (z + i K z) - (K x₀ + B (x₀ + i K x₀))`, so that
`K'' y = G (y - i e₁)`. -/
def Gmap (K : E → H) (B : E →L[ℝ] H) (x₀ : E) (z : E) : H :=
  K z + B (z + i (K z)) - (K x₀ + B (x₀ + i (K x₀)))

theorem hasFDerivAt_Gmap (K : E → H) (B : E →L[ℝ] H) (x₀ z : E)
    (hK : DifferentiableAt ℝ K z) :
    HasFDerivAt (Gmap i K B x₀)
      (fderiv ℝ K z + B.comp (ContinuousLinearMap.id ℝ E + i.comp (fderiv ℝ K z))) z := by
  have h := (hK.hasFDerivAt.add (B.hasFDerivAt.comp z
    ((hasFDerivAt_id z).add (i.hasFDerivAt.comp z hK.hasFDerivAt)))).sub_const
    (K x₀ + B (x₀ + i (K x₀)))
  exact h

theorem contDiff_Gmap (K : E → H) (B : E →L[ℝ] H) (x₀ : E) (hK : ContDiff ℝ 1 K) :
    ContDiff ℝ 1 (Gmap i K B x₀) := by
  unfold Gmap
  exact (hK.add (B.contDiff.comp (contDiff_id.add (i.contDiff.comp hK)))).sub contDiff_const

theorem fderiv_Gmap_comp_zero (K : E → H) (B : E →L[ℝ] H)
    (x₀ : E) (hK : DifferentiableAt ℝ K x₀)
    (hv : ∀ u, fderiv ℝ K x₀ u + B (u + i (fderiv ℝ K x₀ u)) = 0) (v : H) :
    fderiv ℝ (Gmap i K B x₀) x₀ (i v) = 0 := by
  rw [(hasFDerivAt_Gmap i K B x₀ x₀ hK).fderiv]
  simpa using hv (i v)

theorem Gmap_self (K : E → H) (B : E →L[ℝ] H) (x₀ : E) : Gmap i K B x₀ x₀ = 0 := by
  simp [Gmap]

/-- `K''` of Ramer's Step 4. -/
def K2 (K : E → H) (B : E →L[ℝ] H) (e₁ e₂ : H) (y : E) : H :=
  -e₁ - e₂ + K (y - i e₁) + B (y - i e₁ + i (K (y - i e₁)))

/-- `T₂⁻¹ ∘ T ∘ T₁⁻¹ = I + i ∘ K''`, with `T₁⁻¹ y = y - i e₁`, `T₂⁻¹ w = T̃⁻¹ w - i e₂`. -/
theorem K2_identity (T : E ≃ₜ E) (K : E → H) (hT : ∀ x, T x = x + i (K x))
    (Tt : E ≃L[ℝ] E) (B : E →L[ℝ] H) (hTt : ∀ y, Tt.symm y = y + i (B y)) (e₁ e₂ : H) (y : E) :
    Tt.symm (T (y - i e₁)) - i e₂ = y + i (K2 i K B e₁ e₂ y) := by
  rw [hTt, hT]
  simp only [K2, map_add, map_sub, map_neg]
  abel

theorem K2_eq_Gmap (T : E ≃ₜ E) (K : E → H) (hT : ∀ x, T x = x + i (K x))
    (B : E →L[ℝ] H) (x₀ : E) (e₁ : H) :
    K2 i K B e₁ (-e₁ + K x₀ + B (T x₀)) = fun y => Gmap i K B x₀ (y - i e₁) := by
  funext y
  simp only [K2, Gmap, hT]
  abel

end Generic

section HSGeneric

open NlsGge.Analysis.RegularizedDeterminant

theorem hs_apply_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : HilbertSchmidt E F) (x : E) : ‖T.toCLM x‖ ≤ ‖T‖ * ‖x‖ :=
  (T.toCLM.le_opNorm x).trans (mul_le_mul_of_nonneg_right (HilbertSchmidt.opNorm_le T)
    (norm_nonneg _))

end HSGeneric
end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Analysis.RegularizedDeterminant

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- **Ramer Step 4 core (over `S`).**  (Old: `ramer_step4_core`; the hypothesis `hs` is gone.) -/
theorem ramer_step4_core
    (T : S.E ≃ₜ S.E)
    (K : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hK : ContDiff ℝ 1 K) (x₀ : S.E)
    (Tt : S.E ≃L[ℝ] S.E)
    (B : S.E →L[ℝ] S.H)
    (hTts : ∀ y, Tt.symm y = y + S.incl (B y))
    (hv : ∀ u, fderiv ℝ K x₀ u + B (u + S.incl (fderiv ℝ K x₀ u)) = 0) :
  ∃ ε : ℝ, 0 < ε ∧ ∃ d : ℝ, 0 < d ∧ ∃ e₁ e₂ : S.H,
        e₂ = -e₁ + K x₀ + B (T x₀) ∧
        (∀ y, Tt.symm (T (y - S.incl e₁)) - S.incl e₂ =
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
  have hKeq := Gen.K2_eq_Gmap S.incl T K hT B x₀ e₁
  have hsT : ∀ y, S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (T x₀))) y =
      S.hsDerivH G (y - S.incl e₁) := by
    intro y
    unfold hsDerivH
    congr 1
    exact (congrArg (fun F => fderiv ℝ F y) hKeq).trans
      (fderiv_comp_sub (f := G) (x := y) (S.incl e₁))
  refine ⟨ε, hεpos, 1, one_pos, e₁, -e₁ + K x₀ + B (T x₀), rfl,
    fun y => Gen.K2_identity S.incl T K hT Tt B hTts e₁ _ y, ?_, ?_, ?_, ?_, hy0, ?_⟩
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
    have h2 : (S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (T x₀))) y).toCLM h =
        fderiv ℝ (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (T x₀))) y (S.incl h) :=
      congrArg (fun f => f h) (S.hsDerivH_toCLM
        (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (T x₀))) y)
    rw [← h2]
    have h3 := Gen.hs_apply_le (S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (T x₀))) y) h
    have h4 : ‖S.hsDerivH (Gen.K2 S.incl K B e₁ (-e₁ + K x₀ + B (T x₀))) y‖ < 1 / 8 := by
      rw [h1]; exact (hball (hnear y hy)).1
    calc _ ≤ _ := h3
      _ ≤ 1 / 8 * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right h4.le (norm_nonneg _)
  · have e : x₀ + S.incl e₁ - S.incl e₁ = x₀ := by abel
    exact (congrFun hKeq (x₀ + S.incl e₁)).trans ((congrArg (Gen.Gmap S.incl K B x₀) e).trans
      (Gen.Gmap_self S.incl K B x₀))

/-- **Ramer Step 4 (v2), over `S`.**  (Old: `ramer_step4`.) -/
theorem ramer_step4
    (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K') (x₀ : S.E) :
    ∃ Tt : S.E ≃L[ℝ] S.E,
      (∀ x, Tt x = x + S.incl (fderiv ℝ K x₀ x)) ∧
      (∀ y, Tt.symm y = y + S.incl (fderiv ℝ K' (T x₀) y)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ d : ℝ, 0 < d ∧ ∃ e₁ e₂ : S.H,
        e₂ = -e₁ + K x₀ + fderiv ℝ K' (T x₀) (T x₀) ∧
        (∀ y, Tt.symm (T (y - S.incl e₁)) - S.incl e₂ =
          y + S.incl (Gen.K2 S.incl K (fderiv ℝ K' (T x₀)) e₁ e₂ y)) ∧
        (∀ y, ‖y‖ < ε → ‖Gen.K2 S.incl K (fderiv ℝ K' (T x₀)) e₁ e₂ y‖ < d) ∧
        (∀ y, ‖y‖ < ε →
          ‖S.hsDerivH (Gen.K2 S.incl K (fderiv ℝ K' (T x₀)) e₁ e₂) y‖ < d) ∧
        (∀ y, ‖y‖ < ε →
          ‖S.hsDerivH (Gen.K2 S.incl K (fderiv ℝ K' (T x₀)) e₁ e₂) y‖ < 1 / 8) ∧
        (∀ y, ‖y‖ < ε → ∀ h : S.H,
          ‖fderiv ℝ (Gen.K2 S.incl K (fderiv ℝ K' (T x₀)) e₁ e₂) y (S.incl h)‖ ≤ 1 / 8 * ‖h‖) ∧
        ‖x₀ + S.incl e₁‖ < ε / 2 ∧
        Gen.K2 S.incl K (fderiv ℝ K' (T x₀)) e₁ e₂ (x₀ + S.incl e₁) = 0 := by
  obtain ⟨Tt, hTt, hTts, hv⟩ := Gen.exists_linearization S.incl S.incl_injective T K K'
    hT hTs (hK.differentiable (by norm_num)) (hK'.differentiable (by norm_num)) x₀
  exact ⟨Tt, hTt, hTts, S.ramer_step4_core T K hT hK x₀ Tt _ hTts hv⟩

end NlsGge.Ramer.General.RamerSetting
