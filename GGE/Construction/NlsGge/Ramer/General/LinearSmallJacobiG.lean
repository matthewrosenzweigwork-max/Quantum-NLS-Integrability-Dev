import Mathlib
import NlsGge.Ramer.General.LinearSmallJacobiLocalG
import NlsGge.Ramer.General.CameronMartinEG
import NlsGge.Ramer.LocalJacobiExtension
import NlsGge.Ramer.RamerStep1Locality

/-!
# D2, steps 3-4: the global Jacobi formula for the linear small `Q`, generalized (GE3)

Adapted from `NlsGge/Ramer/LinearSmallJacobi.lean`.  Dictionary: `c, s, hs ↦ S`,
`FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `inclE ↦ S.incl`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `TM c s hs ↦ S.TM`, `ramerJac c s hs ↦ S.ramerJac`,
`headProj c / tailProj c ↦ S.headProj / S.tailProj`, `SameTail c s ↦ S.SameTail`,
`aemeasurable_constDensity ↦ S.aemeasurable_constDensity` (GD13),
`quasiMeasurePreserving_add_inclE ↦ S.quasiMeasurePreserving_add_incl` (G2),
`lintegral_image_add_inclE ↦ S.lintegral_image_add_incl` (GD13).

The linear equivalence called `S` in the old file is called `Q` here (`S` is the setting).
No isotropy is used.

From the local formula near `0` (GE2), Cameron-Martin translations (GD13) and Ramer's Lemma 5.4
(GD12) we obtain `(*)` near every point and globalize with `map_symm_eq_withDensity_of_local`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- **Global form from the local one**, for a linear field `L` and `Q = I + iL`. -/
theorem global_of_local (L : S.E →L[ℝ] S.H)
    (Q : S.E ≃L[ℝ] S.E)
    (hS : ∀ x, Q x = x + S.incl (L x)) (ρ : ℝ) (hρ : 0 < ρ)
    (J : S.E → ℝ≥0∞) (hJ : Measurable J)
    (hJae : J =ᵐ[S.γE]
      fun x => ENNReal.ofReal (S.ramerJac (fun y => L y) x))
    (hloc : LocalJacobiUC (S.γE)
      (Q.toHomeomorph : S.E ≃ₜ S.E) J
      (ball (0 : S.E) ρ))
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE
        (ball (0 : S.E) ρ ∩ S.TM (fun y => L y) ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE
        (ball (0 : S.E) ρ ∩
          S.TM (S.projField k (fun y => L y)) ⁻¹' N) = 0) :
    (S.γE).map Q.symm =
      (S.γE).withDensity J := by
  set γ := S.γE with hγ
  have : IsFiniteMeasure γ := by rw [hγ]; infer_instance
  have hLd : ContDiff ℝ 2 (fun y => L y) := L.contDiff
  refine map_symm_eq_withDensity_of_local γ Q.toHomeomorph J hJ ?_
  intro x₀
  have hdense : DenseRange (S.incl) :=
    S.incl_denseRange
  obtain ⟨e, he⟩ : ∃ e : S.H, dist x₀ (S.incl e) < ρ := by
    have := hdense x₀
    rw [Metric.mem_closure_iff] at this
    obtain ⟨_, ⟨e, rfl⟩, h⟩ := this ρ hρ
    exact ⟨e, h⟩
  set V₀ : Set (S.E) := ball 0 ρ with hV₀
  set V : Set (S.E) := (fun x => x + S.incl e) '' V₀ with hV
  have hV₀o : IsOpen V₀ := isOpen_ball
  have hVo : IsOpen V := (Homeomorph.addRight (S.incl e)).isOpenMap _ hV₀o
  have hVm : MeasurableSet V := hVo.measurableSet
  have hx₀ : x₀ ∈ V := ⟨x₀ - S.incl e, by
    rw [hV₀, mem_ball_zero_iff, ← dist_eq_norm]; exact he, sub_add_cancel _ _⟩
  refine ⟨V, hVo, hx₀, ?_⟩
  set d : S.H := -e with hd
  set e' : S.H := e + L (S.incl e) with he'
  have hSe : ∀ x, Q (x + S.incl e) = Q x + S.incl e' := by
    intro x
    rw [map_add, hS (S.incl e), he', map_add]
  have hSd : ∀ x, Q (x + S.incl d) + S.incl e' = Q x := by
    intro x
    have := hSe (x + S.incl d)
    rw [add_assoc, ← map_add, hd, neg_add_cancel, map_zero, add_zero] at this
    rw [← this]
  have hVd : (fun x => x + S.incl d) '' V = V₀ := by
    rw [hV, Set.image_image]
    ext y; simp [hd]
  have hSV : Q.toHomeomorph '' V = (fun y => y + S.incl e') '' (Q.toHomeomorph '' V₀) := by
    rw [hV, Set.image_image, Set.image_image]
    exact Set.image_congr (fun x _ => hSe x)
  have hSV₀m : MeasurableSet (Q.toHomeomorph '' V₀) :=
    (Q.toHomeomorph.isOpenMap V₀ hV₀o).measurableSet
  -- measurable representative of the Cameron–Martin density for `e'`
  have hmc := S.aemeasurable_constDensity e'
  set Jc' := hmc.mk with hJc'def
  have hJc'm : Measurable Jc' := hmc.measurable_mk
  have hJc'ae : Jc' =ᵐ[γ] fun x => ENNReal.ofReal (S.ramerJac (fun _ => e') x) :=
    hmc.ae_eq_mk.symm
  -- the field of `M = Q ∘ τ_{-ie}`
  set KM : S.E → S.H :=
    (fun _ => d) + (fun y => L y) ∘ S.TM (fun _ => d) with hKM
  have hKMd : ContDiff ℝ 2 KM :=
    contDiff_const.add (hLd.comp (S.contDiff_TM _ contDiff_const))
  have hTMd : ∀ x, S.TM (fun _ => d) x = x + S.incl d := fun x => rfl
  have hTMKM : ∀ x, S.TM KM x = S.TM (fun y => L y) (x + S.incl d) := by
    intro x
    simp only [TM, hKM, Pi.add_apply, Function.comp_apply, map_add]
    abel
  have hTMS : ∀ x, S.TM (fun y => L y) x = Q x := fun x => (hS x).symm
  -- null preservation of the inner maps on `V`
  have hT' : ∀ N : Set (S.E), γ N = 0 → γ (V ∩ S.TM KM ⁻¹' N) = 0 := by
    intro N hN
    refine measure_mono_null ?_
      ((S.quasiMeasurePreserving_add_incl d).preimage_null (hT N hN))
    rintro x ⟨hxV, hxN⟩
    refine ⟨?_, ?_⟩
    · rw [← hVd]; exact ⟨x, hxV, rfl⟩
    · show S.TM (fun y => L y) (x + S.incl d) ∈ N
      rw [← hTMKM]; exact hxN
  have hTk' : ∀ k : ℕ, ∀ N : Set (S.E), γ N = 0 →
      γ (V ∩ S.TM (S.projField k KM) ⁻¹' N) = 0 := by
    intro k N hN
    have hN'' : γ ((fun y => y + S.incl (S.headProj k d - d)) ⁻¹' N) = 0 :=
      (S.quasiMeasurePreserving_add_incl (S.headProj k d - d)).preimage_null hN
    refine measure_mono_null ?_
      ((S.quasiMeasurePreserving_add_incl d).preimage_null (hTk k _ hN''))
    rintro x ⟨hxV, hxN⟩
    refine ⟨?_, ?_⟩
    · rw [← hVd]; exact ⟨x, hxV, rfl⟩
    · show S.TM (S.projField k fun y => L y) (x + S.incl d) +
        S.incl (S.headProj k d - d) ∈ N
      have : S.TM (S.projField k fun y => L y) (x + S.incl d) +
          S.incl (S.headProj k d - d) = S.TM (S.projField k KM) x := by
        simp only [TM, hKM, projField, Pi.add_apply, Function.comp_apply, map_add, map_sub]
        abel
      rw [this]; exact hxN
  -- (4a) and (4b)
  have h4a : ∀ᵐ x ∂γ, S.ramerJac KM x =
      S.ramerJac (fun y => L y) (x + S.incl d) *
        S.ramerJac (fun _ => d) x := by
    filter_upwards [S.ramer_lemma_5_4_eventually univ isOpen_univ (fun _ => d)
      (fun y => L y) contDiff_const hLd (S.hT_TM_const d univ)
      (S.hTk_TM_const_eventually d univ)] with x hx
    exact hx (mem_univ x)
  have hfun : KM + (fun _ => e') ∘ S.TM KM = fun y => L y := by
    funext x
    simp only [hKM, TM, Pi.add_apply, Function.comp_apply, map_add, map_neg, hd, he']
    abel
  have h4b : ∀ᵐ x ∂γ, x ∈ V → S.ramerJac (fun y => L y) x =
      S.ramerJac (fun _ => e') (Q (x + S.incl d)) * S.ramerJac KM x := by
    filter_upwards [S.ramer_lemma_5_4_eventually V hVo KM (fun _ => e') hKMd contDiff_const
      hT' (Filter.Eventually.of_forall hTk')] with x hx hxV
    have := hx hxV
    rw [hfun, hTMKM, hTMS] at this
    exact this
  have hc : ∀ᵐ x ∂γ, J (x + S.incl d) =
      ENNReal.ofReal (S.ramerJac (fun y => L y) (x + S.incl d)) :=
    (S.quasiMeasurePreserving_add_incl d).ae hJae
  have hdd : ∀ᵐ x ∂γ, x ∈ V → Jc' (Q (x + S.incl d)) =
      ENNReal.ofReal (S.ramerJac (fun _ => e') (Q (x + S.incl d))) := by
    have h0 : γ {y | ¬ Jc' y = ENNReal.ofReal (S.ramerJac (fun _ => e') y)} = 0 :=
      ae_iff.1 hJc'ae
    have h1 := hT' _ h0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx hxV
    by_contra hne
    exact hx ⟨hxV, by
      show ¬ _ = _
      rw [hTMKM, hTMS]; exact hne⟩
  have hkey : ∀ᵐ x ∂γ, x ∈ V →
      Jc' (Q (x + S.incl d)) * J (x + S.incl d) *
        ENNReal.ofReal (S.ramerJac (fun _ => d) x) = J x := by
    filter_upwards [h4a, h4b, hc, hdd, hJae] with x a b c' d' j hxV
    rw [d' hxV, c', j, b hxV, a, ENNReal.ofReal_mul (S.ramerJac_nonneg _ _),
      ENNReal.ofReal_mul (S.ramerJac_nonneg _ _), mul_assoc]
  -- the main chain
  have claim : ∀ G : S.E → ℝ≥0∞, Measurable G →
      ∫⁻ y in Q.toHomeomorph '' V, G y ∂γ = ∫⁻ x in V, G (Q.toHomeomorph x) * J x ∂γ := by
    intro G hG
    have hA := S.lintegral_image_add_incl e' G hG _ hSV₀m
    have hA' : ∫⁻ y in Q.toHomeomorph '' V₀, G (y + S.incl e') *
        ENNReal.ofReal (S.ramerJac (fun _ => e') y) ∂γ =
        ∫⁻ y in Q.toHomeomorph '' V₀, G (y + S.incl e') * Jc' y ∂γ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hJc'ae] with y hy
      rw [hy]
    have hHm : Measurable (fun y => G (y + S.incl e') * Jc' y) :=
      (hG.comp (measurable_id.add_const _)).mul hJc'm
    have hB := lintegral_image_eq_of_local_ext γ Q.toHomeomorph J hJ V₀ hV₀o hloc _ hHm
    have hH2m : Measurable (fun x => G (Q x + S.incl e') * Jc' (Q x) * J x) :=
      ((hG.comp (Q.continuous.measurable.add_const _)).mul
        (hJc'm.comp Q.continuous.measurable)).mul hJ
    have hC := S.lintegral_image_add_incl d _ hH2m V hVm
    rw [hVd] at hC
    rw [hSV, hA, hA', hB]
    refine (lintegral_congr fun x => rfl : _ = ∫⁻ x in V₀,
      G (Q x + S.incl e') * Jc' (Q x) * J x ∂γ).trans (hC.trans ?_)
    refine lintegral_congr_ae ((ae_restrict_iff' hVm).2 ?_)
    filter_upwards [hkey] with x hx hxV
    have := hx hxV
    show G (Q (x + S.incl d) + S.incl e') * Jc' (Q (x + S.incl d)) *
      J (x + S.incl d) * ENNReal.ofReal (S.ramerJac (fun _ => d) x) =
      G (Q x) * J x
    rw [hSd x, ← this]
    ring
  intro F hF1 hF2 hF3 hF4
  have hFm : Measurable F := hF1.continuous.measurable
  exact claim _ (ENNReal.measurable_ofReal.comp hFm)

/-- **D2 steps 3-4: the global Jacobi formula for the linear small `Q`.**
(Old: `linearSmall_map_symm`.) -/
theorem linearSmall_map_symm
    (K : S.E →L[ℝ] S.H)
    (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (Q Pi : S.E ≃L[ℝ] S.E)
      (M : S.E →L[ℝ] S.H),
      (∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, Q x = x + S.incl (S.tailProj n (K x))) ∧
      (∀ x, Q.symm x = x + S.incl (M x)) ∧
      (∀ x, M x = -(S.tailProj n (K (Q.symm x)))) ∧
      (∀ x, Pi x = T (Q.symm x)) ∧
      (∀ x, Pi x - x = S.incl (S.headProj n (K (Q.symm x)))) ∧
      (∀ x, S.SameTail n (Pi x) x) ∧
      ∃ J : S.E → ℝ≥0∞, Measurable J ∧
        (J =ᵐ[S.γE]
          fun x => ENNReal.ofReal (S.ramerJac (fun y => S.tailProj n (K y)) x)) ∧
        S.γE.map Q.symm = S.γE.withDensity J := by
  obtain ⟨κ0, hκ0, hK0⟩ := K.bound
  set κ := max κ0 0 with hκdef
  have hκ : 0 ≤ κ := le_max_right _ _
  have hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖ := fun y =>
    (hK0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ S.H
  have hi := S.incl_hs b
  obtain ⟨n₀, hn₀⟩ := Gen.exists_tail_small S (3 * κ * ε + 1) (ε / 2) (by linarith)
  obtain ⟨n, Q, Pi, M, hnn, hAi, hS, hSs, hM, hMi, hPi, hPi2⟩ :=
    linear_decomposition_ge S.incl b hi K T hT (S.headProj)
      (fun n x => S.norm_headProj_le n x) S.headProj_tendsto
      (S.tailProj) (S.tailProj_apply) n₀
  have hn' : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < 3 * κ * ε + 1 →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2 :=
    fun m hm h hh => hn₀ m (le_trans hnn hm) h hh
  have hAi' : ∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖ := hAi
  have hMi' : ∀ h : S.H, ‖M (S.incl h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖ := hMi
  have hS0 : ∀ x, Q x = x + S.incl (S.tailProj n (K x)) := hS
  have hM0 : ∀ x, M x = -(S.tailProj n (K (Q.symm x))) := hM
  have hPi3 : ∀ x, Pi x - x = S.incl (S.headProj n (K (Q.symm x))) := hPi2
  have hfix : ∀ x, S.SameTail n (Pi x) x := by
    intro x m hm
    have e : S.coord m (Pi x - x) = 0 := by
      rw [hPi3 x]; exact S.coord_incl_headProj n (K (Q.symm x)) m hm
    rw [S.coord_sub] at e
    exact sub_eq_zero.1 e
  obtain ⟨-, hcA⟩ := S.linearSmall_step8_S K κ hκ hK n hAi' ε hε hn'
  obtain ⟨-, hcM⟩ := S.linearSmall_step8_Sinv K Q M κ hκ hK n hAi' hSs hM0 hMi' ε hε hn'
  have hcAk := fun k => S.linearSmall_step8_proj K κ hκ hK n hAi' ε hε hn' k
  -- the radius
  obtain ⟨a0, -, ha0⟩ := S.incl.bound
  set a : ℝ := max a0 0 with ha
  have ha1 : 0 ≤ a := le_max_right _ _
  have ha2 : ∀ w, ‖S.incl w‖ ≤ a * ‖w‖ := fun w =>
    (ha0 w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set C : ℝ := 1 + a * (2 * κ) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ a * (2 * κ) := by positivity
    linarith
  set ρ : ℝ := ε / (2 * (C + 1)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρε : ρ ≤ ε / 2 := by
    rw [hρ]
    apply div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
  have hbound : ∀ x : S.E, ‖x‖ < ρ → ∀ w : S.H,
      ‖w‖ ≤ ‖S.tailProj n (K x)‖ → ‖x + S.incl w‖ < ε / 2 := by
    intro x hx w hw
    have h1 : ‖S.tailProj n (K x)‖ ≤ 2 * (κ * ‖x‖) :=
      (S.norm_tailProj_le n _).trans (by linarith [hK x])
    have h2 : ‖S.incl w‖ ≤ a * ‖w‖ := ha2 w
    have h4 : a * ‖w‖ ≤ a * (2 * (κ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hw.trans h1) ha1
    have h5 : ‖x + S.incl w‖ ≤ C * ‖x‖ := by
      calc _ ≤ ‖x‖ + ‖S.incl w‖ := norm_add_le _ _
        _ ≤ ‖x‖ + a * (2 * (κ * ‖x‖)) := by linarith
        _ = C * ‖x‖ := by rw [hC]; ring
    have h6 : C * ‖x‖ < C * ρ := mul_lt_mul_of_pos_left hx (by linarith)
    have h7 : C * ρ < ε / 2 := by
      rw [hρ, mul_div_assoc', div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  refine ⟨n, Q, Pi, M, hAi', hS0, hSs, hM0, hPi, hPi3, hfix, ?_⟩
  obtain ⟨J, hJm, hJae, hJ⟩ := S.jacobi_local_of_step8 Q (fun y => S.tailProj n (K y))
    (fun y => M y) ((S.tailProj n).comp K).contDiff M.contDiff hS0 hSs
    (fun x => by have := hM0 (Q x); rw [Q.symm_apply_apply] at this; exact this) hcA hcAk hcM
    ρ hρpos hρε
    (fun x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      have h := hbound x hx _ le_rfl
      rw [← hS0 x] at h
      exact h)
    (fun k x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      exact hbound x hx _ ((S.norm_headProj_le k _)))
  have hUb : ball (0 : S.E) ρ ⊆ closedBall 0 ε := fun x hx =>
    ball_subset_closedBall ((ball_subset_ball (by linarith : ρ ≤ ε)) hx)
  have hnA := S.nullPres_of_concl (fun y => S.tailProj n (K y)) hcA
    (ball (0 : S.E) ρ) hUb (fun x hx => by
      rw [mem_ball_zero_iff] at hx
      have h := hbound x hx _ le_rfl
      rw [mem_ball_zero_iff]; exact h)
  have hnAk := fun k => S.nullPres_of_concl (S.projField k fun y => S.tailProj n (K y))
    (hcAk k) (ball (0 : S.E) ρ) hUb (fun x hx => by
      rw [mem_ball_zero_iff] at hx
      have h := hbound x hx _ (S.norm_headProj_le k _)
      rw [mem_ball_zero_iff]; exact h)
  exact ⟨J, hJm, hJae, S.global_of_local ((S.tailProj n).comp K) Q hS0 ρ hρpos J hJm hJae hJ
    hnA hnAk⟩


end NlsGge.Ramer.General.RamerSetting
