import NlsGge.Ramer.LinearSmallJacobiLocal
import NlsGge.Ramer.CameronMartinE
import NlsGge.Ramer.LocalJacobiExtension
import NlsGge.Ramer.RamerLemma54Eventually
import NlsGge.Ramer.RamerStep1Locality

/-!
# D2, steps 3–4: the global Jacobi formula for the linear small `S`

From the local formula near `0` (D2 step 2), Cameron–Martin translations (CM-E) and Ramer's Lemma 5.4
(R9c′), we obtain `(*)` near every point and globalize with R1.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ} {c : BoundedCoefficients lower upper} {s : ℝ}

/-- **Global form from the local one**, for a linear field `L` and `S = I + iL`. -/
theorem global_of_local (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (S : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hS : ∀ x, S x = x + inclE c s hs (L x)) (ρ : ℝ) (hρ : 0 < ρ)
    (J : FullWeightedHilbert c s → ℝ≥0∞) (hJ : Measurable J)
    (hJae : J =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
      fun x => ENNReal.ofReal (ramerJac c s hs (fun y => L y) x))
    (hloc : LocalJacobiUC (NlsGge.Measure.fullWeightedSequenceGaussian c s)
      (S.toHomeomorph : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s) J
      (ball (0 : FullWeightedHilbert c s) ρ))
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (ball (0 : FullWeightedHilbert c s) ρ ∩ TM c s hs (fun y => L y) ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (ball (0 : FullWeightedHilbert c s) ρ ∩
          TM c s hs (projField k (fun y => L y)) ⁻¹' N) = 0) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map S.symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity J := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  have : IsFiniteMeasure γ := by rw [hγ]; infer_instance
  have hLd : ContDiff ℝ 2 (fun y => L y) := L.contDiff
  refine map_symm_eq_withDensity_of_local γ S.toHomeomorph J hJ ?_
  intro x₀
  have hdense : DenseRange (inclE c s hs) :=
    cmToFullWeightedHilbert_denseRange c s (zero_le_of_half_lt hs)
  obtain ⟨e, he⟩ : ∃ e : ActualCM c, dist x₀ (inclE c s hs e) < ρ := by
    have := hdense x₀
    rw [Metric.mem_closure_iff] at this
    obtain ⟨_, ⟨e, rfl⟩, h⟩ := this ρ hρ
    exact ⟨e, h⟩
  set V₀ : Set (FullWeightedHilbert c s) := ball 0 ρ with hV₀
  set V : Set (FullWeightedHilbert c s) := (fun x => x + inclE c s hs e) '' V₀ with hV
  have hV₀o : IsOpen V₀ := isOpen_ball
  have hVo : IsOpen V := (Homeomorph.addRight (inclE c s hs e)).isOpenMap _ hV₀o
  have hVm : MeasurableSet V := hVo.measurableSet
  have hx₀ : x₀ ∈ V := ⟨x₀ - inclE c s hs e, by
    rw [hV₀, mem_ball_zero_iff, ← dist_eq_norm]; exact he, sub_add_cancel _ _⟩
  refine ⟨V, hVo, hx₀, ?_⟩
  set d : ActualCM c := -e with hd
  set e' : ActualCM c := e + L (inclE c s hs e) with he'
  have hSe : ∀ x, S (x + inclE c s hs e) = S x + inclE c s hs e' := by
    intro x
    rw [map_add, hS (inclE c s hs e), he', map_add]
  have hSd : ∀ x, S (x + inclE c s hs d) + inclE c s hs e' = S x := by
    intro x
    have := hSe (x + inclE c s hs d)
    rw [add_assoc, ← map_add, hd, neg_add_cancel, map_zero, add_zero] at this
    rw [← this]
  have hVd : (fun x => x + inclE c s hs d) '' V = V₀ := by
    rw [hV, Set.image_image]
    ext y; simp [hd]
  have hSV : S.toHomeomorph '' V = (fun y => y + inclE c s hs e') '' (S.toHomeomorph '' V₀) := by
    rw [hV, Set.image_image, Set.image_image]
    exact Set.image_congr (fun x _ => hSe x)
  have hSV₀m : MeasurableSet (S.toHomeomorph '' V₀) :=
    (S.toHomeomorph.isOpenMap V₀ hV₀o).measurableSet
  -- measurable representative of the Cameron–Martin density for `e'`
  have hmc := aemeasurable_constDensity c s hs e'
  set Jc' := hmc.mk with hJc'def
  have hJc'm : Measurable Jc' := hmc.measurable_mk
  have hJc'ae : Jc' =ᵐ[γ] fun x => ENNReal.ofReal (ramerJac c s hs (fun _ => e') x) :=
    hmc.ae_eq_mk.symm
  -- the field of `M = S ∘ τ_{-ie}`
  set KM : FullWeightedHilbert c s → ActualCM c :=
    (fun _ => d) + (fun y => L y) ∘ TM c s hs (fun _ => d) with hKM
  have hKMd : ContDiff ℝ 2 KM :=
    contDiff_const.add (hLd.comp (contDiff_TM c s hs _ contDiff_const))
  have hTMd : ∀ x, TM c s hs (fun _ => d) x = x + inclE c s hs d := fun x => rfl
  have hTMKM : ∀ x, TM c s hs KM x = TM c s hs (fun y => L y) (x + inclE c s hs d) := by
    intro x
    simp only [TM, hKM, Pi.add_apply, Function.comp_apply, map_add]
    abel
  have hTMS : ∀ x, TM c s hs (fun y => L y) x = S x := fun x => (hS x).symm
  -- null preservation of the inner maps on `V`
  have hT' : ∀ N : Set (FullWeightedHilbert c s), γ N = 0 → γ (V ∩ TM c s hs KM ⁻¹' N) = 0 := by
    intro N hN
    refine measure_mono_null ?_
      ((quasiMeasurePreserving_add_inclE c s hs d).preimage_null (hT N hN))
    rintro x ⟨hxV, hxN⟩
    refine ⟨?_, ?_⟩
    · rw [← hVd]; exact ⟨x, hxV, rfl⟩
    · show TM c s hs (fun y => L y) (x + inclE c s hs d) ∈ N
      rw [← hTMKM]; exact hxN
  have hTk' : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s), γ N = 0 →
      γ (V ∩ TM c s hs (projField k KM) ⁻¹' N) = 0 := by
    intro k N hN
    have hN'' : γ ((fun y => y + inclE c s hs (headProj c k d - d)) ⁻¹' N) = 0 :=
      (quasiMeasurePreserving_add_inclE c s hs (headProj c k d - d)).preimage_null hN
    refine measure_mono_null ?_
      ((quasiMeasurePreserving_add_inclE c s hs d).preimage_null (hTk k _ hN''))
    rintro x ⟨hxV, hxN⟩
    refine ⟨?_, ?_⟩
    · rw [← hVd]; exact ⟨x, hxV, rfl⟩
    · show TM c s hs (projField k fun y => L y) (x + inclE c s hs d) +
        inclE c s hs (headProj c k d - d) ∈ N
      have : TM c s hs (projField k fun y => L y) (x + inclE c s hs d) +
          inclE c s hs (headProj c k d - d) = TM c s hs (projField k KM) x := by
        simp only [TM, hKM, projField, Pi.add_apply, Function.comp_apply, map_add, map_sub]
        abel
      rw [this]; exact hxN
  -- (4a) and (4b)
  have h4a : ∀ᵐ x ∂γ, ramerJac c s hs KM x =
      ramerJac c s hs (fun y => L y) (x + inclE c s hs d) *
        ramerJac c s hs (fun _ => d) x := by
    filter_upwards [ramer_lemma_5_4_eventually c s hs univ isOpen_univ (fun _ => d)
      (fun y => L y) contDiff_const hLd (hT_TM_const c s hs d univ)
      (hTk_TM_const_eventually c s hs d univ)] with x hx
    exact hx (mem_univ x)
  have hfun : KM + (fun _ => e') ∘ TM c s hs KM = fun y => L y := by
    funext x
    simp only [hKM, TM, Pi.add_apply, Function.comp_apply, map_add, map_neg, hd, he']
    abel
  have h4b : ∀ᵐ x ∂γ, x ∈ V → ramerJac c s hs (fun y => L y) x =
      ramerJac c s hs (fun _ => e') (S (x + inclE c s hs d)) * ramerJac c s hs KM x := by
    filter_upwards [ramer_lemma_5_4_eventually c s hs V hVo KM (fun _ => e') hKMd contDiff_const
      hT' (Filter.Eventually.of_forall hTk')] with x hx hxV
    have := hx hxV
    rw [hfun, hTMKM, hTMS] at this
    exact this
  have hc : ∀ᵐ x ∂γ, J (x + inclE c s hs d) =
      ENNReal.ofReal (ramerJac c s hs (fun y => L y) (x + inclE c s hs d)) :=
    (quasiMeasurePreserving_add_inclE c s hs d).ae hJae
  have hdd : ∀ᵐ x ∂γ, x ∈ V → Jc' (S (x + inclE c s hs d)) =
      ENNReal.ofReal (ramerJac c s hs (fun _ => e') (S (x + inclE c s hs d))) := by
    have h0 : γ {y | ¬ Jc' y = ENNReal.ofReal (ramerJac c s hs (fun _ => e') y)} = 0 :=
      ae_iff.1 hJc'ae
    have h1 := hT' _ h0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx hxV
    by_contra hne
    exact hx ⟨hxV, by
      show ¬ _ = _
      rw [hTMKM, hTMS]; exact hne⟩
  have hkey : ∀ᵐ x ∂γ, x ∈ V →
      Jc' (S (x + inclE c s hs d)) * J (x + inclE c s hs d) *
        ENNReal.ofReal (ramerJac c s hs (fun _ => d) x) = J x := by
    filter_upwards [h4a, h4b, hc, hdd, hJae] with x a b c' d' j hxV
    rw [d' hxV, c', j, b hxV, a, ENNReal.ofReal_mul (ramerJac_nonneg c s hs _ _),
      ENNReal.ofReal_mul (ramerJac_nonneg c s hs _ _), mul_assoc]
  -- the main chain
  have claim : ∀ G : FullWeightedHilbert c s → ℝ≥0∞, Measurable G →
      ∫⁻ y in S.toHomeomorph '' V, G y ∂γ = ∫⁻ x in V, G (S.toHomeomorph x) * J x ∂γ := by
    intro G hG
    have hA := lintegral_image_add_inclE c s hs e' G hG _ hSV₀m
    have hA' : ∫⁻ y in S.toHomeomorph '' V₀, G (y + inclE c s hs e') *
        ENNReal.ofReal (ramerJac c s hs (fun _ => e') y) ∂γ =
        ∫⁻ y in S.toHomeomorph '' V₀, G (y + inclE c s hs e') * Jc' y ∂γ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hJc'ae] with y hy
      rw [hy]
    have hHm : Measurable (fun y => G (y + inclE c s hs e') * Jc' y) :=
      (hG.comp (measurable_id.add_const _)).mul hJc'm
    have hB := lintegral_image_eq_of_local_ext γ S.toHomeomorph J hJ V₀ hV₀o hloc _ hHm
    have hH2m : Measurable (fun x => G (S x + inclE c s hs e') * Jc' (S x) * J x) :=
      ((hG.comp (S.continuous.measurable.add_const _)).mul
        (hJc'm.comp S.continuous.measurable)).mul hJ
    have hC := lintegral_image_add_inclE c s hs d _ hH2m V hVm
    rw [hVd] at hC
    rw [hSV, hA, hA', hB]
    refine (lintegral_congr fun x => rfl : _ = ∫⁻ x in V₀,
      G (S x + inclE c s hs e') * Jc' (S x) * J x ∂γ).trans (hC.trans ?_)
    refine lintegral_congr_ae ((ae_restrict_iff' hVm).2 ?_)
    filter_upwards [hkey] with x hx hxV
    have := hx hxV
    show G (S (x + inclE c s hs d) + inclE c s hs e') * Jc' (S (x + inclE c s hs d)) *
      J (x + inclE c s hs d) * ENNReal.ofReal (ramerJac c s hs (fun _ => d) x) =
      G (S x) * J x
    rw [hSd x, ← this]
    ring
  intro F hF1 hF2 hF3 hF4
  have hFm : Measurable F := hF1.continuous.measurable
  exact claim _ (ENNReal.measurable_ofReal.comp hFm)

variable (c s) in
/-- **D2 steps 3–4: the global Jacobi formula for the linear small `S`.** -/
theorem linearSmall_map_symm (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hT : ∀ x, T x = x + inclE c s hs (K x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (S Pi : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
      (M : FullWeightedHilbert c s →L[ℝ] ActualCM c),
      (∀ h : ActualCM c, ‖tailProj c n (K (inclE c s hs h))‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S x = x + inclE c s hs (tailProj c n (K x))) ∧
      (∀ x, S.symm x = x + inclE c s hs (M x)) ∧
      (∀ x, M x = -(tailProj c n (K (S.symm x)))) ∧
      (∀ x, Pi x = T (S.symm x)) ∧
      (∀ x, Pi x - x = inclE c s hs (headProj c n (K (S.symm x)))) ∧
      (∀ x, SameTail c s n (Pi x) x) ∧
      ∃ J : FullWeightedHilbert c s → ℝ≥0∞, Measurable J ∧
        (J =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
          fun x => ENNReal.ofReal (ramerJac c s hs (fun y => tailProj c n (K y)) x)) ∧
        (NlsGge.Measure.fullWeightedSequenceGaussian c s).map S.symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity J := by
  have hs0 : 0 ≤ s := zero_le_of_half_lt hs
  obtain ⟨κ0, hκ0, hK0⟩ := K.bound
  set κ := max κ0 0 with hκdef
  have hκ : 0 ≤ κ := le_max_right _ _
  have hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖ := fun y =>
    (hK0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ (ActualCM c)
  have hi := cmToFullWeightedHilbert_hs c s hs b
  obtain ⟨n₀, hn₀⟩ := exists_tail_small c s (by linarith : 0 < s) (3 * κ * ε + 1) (ε / 2)
    (by linarith)
  obtain ⟨n, S, Pi, M, hnn, hAi, hS, hSs, hM, hMi, hPi, hPi2⟩ :=
    linear_decomposition_ge (inclE c s hs) b hi K T hT (headProj c)
      (fun n x => norm_cmTrunc_le c n x) (headProj_tendsto c)
      (tailProj c) (tailProj_apply c) n₀
  have hn' : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < 3 * κ * ε + 1 →
      ‖cmToFullWeightedHilbert c s hs0 h - cmToFullWeightedHilbert c s hs0
        ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2 :=
    fun m hm h hh => hn₀ m (le_trans hnn hm) h hh
  have hfix : ∀ x, SameTail c s n (Pi x) x := by
    intro x m hm
    have e : coordE c s (Pi x - x) m = 0 := by
      rw [hPi2 x]; exact coordE_incl_headProj c s hs0 n (K (S.symm x)) m hm
    rw [coordE_sub] at e
    exact sub_eq_zero.1 e
  obtain ⟨-, hcA⟩ := linearSmall_step8_S c s hs K κ hκ hK n hAi ε hε hn'
  obtain ⟨-, hcM⟩ := linearSmall_step8_Sinv c s hs K S M κ hκ hK n hAi hSs hM hMi ε hε hn'
  have hcAk := fun k => linearSmall_step8_proj hs K κ hκ hK n hAi ε hε hn' k
  -- the radius
  obtain ⟨a0, -, ha0⟩ := (inclE c s hs).bound
  set a : ℝ := max a0 0 with ha
  have ha1 : 0 ≤ a := le_max_right _ _
  have ha2 : ∀ w, ‖inclE c s hs w‖ ≤ a * ‖w‖ := fun w =>
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
  have hbound : ∀ x : FullWeightedHilbert c s, ‖x‖ < ρ → ∀ w : ActualCM c,
      ‖w‖ ≤ ‖tailProj c n (K x)‖ → ‖x + inclE c s hs w‖ < ε / 2 := by
    intro x hx w hw
    have h1 : ‖tailProj c n (K x)‖ ≤ 2 * (κ * ‖x‖) :=
      (norm_tailProj_le c n _).trans (by linarith [hK x])
    have h2 : ‖inclE c s hs w‖ ≤ a * ‖w‖ := ha2 w
    have h4 : a * ‖w‖ ≤ a * (2 * (κ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hw.trans h1) ha1
    have h5 : ‖x + inclE c s hs w‖ ≤ C * ‖x‖ := by
      calc _ ≤ ‖x‖ + ‖inclE c s hs w‖ := norm_add_le _ _
        _ ≤ ‖x‖ + a * (2 * (κ * ‖x‖)) := by linarith
        _ = C * ‖x‖ := by rw [hC]; ring
    have h6 : C * ‖x‖ < C * ρ := mul_lt_mul_of_pos_left hx (by linarith)
    have h7 : C * ρ < ε / 2 := by
      rw [hρ, mul_div_assoc', div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  have hS' : ∀ x, S x = x + inclE c s hs (tailProj c n (K x)) := hS
  refine ⟨n, S, Pi, M, hAi, hS, hSs, hM, hPi, hPi2, hfix, ?_⟩
  obtain ⟨J, hJm, hJae, hJ⟩ := jacobi_local_of_step8 hs S (fun y => tailProj c n (K y))
    (fun y => M y) ((tailProj c n).comp K).contDiff M.contDiff hS' hSs
    (fun x => by have := hM (S x); rw [S.symm_apply_apply] at this; exact this) hcA hcAk hcM ρ hρpos hρε
    (fun x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      have h := hbound x hx _ le_rfl
      rw [← hS' x] at h
      exact h)
    (fun k x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      exact hbound x hx _ ((norm_headProj_le c k _)))
  have hUb : ball (0 : FullWeightedHilbert c s) ρ ⊆ closedBall 0 ε := fun x hx =>
    ball_subset_closedBall ((ball_subset_ball (by linarith : ρ ≤ ε)) hx)
  have hnA := nullPres_of_concl c s hs (fun y => tailProj c n (K y)) hcA
    (ball (0 : FullWeightedHilbert c s) ρ) hUb (fun x hx => by
      rw [mem_ball_zero_iff] at hx
      have h := hbound x hx _ le_rfl
      rw [mem_ball_zero_iff]; exact h)
  have hnAk := fun k => nullPres_of_concl c s hs (projField k fun y => tailProj c n (K y))
    (hcAk k) (ball (0 : FullWeightedHilbert c s) ρ) hUb (fun x hx => by
      rw [mem_ball_zero_iff] at hx
      have h := hbound x hx _ (norm_headProj_le c k _)
      rw [mem_ball_zero_iff]; exact h)
  exact ⟨J, hJm, hJae, global_of_local hs ((tailProj c n).comp K) S hS' ρ hρpos J hJm hJae hJ hnA hnAk⟩

#check @global_of_local
#check @linearSmall_map_symm
#print axioms global_of_local
#print axioms linearSmall_map_symm

end NlsGge.Ramer
