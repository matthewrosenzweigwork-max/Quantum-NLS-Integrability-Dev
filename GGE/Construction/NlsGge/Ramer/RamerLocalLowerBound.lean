import NlsGge.Ramer.RamerLocalLowerBoundB

/-!
# R10-P4: Ramer's local lower bound (R10a)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem ramer_local_lower_bound (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (x₀ : FullWeightedHilbert c s)
    (hU : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM)) :
    ∃ V : Set (FullWeightedHilbert c s), IsOpen V ∧ x₀ ∈ V ∧
      (∀ x ∈ V, IsUnit (1 + (hsDerivH c s hs K x).toCLM)) ∧
      (∀ M : Set (FullWeightedHilbert c s),
        ∫⁻ x in V ∩ (fun y => y + inclE c s hs (K y)) ⁻¹' M,
          ENNReal.ofReal (ramerJac c s hs K x) ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
        NlsGge.Measure.fullWeightedSequenceGaussian c s M) ∧
      (∀ N : Set (FullWeightedHilbert c s), NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
        NlsGge.Measure.fullWeightedSequenceGaussian c s
          (V ∩ (fun y => y + inclE c s hs (K y)) ⁻¹' N) = 0) := by
  have hs0 : 0 ≤ s := zero_le_of_half_lt hs
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  obtain ⟨Tt, B, hTt, hTts, hv⟩ := gl_transfer_hsDerivH c s hs K x₀ hU
  obtain ⟨ε, d, hε, e₁, e₂, he₂, hLF, hy0, hK20⟩ :=
    step4_local_fine c s hs K hK x₀ Tt B hTts hv
  set K2' := K2 (inclE c s hs) K B e₁ e₂ with hK2'
  have hε₀ : (0 : ℝ) < ε / 2 := by positivity
  have hlt : ε / 2 < ε := by linarith
  obtain ⟨n₀, hn₀⟩ := ramer_local_pieces hLF hε₀ hlt
  obtain ⟨⟨hSH, hSc, -, hSN4⟩, hrest⟩ := hn₀ n₀ le_rfl
  set y₀ := x₀ + inclE c s hs e₁ with hy₀
  set r : ℝ := (‖y₀‖ + ε / 8) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hyr : ‖y₀‖ < r := by rw [hr]; linarith
  have hr8 : r < ε / 8 := by rw [hr]; linarith
  have hr4 : 4 * r < ε / 2 := by linarith
  obtain ⟨G, hG, hGh, hGPi, -, hii, -, hiii⟩ := hrest r hr0 hr4
  set L := tailField c s n₀ K2' with hLdef
  have hL : ContDiff ℝ 2 L := hSH.smooth
  set i := inclE c s hs with hi
  set Kcl : FullWeightedHilbert c s →L[ℝ] ActualCM c := fderiv ℝ K x₀ with hKcl
  set Â := affineField c s hs Kcl e₂ with hÂdef
  have hÂ : ContDiff ℝ 2 Â := affineField_contDiff hs Kcl e₂
  have hTt' : ∀ x, Tt x = x + inclE c s hs (Kcl x) := hTt
  set T₁ : FullWeightedHilbert c s → FullWeightedHilbert c s := fun x => x + i e₁ with hT₁
  have hT₁c : Continuous T₁ := continuous_id.add_const _
  have hSco : Continuous (TM c s hs L) := (contDiff_TM c s hs L hL).continuous
  have hrb : ball (0 : FullWeightedHilbert c s) r ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2 / 4) :=
    ball_subset_ball (by linarith)
  have hrb2 : ball (0 : FullWeightedHilbert c s) r ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2 / 2) :=
    ball_subset_ball (by linarith)
  have hrcb : ball (0 : FullWeightedHilbert c s) r ⊆ closedBall (0 : FullWeightedHilbert c s) (ε / 2) :=
    (ball_subset_ball (by linarith : r ≤ ε / 2)).trans ball_subset_closedBall
  -- the centre point
  have hLy₀ : L y₀ = 0 := by
    simp [hLdef, tailField, hK20]
  have hSy₀ : TM c s hs L y₀ = y₀ := by
    show y₀ + i (L y₀) = y₀
    rw [hLy₀, map_zero, add_zero]
  have hy₀r : y₀ ∈ ball (0 : FullWeightedHilbert c s) r := by
    rw [mem_ball, dist_zero_right]; exact hyr
  obtain ⟨ru, hru, k₀, hunit⟩ := eventually_uniform_isUnit c s hs K (hK.of_le (by norm_num)) x₀ hU
  set V : Set (FullWeightedHilbert c s) :=
    T₁ ⁻¹' (ball (0 : FullWeightedHilbert c s) r ∩ TM c s hs L ⁻¹' ball (0 : FullWeightedHilbert c s) r)
      ∩ ball x₀ ru with hV
  have hVo : IsOpen V :=
    ((isOpen_ball.inter (isOpen_ball.preimage hSco)).preimage hT₁c).inter isOpen_ball
  have hx₀V : x₀ ∈ V := ⟨⟨hy₀r, by rw [mem_preimage, hSy₀]; exact hy₀r⟩, mem_ball_self hru⟩
  have hVa : ∀ x ∈ V, T₁ x ∈ ball (0 : FullWeightedHilbert c s) r := fun x hx => hx.1.1
  have hVb : ∀ x ∈ V, TM c s hs L (T₁ x) ∈ ball (0 : FullWeightedHilbert c s) r :=
    fun x hx => hx.1.2
  have hVu : ∀ x ∈ V, IsUnit (1 + (hsDerivH c s hs K x).toCLM) := fun x hx => (hunit x hx.2).1
  -- the composite identity
  have hTÂ : ∀ y, TM c s hs Â y = Tt (y + i e₂) := fun y =>
    ((affineHomeo_eq hs Kcl Tt hTt' e₂ y).symm.trans (affineHomeo_apply hs Tt e₂ y))
  have hPhi : ∀ x ∈ V, TM c s hs Â (TM c s hs G (TM c s hs L (T₁ x))) =
      x + i (K x) := by
    intro x hx
    have ha := hVa x hx
    have hb := hVb x hx
    have hacb : T₁ x ∈ closedBall (0 : FullWeightedHilbert c s) (ε / 2) := hrcb ha
    have hbb : TM c s hs L (T₁ x) ∈ ball (0 : FullWeightedHilbert c s) (ε / 2 / 2) := hrb2 hb
    have hSinv : Sinv i L (ε / 2) (TM c s hs L (T₁ x)) = T₁ x :=
      (Sinv_unique hSH.step hacb rfl hbb).symm
    have hGb := hGPi _ hb
    have hPi : TM c s hs G (TM c s hs L (T₁ x)) = T₁ x + i (K2' (T₁ x)) := by
      rw [hGb]
      show Sinv i L (ε / 2) _ + i (K2' (Sinv i L (ε / 2) _)) = _
      rw [hSinv]
    rw [hTÂ, hPi]
    have e1 : T₁ x - i e₁ = x := add_sub_cancel_right x _
    have key : ∀ y : FullWeightedHilbert c s, y - i e₁ = x →
        Tt.symm (x + i (K x)) - i e₂ = y + i (K2' y) := by
      intro y hy
      have h : Tt.symm ((y - i e₁) + i (K (y - i e₁))) - i e₂ = y + i (K2' y) :=
        K2_identity_local i K Tt B hTts e₁ e₂ y
      rw [hy] at h
      exact h
    have hid2 := key (T₁ x) e1
    have e2 : T₁ x + i (K2' (T₁ x)) + i e₂ = Tt.symm (x + i (K x)) := by
      rw [← hid2]; abel
    rw [e2, Tt.apply_symm_apply]
  -- the assembled field equals `K` on `V`
  have hFaC : ContDiff ℝ 2 (fieldFa hs e₁ L G Â) := contDiff_fieldFa hs e₁ hL hG hÂ
  have hFa : EqOn K (fieldFa hs e₁ L G Â) V := by
    intro x hx
    have h1 := TM_fieldFa hs e₁ L G Â x
    have h2 := hPhi x hx
    have h3 : x + i (fieldFa hs e₁ L G Â x) = x + i (K x) := h1.trans h2
    exact (cmToFullWeightedHilbert_injective c s hs0 (add_left_cancel h3)).symm
  -- the Jacobian chain
  have hLn : NullPresOn c s hs L (ball (0 : FullWeightedHilbert c s) r) := (hSN4 _ hrb).1
  have hLnk : ∀ᶠ k in atTop, NullPresOn c s hs (projField k L)
      (ball (0 : FullWeightedHilbert c s) r) := Eventually.of_forall fun k => (hSN4 _ hrb).2 k
  have hchain := chain_ae hs e₁ hL hG hÂ hVo hVa hLn hLnk (hiii _ subset_rfl).1
    (hiii _ subset_rfl).2
  have hJK := ramerJac_ae_eq_of_eqOn c s hs hVo hK hFaC hFa
  -- null-preservation facts
  have nT₁ : NullOn γ T₁ V := fun N hN => translation_null_preserving c s hs e₁ V N hN
  have nS : NullOn γ (TM c s hs L) (ball (0 : FullWeightedHilbert c s) r) :=
    fun N hN => hLn N hN
  have nG : NullOn γ (TM c s hs G) (ball (0 : FullWeightedHilbert c s) r) :=
    fun N hN => (hiii _ subset_rfl).1 N hN
  have nST : NullOn γ (TM c s hs L ∘ T₁) V := nT₁.comp nS hVa
  have nGST : NullOn γ (TM c s hs G ∘ (TM c s hs L ∘ T₁)) V := nST.comp nG hVb
  -- measurable representatives
  have hJLm := aemeasurable_ofReal_ramerJac c s hs L hL
  have hJGm := aemeasurable_ofReal_ramerJac c s hs G hG
  have hJÂm := aemeasurable_ofReal_ramerJac c s hs Â hÂ
  set mL := hJLm.mk with hmL
  set mG := hJGm.mk with hmG
  set mA := hJÂm.mk with hmA
  -- the functional lower-bound chain
  have c1 := fge_translation c s hs e₁ V hVo.measurableSet
  have c2 := (fge_S hs L hL hSc r).congr (ae_restrict_of_ae hJLm.ae_eq_mk)
  have c12 := FGe.comp hSco.measurable c1 c2 hJLm.measurable_mk (W₁ := T₁ '' V)
    (A₂ := closedBall (0 : FullWeightedHilbert c s) (ε / 2) ∩
          TM c s hs L ⁻¹' ball (0 : FullWeightedHilbert c s) (ε / 2 / 2) ∩
        TM c s hs L ⁻¹' ball (0 : FullWeightedHilbert c s) r) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨hrcb (hVa x hx), hrb2 (hVb x hx)⟩, hVb x hx⟩)
  have c3 := ((fge_Pi hs (PiOf hs n₀ K2' (ε / 2)) G r hii).congr_fun measurableSet_ball
    (fun z hz => (hGPi z hz).symm)).congr (ae_restrict_of_ae hJGm.ae_eq_mk)
  have hGm : Measurable (TM c s hs G) := (contDiff_TM c s hs G hG).continuous.measurable
  have c123 := FGe.comp hGm c12 c3 hJGm.measurable_mk inter_subset_right
  have c4 := ((fge_affine c s hs Kcl Tt hTt' e₂).congr_fun MeasurableSet.univ
    (fun z _ => affineHomeo_eq hs Kcl Tt hTt' e₂ z)).congr (ae_restrict_of_ae hJÂm.ae_eq_mk)
  have hÂmeas : Measurable (TM c s hs Â) := (contDiff_TM c s hs Â hÂ).continuous.measurable
  have c1234 := FGe.comp hÂmeas c123 c4 hJÂm.measurable_mk (subset_univ _)
  -- a.e. identification of the total density with `ofReal (ramerJac K)` on `V`
  have eL : ∀ᵐ x ∂γ, x ∈ V → mL (T₁ x) = ENNReal.ofReal (ramerJac c s hs L (T₁ x)) :=
    ae_on_comp (T := T₁) (U := V) nT₁ (P := fun y => mL y = ENNReal.ofReal (ramerJac c s hs L y))
      hJLm.ae_eq_mk.symm
  have eG : ∀ᵐ x ∂γ, x ∈ V → mG ((TM c s hs L ∘ T₁) x) =
      ENNReal.ofReal (ramerJac c s hs G ((TM c s hs L ∘ T₁) x)) :=
    ae_on_comp (T := TM c s hs L ∘ T₁) (U := V) nST
      (P := fun y => mG y = ENNReal.ofReal (ramerJac c s hs G y)) hJGm.ae_eq_mk.symm
  have eA : ∀ᵐ x ∂γ, x ∈ V → mA ((TM c s hs G ∘ (TM c s hs L ∘ T₁)) x) =
      ENNReal.ofReal (ramerJac c s hs Â ((TM c s hs G ∘ (TM c s hs L ∘ T₁)) x)) :=
    ae_on_comp (T := TM c s hs G ∘ (TM c s hs L ∘ T₁)) (U := V) nGST
      (P := fun y => mA y = ENNReal.ofReal (ramerJac c s hs Â y)) hJÂm.ae_eq_mk.symm
  have htot : ∀ᵐ x ∂γ, x ∈ V →
      mA ((TM c s hs G ∘ (TM c s hs L ∘ T₁)) x) *
          (mG ((TM c s hs L ∘ T₁) x) *
            (mL (T₁ x) * ENNReal.ofReal (ramerJac c s hs (fun _ => e₁) x))) =
        ENNReal.ofReal (ramerJac c s hs K x) := by
    filter_upwards [eL, eG, eA, hchain, hJK] with x h1 h2 h3 h4 h5 hxV
    rw [h1 hxV, h2 hxV, h3 hxV, h5 hxV, h4 hxV (hVb x hxV)]
    simp only [Function.comp]
    have n0 := ramerJac_nonneg c s hs
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (n0 _ _) (n0 _ _)) (n0 _ _)),
      ENNReal.ofReal_mul (mul_nonneg (n0 _ _) (n0 _ _)), ENNReal.ofReal_mul (n0 _ _)]
    ring
  -- the inequality for measurable sets
  have hform : ∀ M : Set (FullWeightedHilbert c s), MeasurableSet M →
      ∫⁻ x in V ∩ (fun y => y + i (K y)) ⁻¹' M, ENNReal.ofReal (ramerJac c s hs K x) ∂γ ≤ γ M := by
    intro M hM
    have hKm : Measurable (fun y : FullWeightedHilbert c s => y + i (K y)) :=
      (contDiff_TM c s hs K hK).continuous.measurable
    have e1 : ∫⁻ x in V ∩ (fun y => y + i (K y)) ⁻¹' M, ENNReal.ofReal (ramerJac c s hs K x) ∂γ =
        ∫⁻ x in V, M.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞) (x + i (K x)) *
          ENNReal.ofReal (ramerJac c s hs K x) ∂γ := by
      rw [Set.inter_comm, ← setLIntegral_indicator (hKm hM)]
      refine lintegral_congr fun x => ?_
      by_cases hx : x + i (K x) ∈ M
      · simp [Set.indicator_of_mem (show x ∈ (fun y => y + i (K y)) ⁻¹' M from hx),
          Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem (show x ∉ (fun y => y + i (K y)) ⁻¹' M from hx),
          Set.indicator_of_notMem hx]
    rw [e1]
    have e2 : ∫⁻ x in V, M.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞) (x + i (K x)) *
          ENNReal.ofReal (ramerJac c s hs K x) ∂γ =
        ∫⁻ x in V, M.indicator (1 : FullWeightedHilbert c s → ℝ≥0∞)
            ((TM c s hs Â ∘ (TM c s hs G ∘ (TM c s hs L ∘ T₁))) x) *
          (mA ((TM c s hs G ∘ (TM c s hs L ∘ T₁)) x) *
            (mG ((TM c s hs L ∘ T₁) x) *
              (mL (T₁ x) * ENNReal.ofReal (ramerJac c s hs (fun _ => e₁) x)))) ∂γ := by
      refine setLIntegral_congr_fun_ae hVo.measurableSet ?_
      filter_upwards [htot] with x hx hxV
      rw [hx hxV]
      show _ = M.indicator 1 (TM c s hs Â (TM c s hs G (TM c s hs L (T₁ x)))) * _
      rw [hPhi x hxV]
    rw [e2]
    refine (c1234 _ (measurable_one.indicator hM)).trans ?_
    rw [Measure.restrict_univ, lintegral_indicator_one hM]
  refine ⟨V, hVo, hx₀V, hVu, fun M => ?_, fun N hN => ?_⟩
  · refine le_trans (lintegral_mono_set (inter_subset_inter_right _
      (preimage_mono (subset_toMeasurable γ M)))) ?_
    refine (hform _ (measurableSet_toMeasurable γ M)).trans ?_
    rw [measure_toMeasurable]
  · set N' := toMeasurable γ N with hN'
    have hN'0 : γ N' = 0 := by rw [hN', measure_toMeasurable]; exact hN
    have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
    have hSm : MeasurableSet (V ∩ (fun y => y + i (K y)) ⁻¹' N') :=
      hVo.measurableSet.inter ((contDiff_TM c s hs K hK).continuous.measurable hN'm)
    have h0 := hform N' hN'm
    rw [hN'0, nonpos_iff_eq_zero] at h0
    have hae : ∀ᵐ x ∂γ.restrict (V ∩ (fun y => y + i (K y)) ⁻¹' N'),
        ENNReal.ofReal (ramerJac c s hs K x) = 0 :=
      (lintegral_eq_zero_iff' ((aemeasurable_ofReal_ramerJac c s hs K hK).restrict)).1 h0
    rw [ae_restrict_iff' hSm] at hae
    refine measure_mono_null (inter_subset_inter_right _ (preimage_mono (subset_toMeasurable γ N)))
      ?_
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx hxS
    have := hx hxS
    rw [ENNReal.ofReal_eq_zero] at this
    exact absurd this (not_le.2 (ramerJac_pos_of_isUnit c s hs K x (hVu x hxS.1)))

#check @ramer_local_lower_bound
#print axioms ramer_local_lower_bound

end NlsGge.Ramer
