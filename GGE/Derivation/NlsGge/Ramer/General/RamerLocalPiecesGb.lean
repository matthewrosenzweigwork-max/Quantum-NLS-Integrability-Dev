import Mathlib
import NlsGge.Ramer.General.RamerLocalPiecesGa

/-!
# R10-P3, part b: the head-valued field `G_Π` and the main local-pieces theorem (GE7b)

Adapted from the second half of `NlsGge/Ramer/RamerLocalPieces.lean` (section `GPi`), over a
`RamerSetting S`.  Dictionary as in `RamerLocalPiecesGa`; moreover `hsDerivH c s hs ↦ S.hsDerivH`,
`ramerJac c s hs ↦ S.ramerJac`, `Sn c s hs n ↦ S.Sn n`, `projField ↦ S.projField`.

Anisotropy check: no norm of `E` other than the triangle inequality, the `1/8` contraction
bound `‖DK(y) ∘ i‖ ≤ 1/8` (stated for `i = S.incl`) and the `Step8Hyp` data of part a is used, so
all constants are unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- `Π' = PiMap` for the tail field of `K` (radius `ε₀`). (Old: `PiOf`.) -/
abbrev PiOf (n : ℕ) (K : S.E → S.H) (ε₀ : ℝ) : S.E → S.E :=
  PiMap S.incl (S.tailField n K) K ε₀

variable {S} {K : S.E → S.H} {ε d ε₀ : ℝ}

/-- **`G_Π`**: a globally `C²`, `V_n`-valued field with `I + i G_Π = Π'` on `ball 0 r`, and
`I + D_H G_Π(z)` invertible there. (Old: `exists_headField`.) -/
theorem exists_headField (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : S.TailSmall d ε₀ n) {r : ℝ} (hr : 0 < r) (hr4 : 4 * r < ε₀) :
    ∃ G : S.E → S.H, ContDiff ℝ 2 G ∧
      (∀ z, S.headProj n (G z) = G z) ∧
      (∀ z ∈ ball (0 : S.E) r, S.TM G z = S.PiOf n K ε₀ z) ∧
      (∀ z ∈ ball (0 : S.E) r,
        IsUnit (1 + (S.hsDerivH G z).toCLM)) := by
  have h8 := S.step8Hyp_tailField hK hε₀ hlt n hn
  have hy := h8.step
  set Sv := Sinv S.incl (S.tailField n K) ε₀ with hSv
  obtain ⟨ρ, hρd, -, -, hρin, hρout, -⟩ := exists_bump_generic (0 : S.E) hr
  set G : S.E → S.H := fun z => ρ z • S.headProj n (K (Sv z)) with hG
  have hr2 : ∀ z : S.E, z ∈ ball (0 : S.E) r →
      z ∈ ball (0 : S.E) (ε₀ / 2) := fun z hz =>
    ball_subset_ball (by linarith) hz
  have hGsmooth : ContDiff ℝ 2 G := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ ball (0 : S.E) (ε₀ / 2)
    · have hS := (sinv_local S.incl (S.tailField n K) ε₀ h8.smooth hy hz).1
      exact hρd.contDiffAt.smul ((S.headProj n).contDiff.contDiffAt.comp z
        (hK.smooth.contDiffAt.comp z hS))
    · have hz' : 2 * r < ‖z‖ := by
        rw [mem_ball, dist_zero_right, not_lt] at hz; linarith
      have hev : ∀ᶠ y in 𝓝 z, 2 * r < ‖y‖ :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hz'
      refine (contDiffAt_const (c := (0 : S.H))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy'
      have : y ∉ ball (0 : S.E) (2 * r) := by
        rw [mem_ball, dist_zero_right, not_lt]; exact hy'.le
      simp [hG, hρout y this]
  refine ⟨G, hGsmooth, fun z => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · simp only [hG, map_smul, S.headProj_idem]
  · have hz2 := hr2 z hz
    have h1 := PiMap_sub (K := K) (R := S.headProj n) (i := S.incl) (ε := ε₀) hy hz2
    show z + S.incl (G z) = _
    have e : G z = S.headProj n (K (Sv z)) := by simp [hG, hρin z hz]
    rw [e]
    show _ = PiMap S.incl (fun y => K y - S.headProj n (K y)) K ε₀ z
    exact add_eq_of_eq_sub' h1.symm
  · have hz2 := hr2 z hz
    obtain ⟨-, D, hD, Q, hQ1, hQ2, hDQ⟩ :=
      sinv_local S.incl (S.tailField n K) ε₀ h8.smooth hy hz2
    have hx := Sinv_spec hy hz2
    have hxlt : ‖Sv z‖ < ε := by
      have := hx.1
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    have hKx := hK.diff (Sv z)
    have hG0 : HasFDerivAt G ((S.headProj n).comp ((fderiv ℝ K (Sv z)).comp D)) z := by
      have hev : G =ᶠ[𝓝 z] fun y => S.headProj n (K (Sv y)) := by
        filter_upwards [isOpen_ball.mem_nhds hz] with y hy'
        simp [hG, hρin y hy']
      exact ((S.headProj n).hasFDerivAt.comp z (hKx.hasFDerivAt.comp z hD)).congr_of_eventuallyEq hev
    have hA : ∀ h : S.H, ‖fderiv ℝ K (Sv z) (S.incl h)‖ ≤ 1 / 2 * ‖h‖ := fun h => by
      have := hK.contr _ hxlt h
      nlinarith [norm_nonneg h]
    have hU := isUnit_G S.incl (S.headProj n) K (S.tailField n K) (fun y => rfl)
      (Sv z) hKx D Q hA hQ1 hQ2 hDQ
    convert hU using 2
    ext h
    have := congrArg (fun f => f h) (S.hsDerivH_toCLM G z)
    refine this.trans ?_
    exact fderiv_apply_eq_of_hasFDerivAt hG0 _

/-- Injectivity of `Π'` on `ball 0 (ε₀/2)`: R6 for `T'` and R7b. (Old: `injOn_PiOf`.) -/
theorem injOn_PiOf (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : S.TailSmall d ε₀ n) :
    InjOn (S.PiOf n K ε₀) (ball (0 : S.E) (ε₀ / 2)) :=
  injOn_PiMap (S.step8Hyp_tailField hK hε₀ hlt n hn).step
    (injOn_T'_local_generic S.incl K hlt (fun y _ => hK.diff y) hK.contr)

/-- **(ii)** the change-of-variables identity for `Π'` on `ball 0 r`, with density
`ramerJac G` (`G` head-valued `C²` with `TM G = Π'` there), and measurability of the image.
(Old: `localPieces_ii`.) -/
theorem localPieces_ii (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : S.TailSmall d ε₀ n) {r : ℝ} (hr4 : 4 * r < ε₀) (hr : 0 < r)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G)
    (hGh : ∀ z, S.headProj n (G z) = G z)
    (hGPi : ∀ z ∈ ball (0 : S.E) r, S.TM G z = S.PiOf n K ε₀ z) :
    MeasurableSet (S.PiOf n K ε₀ '' ball (0 : S.E) r) ∧
    ∀ f : S.E → ℝ≥0∞, Measurable f →
      ∫⁻ y in S.PiOf n K ε₀ '' ball (0 : S.E) r, f y ∂S.γE =
        ∫⁻ x in ball (0 : S.E) r, f (S.PiOf n K ε₀ x) *
          ENNReal.ofReal (S.ramerJac G x) ∂S.γE := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hGd : Differentiable ℝ G := hG1.differentiable one_ne_zero
  have hSnTM : S.Sn n G = S.TM G := S.Sn_eq_TM G hGh
  have hSc : Continuous (S.Sn n G) := S.continuous_Sn n G hG1.continuous
  set A : Set S.E := ball (0 : S.E) r with hA
  have hAZ : A ⊆ ball (0 : S.E) (ε₀ / 2) :=
    ball_subset_ball (by linarith)
  have hSP : ∀ z ∈ A, S.Sn n G z = S.PiOf n K ε₀ z := fun z hz => by
    rw [hSnTM]; exact hGPi z hz
  have hinj : InjOn (S.Sn n G) A := fun a ha b hb hab => by
    rw [hSP a ha, hSP b hb] at hab
    exact S.injOn_PiOf hK hε₀ hlt n hn (hAZ ha) (hAZ hb) hab
  have himg : S.Sn n G '' A = S.PiOf n K ε₀ '' A := image_congr hSP
  have hmeas : MeasurableSet (S.Sn n G '' A) :=
    measurableSet_ball.image_of_continuousOn_injOn hSc.continuousOn hinj
  rw [← himg]
  refine ⟨hmeas, fun f hf => ?_⟩
  have h := S.lintegral_image_eq_fibre n (S.Sn n G) hSc.measurable
    (S.sameTail_Sn n G) (S.measurable_fibreJ_Sn n G hG1) A measurableSet_ball hmeas hinj
    (fun t v _ _ => S.differentiable_fibreMapOf_Sn n G hGd t v) f hf
  rw [h]
  have hae := S.ramerJac_ae_eq_fibreJ G hG hGh
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [hae] with x hx hxA
  rw [hx, hSnTM, hGPi x hxA]

/-- `projField k G = G` for a `V_n`-valued `G` and `k ≥ n`. (Old: `projField_eq_of_headValued`.) -/
theorem projField_eq_of_headValued {n k : ℕ} (hkn : n ≤ k)
    (G : S.E → S.H) (hGh : ∀ z, S.headProj n (G z) = G z) :
    S.projField k G = G := by
  funext z
  show S.headProj k (G z) = G z
  rw [← hGh z, S.headProj_headProj_of_le hkn, hGh z]

/-- **(iii)** null preservation of `TM G = Π'` on every `U ⊆ ball 0 r`, from (ii) and
positivity of `ramerJac G`. (Old: `localPieces_iii`.) -/
theorem localPieces_iii (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) (n : ℕ)
    (hn : S.TailSmall d ε₀ n) {r : ℝ} (hr4 : 4 * r < ε₀) (hr : 0 < r)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G)
    (hGh : ∀ z, S.headProj n (G z) = G z)
    (hGPi : ∀ z ∈ ball (0 : S.E) r, S.TM G z = S.PiOf n K ε₀ z)
    (hGU : ∀ z ∈ ball (0 : S.E) r,
        IsUnit (1 + (S.hsDerivH G z).toCLM)) :
    (∀ z ∈ ball (0 : S.E) r, 0 < S.ramerJac G z) ∧
    ∀ U : Set S.E, U ⊆ ball (0 : S.E) r →
      S.NullPresOn G U ∧ ∀ᶠ k in atTop, S.NullPresOn (S.projField k G) U := by
  refine ⟨fun z hz => S.ramerJac_pos_of_isUnit G z (hGU z hz), fun U hU => ?_⟩
  have hT : S.NullPresOn G U := by
    intro N hN
    obtain ⟨-, hii⟩ := S.localPieces_ii hK hε₀ hlt n hn hr4 hr G hG hGh hGPi
    set γ := S.γE with hγ
    set N' := toMeasurable γ N with hN'
    have hN'0 : γ N' = 0 := by rw [hN', measure_toMeasurable]; exact hN
    have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
    have h0 := hii (N'.indicator 1) (measurable_one.indicator hN'm)
    have hL : ∫⁻ y in S.PiOf n K ε₀ '' ball (0 : S.E) r,
        N'.indicator 1 y ∂γ = 0 := by
      refine le_antisymm ?_ zero_le
      calc _ ≤ ∫⁻ y, N'.indicator 1 y ∂γ := setLIntegral_le_lintegral _ _
        _ = γ N' := lintegral_indicator_one hN'm
        _ = 0 := hN'0
    rw [hL] at h0
    have hGc : Continuous (S.TM G) := (S.contDiff_TM G hG).continuous
    have hmeas : AEMeasurable (fun x => N'.indicator (1 : S.E → ℝ≥0∞)
        (S.PiOf n K ε₀ x) * ENNReal.ofReal (S.ramerJac G x))
        (γ.restrict (ball (0 : S.E) r)) := by
      have e : ∀ x ∈ ball (0 : S.E) r,
          N'.indicator (1 : S.E → ℝ≥0∞) (S.PiOf n K ε₀ x) =
          N'.indicator (1 : S.E → ℝ≥0∞) (S.TM G x) := fun x hx => by
        rw [hGPi x hx]
      refine AEMeasurable.congr (f := fun x => N'.indicator (1 : S.E → ℝ≥0∞)
        (S.TM G x) * ENNReal.ofReal (S.ramerJac G x)) ?_ ?_
      · exact (((measurable_one.indicator hN'm).comp hGc.measurable).aemeasurable.mul
          (S.aemeasurable_ofReal_ramerJac G hG)).restrict
      · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
        exact Filter.Eventually.of_forall fun x hx => by rw [e x hx]
    have hz0 := (lintegral_eq_zero_iff' hmeas).1 h0.symm
    have hz : ∀ᵐ x ∂γ.restrict (ball (0 : S.E) r),
        N'.indicator (1 : S.E → ℝ≥0∞) (S.PiOf n K ε₀ x) *
          ENNReal.ofReal (S.ramerJac G x) = 0 := hz0
    rw [ae_restrict_iff' measurableSet_ball] at hz
    rw [measure_eq_zero_iff_ae_notMem]
    have hpos := fun z hz => S.ramerJac_pos_of_isUnit G z (hGU z hz)
    filter_upwards [hz] with x hx hxS
    have hxr := hU hxS.1
    have h1 := hx hxr
    rw [mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have hmem : S.PiOf n K ε₀ x ∈ N' := by
        rw [← hGPi x hxr]; exact subset_toMeasurable _ _ hxS.2
      simp [Set.indicator_of_mem hmem] at h1
    · have := ENNReal.ofReal_pos.2 (hpos x hxr)
      exact absurd h1 this.ne'
  refine ⟨hT, ?_⟩
  filter_upwards [eventually_ge_atTop n] with k hk
  rw [projField_eq_of_headValued hk G hGh]
  exact hT

/-- **R10-P3 (main).**  For `K` as in Step 4 (`LocalField`) and `ε₀ < ε`, there is `n₀` such that
for every `n ≥ n₀`, with `L = (I - P_n) K`, `S = I + iL`, `Π' = PiMap`:
(i) `L` is in class N2; and for every `r` with `4 r < ε₀` there is a globally `C²`, `V_n`-valued
`G_Π` with `I + i G_Π = Π'` on `ball 0 r`, such that
(ii) `Π'(ball 0 r)` is measurable and the change-of-variables identity holds with density
`ramerJac G_Π`; (iii) `ramerJac G_Π > 0` on `ball 0 r`, and `TM G_Π` and all `TM (P_k G_Π)`,
`k ≥ n`, preserve null sets on every `U ⊆ ball 0 r`. (Old: `ramer_local_pieces`.) -/
theorem ramer_local_pieces (hK : S.LocalField K ε d) (hε₀ : 0 < ε₀) (hlt : ε₀ < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (S.Step8Hyp (S.tailField n K) ε₀ ∧ S.Step8Concl (S.tailField n K) ε₀ ∧
        (∀ U : Set S.E,
          U ⊆ closedBall (0 : S.E) ε₀ ∩
            S.TM (S.tailField n K) ⁻¹' ball (0 : S.E) (ε₀ / 2) →
          S.NullPresOn (S.tailField n K) U) ∧
        (∀ U : Set S.E, U ⊆ ball (0 : S.E) (ε₀ / 4) →
          S.NullPresOn (S.tailField n K) U ∧
          ∀ k : ℕ, S.NullPresOn (S.projField k (S.tailField n K)) U)) ∧
      ∀ r : ℝ, 0 < r → 4 * r < ε₀ →
        ∃ G : S.E → S.H, ContDiff ℝ 2 G ∧
          (∀ z, S.headProj n (G z) = G z) ∧
          (∀ z ∈ ball (0 : S.E) r, S.TM G z = S.PiOf n K ε₀ z) ∧
          MeasurableSet (S.PiOf n K ε₀ '' ball (0 : S.E) r) ∧
          (∀ f : S.E → ℝ≥0∞, Measurable f →
            ∫⁻ y in S.PiOf n K ε₀ '' ball (0 : S.E) r, f y ∂S.γE =
              ∫⁻ x in ball (0 : S.E) r, f (S.PiOf n K ε₀ x) *
                ENNReal.ofReal (S.ramerJac G x) ∂S.γE) ∧
          (∀ z ∈ ball (0 : S.E) r, 0 < S.ramerJac G z) ∧
          (∀ U : Set S.E, U ⊆ ball (0 : S.E) r →
            S.NullPresOn G U ∧ ∀ᶠ k in atTop, S.NullPresOn (S.projField k G) U) := by
  obtain ⟨n₀, hn₀⟩ := S.exists_tailSmall d ε₀ hε₀
  refine ⟨n₀, fun n hn => ⟨S.localPieces_i hK hε₀ hlt n (hn₀ n hn), fun r hr hr4 => ?_⟩⟩
  have hnS := hn₀ n hn
  obtain ⟨G, hG, hGh, hGPi, hGU⟩ := S.exists_headField hK hε₀ hlt n hnS hr hr4
  obtain ⟨hm, hii⟩ := S.localPieces_ii hK hε₀ hlt n hnS hr4 hr G hG hGh hGPi
  obtain ⟨hpos, hiii⟩ := S.localPieces_iii hK hε₀ hlt n hnS hr4 hr G hG hGh hGPi hGU
  exact ⟨G, hG, hGh, hGPi, hm, hii, hpos, hiii⟩

end NlsGge.Ramer.General.RamerSetting
