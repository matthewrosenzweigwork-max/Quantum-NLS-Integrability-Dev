import Mathlib
import NlsGge.Ramer.General.RamerLocalPiecesGb
import NlsGge.Ramer.General.RamerStep4LocalG
import NlsGge.Ramer.General.RamerLocalToolsG
import NlsGge.Ramer.General.LinearJacobiG
import NlsGge.Ramer.General.AffineJacobiG
import NlsGge.Ramer.General.CameronMartinEG
import NlsGge.Ramer.General.RamerLemma54EventuallyG
import NlsGge.Ramer.General.RamerStep8BridgeG
import NlsGge.Ramer.General.LinearSmallStep8G

/-!
# R10-P4 (part A), generalized (GE8a): lower-bound calculus and the Step-4 recentering

Adapted from `NlsGge/Ramer/RamerLocalLowerBoundA.lean` over a `RamerSetting S`.  Dictionary:
`FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `inclE c s hs ↦ S.incl`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `ramerJac c s hs ↦ S.ramerJac`, `TM c s hs ↦ S.TM`,
`hsDerivH c s hs ↦ S.hsDerivH`, `affineField/affineHomeo c s hs ↦ S.affineField/S.affineHomeo`,
`LocalField hs ↦ S.LocalField`, `cmToFullWeightedHilbert_denseRange ↦ S.incl_denseRange`.

`FGe μ Φ A W J` is the functional "≥" inequality `∫_A g(Φ x) J(x) ≤ ∫_W g`.  It composes, can be
restricted in the target, and is obtained from the set form (Step-8) and from the equality forms
(translation, `Π'`, linear/affine map).  Also: recentering of `ramer_step4_local`.  The calculus
(`FGe`, `fge_of_sets`) is generic and lives in `NlsGge.Ramer.Gen`.

No isotropy of `E` is used: only `S.incl_denseRange` and the packaged `LocalField` bounds.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

section FGeSec

variable {X : Type*} [MeasurableSpace X]

/-- Functional lower bound: `∫_A g(Φ x) J(x) dμ ≤ ∫_W g dμ` for every measurable `g ≥ 0`. -/
def FGe (μ : Measure X) (Φ : X → X) (A W : Set X) (J : X → ℝ≥0∞) : Prop :=
  ∀ g : X → ℝ≥0∞, Measurable g → ∫⁻ x in A, g (Φ x) * J x ∂μ ≤ ∫⁻ y in W, g y ∂μ

variable {μ : Measure X} {Φ Φ₁ Φ₂ : X → X} {A A₁ A₂ W W₁ W₂ : Set X} {J J' J₁ J₂ : X → ℝ≥0∞}

theorem FGe.congr (h : FGe μ Φ A W J) (hJ : J =ᵐ[μ.restrict A] J') : FGe μ Φ A W J' := by
  intro g hg
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (h g hg)
  filter_upwards [hJ] with x hx
  rw [hx]

theorem FGe.comp (hΦ₂ : Measurable Φ₂) (h₁ : FGe μ Φ₁ A₁ W₁ J₁) (h₂ : FGe μ Φ₂ A₂ W₂ J₂)
    (hJ₂ : Measurable J₂) (hW : W₁ ⊆ A₂) :
    FGe μ (Φ₂ ∘ Φ₁) A₁ W₂ (fun x => J₂ (Φ₁ x) * J₁ x) := by
  intro g hg
  have hh : Measurable (fun y => g (Φ₂ y) * J₂ y) := (hg.comp hΦ₂).mul hJ₂
  calc ∫⁻ x in A₁, g ((Φ₂ ∘ Φ₁) x) * (J₂ (Φ₁ x) * J₁ x) ∂μ
      = ∫⁻ x in A₁, (g (Φ₂ (Φ₁ x)) * J₂ (Φ₁ x)) * J₁ x ∂μ := by
        simp only [Function.comp, mul_assoc]
    _ ≤ ∫⁻ y in W₁, g (Φ₂ y) * J₂ y ∂μ := h₁ _ hh
    _ ≤ ∫⁻ y in A₂, g (Φ₂ y) * J₂ y ∂μ := lintegral_mono_set hW
    _ ≤ ∫⁻ y in W₂, g y ∂μ := h₂ g hg

theorem FGe.restrict_target (h : FGe μ Φ A W J) (hΦ : Measurable Φ) {B : Set X}
    (hB : MeasurableSet B) : FGe μ Φ (A ∩ Φ ⁻¹' B) (W ∩ B) J := by
  intro g hg
  have e1 : ∫⁻ x in A ∩ Φ ⁻¹' B, g (Φ x) * J x ∂μ =
      ∫⁻ x in A, (B.indicator g (Φ x)) * J x ∂μ := by
    rw [Set.inter_comm, ← setLIntegral_indicator (hΦ hB)]
    refine lintegral_congr fun x => ?_
    by_cases hx : Φ x ∈ B
    · simp [Set.indicator_of_mem (show x ∈ Φ ⁻¹' B from hx), Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem (show x ∉ Φ ⁻¹' B from hx), Set.indicator_of_notMem hx]
  rw [e1]
  refine (h _ (hg.indicator hB)).trans (le_of_eq ?_)
  rw [setLIntegral_indicator hB, Set.inter_comm]

theorem FGe.congr_fun (hA : MeasurableSet A) {Φ' : X → X} (hΦ : EqOn Φ Φ' A)
    (h : FGe μ Φ A W J) : FGe μ Φ' A W J := by
  intro g hg
  refine le_trans (le_of_eq (setLIntegral_congr_fun hA fun x hx => ?_)) (h g hg)
  rw [hΦ hx]

/-- The functional form from the set form (`A ⊆ Φ⁻¹ W`, `W` measurable, `J` a.e.-measurable). -/
theorem fge_of_sets (hΦ : Measurable Φ)
    (hAW : A ⊆ Φ ⁻¹' W) (hJ : AEMeasurable J (μ.restrict A))
    (hset : ∀ M : Set X, M ⊆ W → ∫⁻ x in A ∩ Φ ⁻¹' M, J x ∂μ ≤ μ M) : FGe μ Φ A W J := by
  intro g hg
  set ν : Measure X := (μ.restrict A).withDensity J with hν
  have hle : ν.map Φ ≤ μ.restrict W := by
    rw [Measure.le_iff]
    intro B hB
    rw [Measure.map_apply hΦ hB, hν, withDensity_apply _ (hΦ hB), Measure.restrict_restrict (hΦ hB),
      Measure.restrict_apply hB]
    have e : A ∩ Φ ⁻¹' B = A ∩ Φ ⁻¹' (B ∩ W) := by
      ext x
      simp only [mem_inter_iff, mem_preimage]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, hAW h1⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
    rw [Set.inter_comm (Φ ⁻¹' B) A, e]
    exact hset _ inter_subset_right |>.trans (le_of_eq (by rw [Set.inter_comm]))
  calc ∫⁻ x in A, g (Φ x) * J x ∂μ = ∫⁻ x, g (Φ x) ∂ν := by
        rw [hν]
        have := lintegral_withDensity_eq_lintegral_mul₀ hJ (hg.comp hΦ).aemeasurable
        refine (Eq.trans ?_ this.symm)
        refine lintegral_congr fun x => ?_
        simp [mul_comm]
    _ = ∫⁻ y, g y ∂(ν.map Φ) := (lintegral_map hg hΦ).symm
    _ ≤ ∫⁻ y, g y ∂(μ.restrict W) := lintegral_mono' hle le_rfl

end FGeSec
end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- `FGe` for the translation `τ_{ie}` (equality, CM-E). (Old: `fge_translation`.) -/
theorem fge_translation (e : S.H) (V : Set S.E) (hV : MeasurableSet V) :
    FGe S.γE (fun x => x + S.incl e) V ((fun x => x + S.incl e) '' V)
      (fun x => ENNReal.ofReal (S.ramerJac (fun _ => e) x)) := fun g hg =>
  (S.lintegral_image_add_incl e g hg V hV).symm.le

/-- `FGe` for the affine map `T₂` (equality, D4), on the whole space. (Old: `fge_affine`.) -/
theorem fge_affine (K : S.E →L[ℝ] S.H) (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) (e : S.H) :
    FGe S.γE (S.affineHomeo T e) univ univ
      (fun x => ENNReal.ofReal (S.ramerJac (S.affineField K e) x)) := by
  intro g hg
  set γ := S.γE with hγ
  set T₂ := S.affineHomeo T e with hT₂
  have hD4 := S.affine_map_symm K T hT e
  have hJ := S.aemeasurable_ofReal_ramerJac (S.affineField K e) (S.affineField_contDiff K e)
  have hgT : Measurable (g ∘ T₂) := hg.comp T₂.continuous.measurable
  have := lintegral_withDensity_eq_lintegral_mul₀ hJ hgT.aemeasurable
  rw [Measure.restrict_univ]
  have h2 : ∫⁻ x, (g ∘ T₂) x ∂γ.withDensity
      (fun x => ENNReal.ofReal (S.ramerJac (S.affineField K e) x)) =
      ∫⁻ y, g y ∂γ := by
    rw [← hD4, lintegral_map hgT T₂.symm.continuous.measurable]
    simp
    rfl
  refine le_of_eq (Eq.trans ?_ (this.symm.trans h2))
  refine lintegral_congr fun x => ?_
  simp [mul_comm]


/-- `FGe` for the Step-8 map `S = TM L`, from `Step8Concl`, restricted to the target `ball 0 r`.
(Old: `fge_S`.) -/
theorem fge_S (L : S.E → S.H)
    (hL : ContDiff ℝ 2 L) {ε₀ : ℝ} (hc : S.Step8Concl L ε₀) (r : ℝ) :
    FGe S.γE (S.TM L)
      (closedBall (0 : S.E) ε₀ ∩
          S.TM L ⁻¹' ball (0 : S.E) (ε₀ / 2) ∩
        S.TM L ⁻¹' ball (0 : S.E) r)
      (ball (0 : S.E) (ε₀ / 2) ∩ ball (0 : S.E) r)
      (fun x => ENNReal.ofReal (S.ramerJac L x)) := by
  have hSc : Continuous (S.TM L) := (S.contDiff_TM L hL).continuous
  have h1 : FGe S.γE (S.TM L)
      (closedBall (0 : S.E) ε₀ ∩
          S.TM L ⁻¹' ball (0 : S.E) (ε₀ / 2))
      (ball (0 : S.E) (ε₀ / 2))
      (fun x => ENNReal.ofReal (S.ramerJac L x)) := by
    refine fge_of_sets hSc.measurable inter_subset_right
      ((S.aemeasurable_ofReal_ramerJac L hL).restrict) (fun M hM => ?_)
    have e : closedBall (0 : S.E) ε₀ ∩
          S.TM L ⁻¹' ball (0 : S.E) (ε₀ / 2) ∩ S.TM L ⁻¹' M =
        closedBall (0 : S.E) ε₀ ∩ S.TM L ⁻¹' M := by
      ext x
      simp only [mem_inter_iff, mem_preimage]
      exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨⟨h1, hM h3⟩, h3⟩⟩
    rw [e]
    exact hc.2.1 M hM
  exact h1.restrict_target hSc.measurable measurableSet_ball

/-- `FGe` for `Π'` on `ball 0 r`, from the equality of `ramer_local_pieces` (ii).
(Old: `fge_Pi`.) -/
theorem fge_Pi (Pi : S.E → S.E)
    (G : S.E → S.H) (r : ℝ)
    (hii : ∀ f : S.E → ℝ≥0∞, Measurable f →
            ∫⁻ y in Pi '' ball (0 : S.E) r, f y ∂S.γE =
              ∫⁻ x in ball (0 : S.E) r, f (Pi x) *
                ENNReal.ofReal (S.ramerJac G x) ∂S.γE) :
    FGe S.γE Pi (ball (0 : S.E) r)
      (Pi '' ball (0 : S.E) r)
      (fun x => ENNReal.ofReal (S.ramerJac G x)) := fun g hg => (hii g hg).symm.le

/-- **Step 4, local form, with a fine centre.**  As `ramer_step4_local` but with
`‖x₀ + i e₁‖ < ε/8` and `LocalField` packaged (radius `ε`, bound `d`), obtained by re-centering
the output of `ramer_step4_local` (the point `x₀ + i e₁` can be taken arbitrarily close to `0`).
(Old: `step4_local_fine`.) -/
theorem step4_local_fine
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K)
    (x₀ : S.E)
    (Tt : S.E ≃L[ℝ] S.E)
    (B : S.E →L[ℝ] S.H)
    (hTts : ∀ y, Tt.symm y = y + S.incl (B y))
    (hv : ∀ u, fderiv ℝ K x₀ u + B (u + S.incl (fderiv ℝ K x₀ u)) = 0) :
    ∃ ε d : ℝ, 0 < ε ∧ ∃ e₁ e₂ : S.H,
      e₂ = -e₁ + K x₀ + B (x₀ + S.incl (K x₀)) ∧
      S.LocalField (K2 S.incl K B e₁ e₂) ε d ∧
      ‖x₀ + S.incl e₁‖ < ε / 8 ∧
      K2 S.incl K B e₁ e₂ (x₀ + S.incl e₁) = 0 := by
  obtain ⟨ε, hε, d, hd, e₁, e₂, he₂, -, hb, -, -, hc, hy0, -⟩ :=
    S.ramer_step4_local K (hK.of_le (by norm_num)) x₀ Tt B hTts hv
  set i := S.incl with hi
  have hdense : DenseRange i := S.incl_denseRange
  obtain ⟨e₁', he₁'⟩ := hdense.exists_dist_lt (-x₀) (by positivity : 0 < ε / 64)
  have hy0' : ‖x₀ + i e₁'‖ < ε / 64 := by
    rw [dist_eq_norm] at he₁'
    have : x₀ + i e₁' = -(-x₀ - i e₁') := by abel
    rw [this, norm_neg]; exact he₁'
  set e₂' : S.H := -e₁' + K x₀ + B (x₀ + i (K x₀)) with he₂'
  set w : S.E := i e₁ - i e₁' with hw
  have hwn : ‖w‖ < ε / 2 + ε / 64 := by
    have : w = (x₀ + i e₁) - (x₀ + i e₁') := by rw [hw]; abel
    rw [this]
    calc _ ≤ ‖x₀ + i e₁‖ + ‖x₀ + i e₁'‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 64 := add_lt_add hy0 hy0'
  have hKeq : K2 i K B e₁' e₂' = fun y => K2 i K B e₁ e₂ (y + w) := by
    have h1 : K2 i K B e₁' e₂' = fun y => Gmap i K B x₀ (y - i e₁') :=
      K2_eq_Gmap_local i K B x₀ e₁'
    have h2 : K2 i K B e₁ e₂ = fun y => Gmap i K B x₀ (y - i e₁) := by
      rw [he₂]; exact K2_eq_Gmap_local i K B x₀ e₁
    rw [h1, h2]
    funext y
    congr 1
    rw [hw]; abel
  have hsm : ContDiff ℝ 2 (K2 i K B e₁' e₂') := by
    unfold K2
    have h1 : ContDiff ℝ 2 (fun y : S.E => K (y - i e₁')) :=
      hK.comp (contDiff_id.sub contDiff_const)
    exact (contDiff_const.add h1).add (B.contDiff.comp
      ((contDiff_id.sub contDiff_const).add (i.contDiff.comp h1)))
  have hnear : ∀ y : S.E, ‖y‖ < ε / 4 → ‖y + w‖ < ε := fun y hy =>
    calc _ ≤ ‖y‖ + ‖w‖ := norm_add_le _ _
      _ < ε := by linarith
  refine ⟨ε / 4, d, by positivity, e₁', e₂', rfl, ⟨hsm, fun y hy => ?_, fun y hy h => ?_⟩, ?_, ?_⟩
  · rw [hKeq]; exact hb _ (hnear y hy)
  · rw [hKeq]
    show ‖fderiv ℝ (fun y => K2 i K B e₁ e₂ (y + w)) y (i h)‖ ≤ _
    have h3 : fderiv ℝ (fun y => K2 i K B e₁ e₂ (y + w)) y =
        fderiv ℝ (K2 i K B e₁ e₂) (y + w) := fderiv_comp_add_right w
    rw [h3]
    exact hc _ (hnear y hy) h
  · linarith
  · have h1 : K2 i K B e₁' e₂' = fun y => Gmap i K B x₀ (y - i e₁') :=
      K2_eq_Gmap_local i K B x₀ e₁'
    have e : x₀ + i e₁' - i e₁' = x₀ := by abel
    rw [h1]
    show Gmap i K B x₀ (x₀ + i e₁' - i e₁') = 0
    rw [e]; exact Gmap_self i K B x₀

end NlsGge.Ramer.General.RamerSetting
