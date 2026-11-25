import QuantumNLS.TerraMultiRound85TranslationCubic
import QuantumNLS.TerraMultiRound85FlowScalingL2
import QuantumNLS.BornTranslation

/-! Translation covariance of the actual cubic physical flow. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Global
open QuantumNLS.H1Bridge QuantumNLS.L2Flow QuantumNLS.DuhamelDuality
open QuantumNLS.TerraMultiRound85H1Bridge QuantumNLS.TerraMultiRound85H1Density
open QuantumNLS.TerraMultiRound85TranslationH1 QuantumNLS.TerraMultiRound85TranslationCubic
namespace QuantumNLS.TerraMultiRound85TranslationFlow
variable {L : ℝ} [Fact (0 < L)]

/-- The Fourier multiplier is the actual translation of a physical field. -/
theorem emb_translate (y : ℝ) (a : h04 L 1) :
    emb (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y a) = QuantumNLS.BornTranslation.trans y (emb a) := by
  apply MeasureTheory.Lp.ext
  have h1 := emb_coeFn (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y a)
  have h2 := QuantumNLS.BornTranslation.coeFn_trans y (emb a)
  have hmp := measurePreserving_add_right (volume : Measure (AddCircle L)) (y : AddCircle L)
  have h3 := hmp.quasiMeasurePreserving.ae_eq_comp (emb_coeFn a)
  filter_upwards [h1,h2,h3] with x h1x h2x h3x
  rw [h1x,h2x]
  change seriesRep L (translatedSeq (L := L) y a.val) x = (emb a : AddCircle L → ℂ) (x + (y : AddCircle L))
  rw [series_translated]
  exact h3x.symm

/-- A global H¹ mild solution remains mild after spatial translation. -/
theorem translate_mild {κ : ℝ} (y : ℝ) (u0 : h04 L 1) (u : ℝ → h04 L 1)
    (hu : IsMild (le_refl (1 : ℝ)) κ Set.univ u0 u) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y u0) (fun t => QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y (u t)) := by
  refine ⟨Set.mem_univ _, Set.ordConnected_univ, ?_, ?_⟩
  · exact (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y).continuous.comp_continuousOn hu.cont
  · intro t ht
    have hi := integrable_duhamel (le_refl (1 : ℝ)) hu.ordConnected hu.cont t 0 t
      (Set.mem_univ 0) (Set.mem_univ t)
    rw [hu.duhamel_eq t (Set.mem_univ t)]
    unfold duhamel
    rw [map_sub, map_smul, translate_Sgrp, ← (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y).intervalIntegral_comp_comm hi]
    congr 2
    apply intervalIntegral.integral_congr
    intro r hr
    change QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y (Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (u r))) =
      Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y (u r)))
    rw [translate_Sgrp, Fh_translate]

/-- The actual L² physical flow commutes with spatial translations. -/
theorem translate_flow {κ : ℝ} (hκ : 0 ≤ κ) (y : ℝ) (u : HL L) (t : ℝ) :
    flowMap hκ (QuantumNLS.BornTranslation.trans y u) t =
      QuantumNLS.BornTranslation.trans y (flowMap hκ u t) := by
  let T : HL L →ₗᵢ[ℂ] HL L := QuantumNLS.BornTranslation.trans y
  have h1 : Continuous (fun u : HL L => flowMap hκ (T u) t) :=
    (continuous_flowMap hκ t).comp T.continuous
  have h2 : Continuous (fun u : HL L => T (flowMap hκ u t)) :=
    T.continuous.comp (continuous_flowMap hκ t)
  have he := Continuous.ext_on (denseRange_emb (L := L)) h1 h2 (by
    rintro _ ⟨g, rfl⟩
    let v := umax (le_refl (1 : ℝ)) κ g
    have hv := umax_mild (hs := le_refl (1 : ℝ)) hκ g
    rw [Imax1_eq_univ hκ g] at hv
    have hh := flowMap_of_global_mild hκ (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y g) (fun t => QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) 1 y (v t))
      (translate_mild y g v hv) t
    change flowMap hκ (T (emb g)) t = T (flowMap hκ (emb g) t)
    rw [flowMap_H1 hκ g t]
    simpa only [emb_translate] using hh)
  exact congrFun he u

#print axioms emb_translate
#print axioms translate_mild
#print axioms translate_flow
end QuantumNLS.TerraMultiRound85TranslationFlow
