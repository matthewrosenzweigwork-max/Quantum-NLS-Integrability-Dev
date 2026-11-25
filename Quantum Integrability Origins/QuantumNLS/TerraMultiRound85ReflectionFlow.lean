import QuantumNLS.TerraMultiRound85ReflectionCubic
import QuantumNLS.TerraMultiRound85FlowScalingL2
import QuantumNLS.ResetNormalizationBinding

/-! Spatial reflection of the actual cubic flow, via H¹ mild solutions. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Global
open QuantumNLS.H1Bridge QuantumNLS.L2Flow QuantumNLS.DuhamelDuality
open QuantumNLS.TerraMultiRound85H1Bridge QuantumNLS.TerraMultiRound85H1Density
open QuantumNLS.TerraMultiRound85ReflectionH1 QuantumNLS.TerraMultiRound85ReflectionCubic
namespace QuantumNLS.TerraMultiRound85ReflectionFlow
variable {L : ℝ} [Fact (0 < L)]

/-- The coefficient-space reflection is the actual L² spatial reflection. -/
theorem emb_reflect (a : h04 L 1) :
    emb (reflect 1 a) = QuantumNLS.ResetNormalizationUniqueness.reflectR L (emb a) := by
  apply MeasureTheory.Lp.ext
  have h1 := emb_coeFn (reflect 1 a)
  have h2 := QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L (emb a)
  have h3 := (QuantumNLS.ResetNormalizationUniqueness.negMP L).quasiMeasurePreserving.ae_eq_comp (emb_coeFn a)
  filter_upwards [h1, h2, h3] with x h1x h2x h3x
  rw [h1x, h2x]
  change seriesRep L (reverseSeq a.val) x = (emb a : AddCircle L → ℂ) (-x)
  rw [series_reverse]
  exact h3x.symm

/-- A mild H¹ solution remains mild under spatial reflection. -/
theorem reflect_mild {κ : ℝ} (u0 : h04 L 1) (u : ℝ → h04 L 1)
    (hu : IsMild (le_refl (1 : ℝ)) κ Set.univ u0 u) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ (reflect 1 u0) (fun t => reflect 1 (u t)) := by
  refine ⟨Set.mem_univ _, Set.ordConnected_univ, ?_, ?_⟩
  · exact (reflect 1).continuous.comp_continuousOn hu.cont
  · intro t ht
    have hi := integrable_duhamel (le_refl (1 : ℝ)) hu.ordConnected hu.cont t 0 t
      (Set.mem_univ 0) (Set.mem_univ t)
    rw [hu.duhamel_eq t (Set.mem_univ t)]
    unfold duhamel
    rw [map_sub, map_smul, reflect_Sgrp, ← (reflect 1).intervalIntegral_comp_comm hi]
    congr 2
    apply intervalIntegral.integral_congr
    intro r hr
    change reflect 1 (Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (u r))) =
      Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (reflect 1 (u r)))
    rw [reflect_Sgrp, Fh_reflect]

/-- The physical L² flow commutes with spatial reflection. -/
theorem reflect_flow {κ : ℝ} (hκ : 0 ≤ κ) (u : HL L) (t : ℝ) :
    flowMap hκ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) t =
      QuantumNLS.ResetNormalizationUniqueness.reflectR L (flowMap hκ u t) := by
  let R := QuantumNLS.ResetNormalizationUniqueness.reflectR L
  have h1 : Continuous (fun u : HL L => flowMap hκ (R u) t) :=
    (continuous_flowMap hκ t).comp R.continuous
  have h2 : Continuous (fun u : HL L => R (flowMap hκ u t)) :=
    R.continuous.comp (continuous_flowMap hκ t)
  have he := Continuous.ext_on (denseRange_emb (L := L)) h1 h2 (by
    rintro _ ⟨g, rfl⟩
    let v := umax (le_refl (1 : ℝ)) κ g
    have hv := umax_mild (hs := le_refl (1 : ℝ)) hκ g
    rw [Imax1_eq_univ hκ g] at hv
    have hh := flowMap_of_global_mild hκ (reflect 1 g) (fun t => reflect 1 (v t))
      (reflect_mild g v hv) t
    change flowMap hκ (R (emb g)) t = R (flowMap hκ (emb g) t)
    rw [flowMap_H1 hκ g t]
    simpa only [emb_reflect] using hh)
  exact congrFun he u

#print axioms emb_reflect
#print axioms reflect_mild
#print axioms reflect_flow
end QuantumNLS.TerraMultiRound85ReflectionFlow
