import Mathlib
import NlsGge.Ramer.LinearJacobi
import NlsGge.Ramer.CameronMartinE
import NlsGge.Ramer.RamerLemma54Eventually

/-!
# D4: the Jacobi formula for the affine `T₂ = T̃ ∘ τ_{ie}`

`T̃ = I + iK̃` a continuous linear automorphism of `E`, `τ_{ie} x = x + i e`.
`T₂ x = T̃ (x + i e) = x + i K₂ x` with `K₂ x = K̃ x + (e + K̃ (i e))`, and
`γ_E.map T₂⁻¹ = γ_E.withDensity (ofReal ∘ ramerJac K₂)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- The field of the affine map `T₂`. -/
def affineField (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (e : ActualCM c) : FullWeightedHilbert c s → ActualCM c :=
  fun x => K x + (e + K (inclE c s hs e))

/-- `T₂ = T̃ ∘ τ_{ie}` as a homeomorphism. -/
def affineHomeo (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s) (e : ActualCM c) :
    FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s :=
  (Homeomorph.addRight (inclE c s hs e)).trans T.toHomeomorph

variable {c s}

theorem affineField_contDiff (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (e : ActualCM c) : ContDiff ℝ 2 (affineField c s hs K e) :=
  K.contDiff.add contDiff_const

theorem affineHomeo_apply (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s) (e : ActualCM c)
    (x : FullWeightedHilbert c s) : affineHomeo c s hs T e x = T (x + inclE c s hs e) := rfl

theorem affineHomeo_symm_apply (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s) (e : ActualCM c)
    (y : FullWeightedHilbert c s) : (affineHomeo c s hs T e).symm y = T.symm y - inclE c s hs e :=
  rfl

/-- `T₂ = I + i K₂`. -/
theorem affineHomeo_eq (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hT : ∀ x, T x = x + inclE c s hs (K x)) (e : ActualCM c) (x : FullWeightedHilbert c s) :
    affineHomeo c s hs T e x = x + inclE c s hs (affineField c s hs K e x) := by
  rw [affineHomeo_apply, hT]
  simp only [affineField, map_add]
  abel

theorem affineField_eq (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (e : ActualCM c) :
    affineField c s hs K e =
      (fun _ => e) + (fun y => K y) ∘ TM c s hs (fun _ => e) := by
  funext x
  simp only [affineField, Pi.add_apply, Function.comp, TM_const, map_add]
  abel

variable (c s)

/-- **D4: the affine Jacobi formula.** -/
theorem affine_map_symm (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hT : ∀ x, T x = x + inclE c s hs (K x)) (e : ActualCM c) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map (affineHomeo c s hs T e).symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (ramerJac c s hs (affineField c s hs K e) x)) := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  set f : FullWeightedHilbert c s → FullWeightedHilbert c s := fun x => x - inclE c s hs e with hf
  set g : FullWeightedHilbert c s → FullWeightedHilbert c s := fun x => x + inclE c s hs e with hg
  have hfm : Measurable f := measurable_id.sub_const _
  have hgm : Measurable g := measurable_id.add_const _
  have hgf : ∀ x, g (f x) = x := fun x => sub_add_cancel _ _
  set Jt : FullWeightedHilbert c s → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (ramerJac c s hs (fun y => K y) x) with hJt
  set Jc : FullWeightedHilbert c s → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (ramerJac c s hs (fun _ => e) x) with hJc
  have hJtae : AEMeasurable Jt γ := aemeasurable_ofReal_ramerJac c s hs _ K.contDiff
  have hJtae' := hJtae
  obtain ⟨m, hmm, hm⟩ := hJtae
  have hD3 := linear_map_symm c s hs K T hT
  have hsymm : ⇑(affineHomeo c s hs T e).symm = f ∘ T.symm := by
    funext y; rfl
  have hqg : Measure.QuasiMeasurePreserving g γ γ := quasiMeasurePreserving_add_inclE c s hs e
  have hqf : Measure.QuasiMeasurePreserving f γ γ := quasiMeasurePreserving_sub_inclE c s hs e
  have h1 : γ.map (affineHomeo c s hs T e).symm = (γ.map f).withDensity (m ∘ g) := by
    rw [hsymm, ← Measure.map_map hfm T.symm.continuous.measurable, hD3,
      withDensity_congr_ae hm]
    exact map_withDensity_inv γ f g hfm hgm hgf m hmm
  have hmf : γ.map f = γ.withDensity Jc := map_sub_inclE_eq_withDensity c s hs e
  have hae : (m ∘ g) =ᵐ[γ.map f] (Jt ∘ g) := by
    have hqg' : Measure.QuasiMeasurePreserving g (γ.map f) γ := by
      refine ⟨hgm, ?_⟩
      rw [Measure.map_map hgm hfm]
      have : g ∘ f = id := funext hgf
      rw [this, Measure.map_id]
    exact hqg'.ae_eq_comp hm.symm
  rw [h1, withDensity_congr_ae hae, hmf]
  have hJgm : AEMeasurable (Jt ∘ g) γ := hJtae'.comp_quasiMeasurePreserving hqg
  have hJcm : AEMeasurable Jc γ := aemeasurable_constDensity c s hs e
  rw [← withDensity_mul₀ hJcm hJgm]
  refine withDensity_congr_ae ?_
  have hprod := ramer_lemma_5_4_eventually c s hs univ isOpen_univ (fun _ => e) (fun y => K y)
    contDiff_const K.contDiff (fun N hN => by simpa using hT_TM_const c s hs e univ N hN)
    (hTk_TM_const_eventually c s hs e univ)
  filter_upwards [hprod] with x hx
  have hx' := hx (mem_univ x)
  rw [← affineField_eq hs K e] at hx'
  show Jc x * Jt (g x) = _
  rw [hx', ENNReal.ofReal_mul (ramerJac_nonneg c s hs _ _), mul_comm]
  rfl

#check @affineField
#check @affineHomeo
#check @affine_map_symm
#print axioms affine_map_symm

end NlsGge.Ramer
