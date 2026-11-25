import Mathlib
import NlsGge.Ramer.General.LinearJacobiG
import NlsGge.Ramer.General.CameronMartinEG

/-!
# D4: the Jacobi formula for the affine `T₂ = T̃ ∘ τ_{ie}`, generalized (GE5)

Adapted from `NlsGge/Ramer/AffineJacobi.lean`.  Dictionary: `c, s, hs ↦ S`,
`FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `inclE ↦ S.incl`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `TM ↦ S.TM`, `ramerJac ↦ S.ramerJac`.
No isotropy is used.

`T̃ = I + iK̃` a continuous linear automorphism of `E`, `τ_{ie} x = x + i e`.
`T₂ x = T̃ (x + i e) = x + i K₂ x` with `K₂ x = K̃ x + (e + K̃ (i e))`, and
`γ_E.map T₂⁻¹ = γ_E.withDensity (ofReal ∘ ramerJac K₂)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen NlsGge.Analysis.RegularizedDeterminant

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- The field of the affine map `T₂`. (Old: `affineField`.) -/
def affineField (K : S.E →L[ℝ] S.H) (e : S.H) : S.E → S.H :=
  fun x => K x + (e + K (S.incl e))

/-- `T₂ = T̃ ∘ τ_{ie}` as a homeomorphism. (Old: `affineHomeo`.) -/
def affineHomeo (T : S.E ≃L[ℝ] S.E) (e : S.H) : S.E ≃ₜ S.E :=
  (Homeomorph.addRight (S.incl e)).trans T.toHomeomorph

theorem affineField_contDiff (K : S.E →L[ℝ] S.H) (e : S.H) :
    ContDiff ℝ 2 (S.affineField K e) :=
  K.contDiff.add contDiff_const

theorem affineHomeo_apply (T : S.E ≃L[ℝ] S.E) (e : S.H) (x : S.E) :
    S.affineHomeo T e x = T (x + S.incl e) := rfl

theorem affineHomeo_symm_apply (T : S.E ≃L[ℝ] S.E) (e : S.H) (y : S.E) :
    (S.affineHomeo T e).symm y = T.symm y - S.incl e := rfl

/-- `T₂ = I + i K₂`. -/
theorem affineHomeo_eq (K : S.E →L[ℝ] S.H) (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) (e : S.H) (x : S.E) :
    S.affineHomeo T e x = x + S.incl (S.affineField K e x) := by
  rw [affineHomeo_apply, hT]
  simp only [affineField, map_add]
  abel

theorem affineField_eq (K : S.E →L[ℝ] S.H) (e : S.H) :
    S.affineField K e = (fun _ => e) + (fun y => K y) ∘ S.TM (fun _ => e) := by
  funext x
  simp only [affineField, Pi.add_apply, Function.comp, S.TM_const, map_add]
  abel

/-- **D4: the affine Jacobi formula.** (Old: `affine_map_symm`.) -/
theorem affine_map_symm
    (K : S.E →L[ℝ] S.H)
    (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) (e : S.H) :
    S.γE.map (S.affineHomeo T e).symm =
      S.γE.withDensity
        (fun x => ENNReal.ofReal (S.ramerJac (S.affineField K e) x)) := by
  set γ := S.γE with hγ
  set f : S.E → S.E := fun x => x - S.incl e with hf
  set g : S.E → S.E := fun x => x + S.incl e with hg
  have hfm : Measurable f := measurable_id.sub_const _
  have hgm : Measurable g := measurable_id.add_const _
  have hgf : ∀ x, g (f x) = x := fun x => sub_add_cancel _ _
  set Jt : S.E → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (S.ramerJac (fun y => K y) x) with hJt
  set Jc : S.E → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (S.ramerJac (fun _ => e) x) with hJc
  have hJtae : AEMeasurable Jt γ := S.aemeasurable_ofReal_ramerJac _ K.contDiff
  have hJtae' := hJtae
  obtain ⟨m, hmm, hm⟩ := hJtae
  have hD3 := S.linear_map_symm K T hT
  have hsymm : ⇑(S.affineHomeo T e).symm = f ∘ T.symm := by
    funext y; rfl
  have hqg : Measure.QuasiMeasurePreserving g γ γ := S.quasiMeasurePreserving_add_incl e
  have hqf : Measure.QuasiMeasurePreserving f γ γ := S.quasiMeasurePreserving_sub_incl e
  have h1 : γ.map (S.affineHomeo T e).symm = (γ.map f).withDensity (m ∘ g) := by
    rw [hsymm, ← Measure.map_map hfm T.symm.continuous.measurable, hD3,
      withDensity_congr_ae hm]
    exact Gen.map_withDensity_inv γ f g hfm hgm hgf m hmm
  have hmf : γ.map f = γ.withDensity Jc := S.map_sub_incl_eq_withDensity e
  have hae : (m ∘ g) =ᵐ[γ.map f] (Jt ∘ g) := by
    have hqg' : Measure.QuasiMeasurePreserving g (γ.map f) γ := by
      refine ⟨hgm, ?_⟩
      rw [Measure.map_map hgm hfm]
      have : g ∘ f = id := funext hgf
      rw [this, Measure.map_id]
    exact hqg'.ae_eq_comp hm.symm
  rw [h1, withDensity_congr_ae hae, hmf]
  have hJgm : AEMeasurable (Jt ∘ g) γ := hJtae'.comp_quasiMeasurePreserving hqg
  have hJcm : AEMeasurable Jc γ := S.aemeasurable_constDensity e
  rw [← withDensity_mul₀ hJcm hJgm]
  refine withDensity_congr_ae ?_
  have hprod := S.ramer_lemma_5_4_eventually univ isOpen_univ (fun _ => e) (fun y => K y)
    contDiff_const K.contDiff (fun N hN => by simpa using S.hT_TM_const e univ N hN)
    (S.hTk_TM_const_eventually e univ)
  filter_upwards [hprod] with x hx
  have hx' := hx (mem_univ x)
  rw [← S.affineField_eq K e] at hx'
  show Jc x * Jt (g x) = _
  rw [hx', ENNReal.ofReal_mul (S.ramerJac_nonneg _ _), mul_comm]
  rfl


end NlsGge.Ramer.General.RamerSetting
