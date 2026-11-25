                                                                                                                      
                                                                                                                         
import Mathlib
import NlsGge.GK38.ActionCompact
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38

                                                                                                                                      
                                                                                                                        
                                                                                                                           
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6005 (n : ℤ) (u : ℕ → PhysicalL2) (v : PhysicalL2)
    (hbd : Bornology.IsBounded (Set.range u))
    (hw : ∀ L : PhysicalL2 →L[ℝ] ℝ,
      Tendsto (fun j : ℕ => L (u j)) atTop (𝓝 (L v))) :
  Tendsto (fun j : ℕ => actualGapActionAllE02_38 (u j) n) atTop
    (𝓝 (actualGapActionAllE02_38 v n)) := by
  have hW : IsWeakLim u v := by
    intro w
    let P : PhysicalL2 →L[ℝ] ℂ := (innerSL ℂ w).restrictScalars ℝ
    have hre := hw (Complex.reCLM.comp P)
    have him := hw (Complex.imCLM.comp P)
    simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply] at hre him
    have hc : ∀ x : PhysicalL2, (P x) = ((P x).re : ℂ) + ((P x).im : ℂ) * Complex.I := fun x =>
      (Complex.re_add_im (P x)).symm
    have hP : ∀ x : PhysicalL2, P x = inner ℂ w x := fun x => rfl
    have h1 : Tendsto (fun j : ℕ => ((P (u j)).re : ℂ) + ((P (u j)).im : ℂ) * Complex.I) atTop
        (𝓝 (((P v).re : ℂ) + ((P v).im : ℂ) * Complex.I)) :=
      ((Complex.continuous_ofReal.tendsto _).comp hre).add
        (((Complex.continuous_ofReal.tendsto _).comp him).mul tendsto_const_nhds)
    have e1 : (fun j : ℕ => ((P (u j)).re : ℂ) + ((P (u j)).im : ℂ) * Complex.I) =
        fun j : ℕ => inner ℂ w (u j) := funext fun j => (hc (u j)).symm
    have e2 : ((P v).re : ℂ) + ((P v).im : ℂ) * Complex.I = inner ℂ w v := (hc v).symm
    rw [e1, e2] at h1
    exact h1
  exact gapAction_weak_tendsto38 u v hW n


end
end NlsGge.GKDefinitionDesign
