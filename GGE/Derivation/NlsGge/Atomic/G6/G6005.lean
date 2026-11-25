/- G6-005 PRODUCTION01 (proof development kit; source proof development/G6005_PROOF02.lean.txt, author proof development; reviewer proof development).
   Target NlsGge/Atomic/G6/G6005.lean, module NlsGge.Atomic.G6.G6005. Statement verbatim from STATEMENTS/G6.md G6-005. -/
import Mathlib
import NlsGge.GK38.ActionCompact
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38

/- G6-005 PROOF01 (proof development, AUTHOR; not self-reviewed).  Statement verbatim from defs3 STATEMENTS/G6.md G6005 (opens as G6.lean.md).
   Bridge: the hypothesis hw (all real CLMs) gives IsWeakLim for the complex pairing by applying it to the two real CLMs
   x ↦ Re ⟪v,x⟫ and x ↦ Im ⟪v,x⟫ and recombining; then production gapAction_weak_tendsto38.  `hbd` is unused (harmless). -/
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
