import Mathlib
import NlsGge.Hierarchy.ALFiniteMeasure38

                                                                                                                                            
                                                                                                                                           
                                                                                                                                              
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Set Filter Topology MeasureTheory
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

theorem al027 {L : ℕ} [NeZero L]
    (α : ZMod L → ℂ) (hα : IsALField38 α) (j : ℕ) (t : ℝ) :
  alK38 (alFlow38 alHd t α) j = alK38 α j := by
  have hαd : α ∈ alDisk38 L := hα
  have hγ : ∀ s ∈ (Set.univ : Set ℝ), IsALField38 (alFlow38 alHd s α) ∧
      HasDerivAt (fun s => alFlow38 alHd s α) (alX38 alHd (alFlow38 alHd s α)) s :=
    fun s _ => ⟨alFlow_mem38 alHd_contDiffOn38 alBracket_mass_alHd38 hαd s,
      alFlow_hasDerivAt38 alHd_contDiffOn38 alBracket_mass_alHd38 hαd s⟩
  have := alK_const38 (U := Set.univ) isOpen_univ isPreconnected_univ
    (γ := fun s => alFlow38 alHd s α) hγ (Set.mem_univ t) (Set.mem_univ 0) j
  simpa [alFlow_zero38 alHd_contDiffOn38 alBracket_mass_alHd38] using this

end NlsGge.ThirdConsultation.AL
