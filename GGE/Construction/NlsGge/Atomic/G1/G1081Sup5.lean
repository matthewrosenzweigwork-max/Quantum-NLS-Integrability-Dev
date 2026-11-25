import Mathlib
import NlsGge.Atomic.G1.G1081Host
import NlsGge.Atomic.G1.G1081Sup1
import NlsGge.Atomic.G1.G1081Sup3

                                                                                           
                                                                                                                                  
                                                                                                                              
                                                                                                                  
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign
namespace NlsGge.Atomic.G1081Sup5
noncomputable section

theorem completeGapFlow_unique (n : ℤ) {f g : ℝ → PhysicalL2 → PhysicalL2}
    (hf : completeGapFlow n f) (hg : completeGapFlow n g) : f = g := by
  funext t u
  have := NlsGge.Atomic.G1081Sup3.singleGapField_global_unique n (x := fun s => f s u)
    (y := fun s => g s u) (hf.2 u) (hg.2 u) (by simp only [hf.1 u, hg.1 u])
  exact congrFun this t

theorem completeGapFlow_group (n : ℤ) {f : ℝ → PhysicalL2 → PhysicalL2}
    (hf : completeGapFlow n f) (s t : ℝ) (u : PhysicalL2) :
    f (s + t) u = f s (f t u) := by
  have := NlsGge.Atomic.G1081Sup3.singleGapField_global_unique n
    (x := fun r => f (r + t) u) (y := fun r => f r (f t u))
    (fun r => (hf.2 u (r + t)).comp_add_const r t) (hf.2 (f t u))
    (by simp only [zero_add, hf.1 (f t u)])
  exact congrFun this s

theorem completeGapFlow_exists_of_compact
    (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u)) (n : ℤ) :
    ∃ f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f := by
  have h := fun u : PhysicalL2 =>
    NlsGge.Atomic.G1081Sup3.singleGapField_global_exists_of_compact hcpt n u
  choose g hg0 hg using h
  exact ⟨fun t u => g u t, fun u => hg0 u, fun u t => hg u t⟩

theorem completeGapFlow_existsUnique_of_compact
    (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u)) (n : ℤ) :
    ∃! f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f := by
  obtain ⟨f, hf⟩ := completeGapFlow_exists_of_compact hcpt n
  exact ⟨f, hf, fun g hg => completeGapFlow_unique n hg hf⟩

open Classical in
theorem singleGapFlow_complete_of_compact
    (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u)) (n : ℤ) :
    completeGapFlow n (singleGapFlow n) := by
  have h := completeGapFlow_exists_of_compact hcpt n
  unfold singleGapFlow; rw [dif_pos h]; exact Classical.choose_spec h

-- BEGIN G1080-DEPENDENT
theorem completeGapFlow_exists (n : ℤ) :
    ∃ f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f :=
  completeGapFlow_exists_of_compact (fun v => (G1_080 v).1) n

theorem completeGapFlow_existsUnique (n : ℤ) :
    ∃! f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f :=
  completeGapFlow_existsUnique_of_compact (fun v => (G1_080 v).1) n

theorem singleGapFlow_complete (n : ℤ) : completeGapFlow n (singleGapFlow n) :=
  singleGapFlow_complete_of_compact (fun v => (G1_080 v).1) n

theorem singleGapFlow_zero (n : ℤ) (u : PhysicalL2) : singleGapFlow n 0 u = u :=
  (singleGapFlow_complete n).1 u

theorem singleGapFlow_add (n : ℤ) (s t : ℝ) (u : PhysicalL2) :
    singleGapFlow n (s + t) u = singleGapFlow n s (singleGapFlow n t u) :=
  completeGapFlow_group n (singleGapFlow_complete n) s t u

theorem singleGapFlow_hasDerivAt (n : ℤ) (u : PhysicalL2) (t : ℝ) :
    HasDerivAt (fun s => singleGapFlow n s u) (singleGapField n (singleGapFlow n t u)) t :=
  (singleGapFlow_complete n).2 u t
-- END G1080-DEPENDENT

end
end NlsGge.Atomic.G1081Sup5
