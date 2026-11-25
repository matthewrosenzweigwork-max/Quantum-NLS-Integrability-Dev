import Mathlib
import NlsGge.Atomic.G6.G6020
import NlsGge.Atomic.G1.G1081Host
import NlsGge.Atomic.G1.G1081Sup2
import NlsGge.Atomic.G1.G1081Sup3
import NlsGge.Atomic.G1.G1081Sup5

/- G1-081 SUP6 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1081Sup6.lean.
   Isospectral invariance of singleGapFlow for ALL real t: t >= 0 by Sup2 with c = 1 on gamma s = flow s u, T = t+1;
   t < 0 by Sup2 with c = -1 on gamma s = flow (-s) u (Sup3.reflect_hasDerivAt), T = -t+1. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign
namespace NlsGge.Atomic.G1081Sup6
noncomputable section

theorem singleGapFlow_isospectral_of_compact
    (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u)) (n : ℤ) (t : ℝ) (u : PhysicalL2) :
    isospectral u (singleGapFlow n t u) := by
  have hc := NlsGge.Atomic.G1081Sup5.singleGapFlow_complete_of_compact hcpt n
  rcases le_or_gt 0 t with ht | ht
  · have h := NlsGge.Atomic.G1081Sup2.isospectral_of_solution_Ico n
      (γ := fun s => singleGapFlow n s u) (T := t + 1) 1
      (fun s _ => by
        simpa only [one_smul] using (hc.2 u s).hasDerivWithinAt)
      t ⟨ht, by linarith⟩
    simpa only [hc.1 u] using h
  · have h := NlsGge.Atomic.G1081Sup2.isospectral_of_solution_Ico n
      (γ := fun s => singleGapFlow n (-s) u) (T := -t + 1) (-1)
      (fun s _ => by
        have := (NlsGge.Atomic.G1081Sup3.reflect_hasDerivAt
          (V := singleGapField n) (x := fun r => singleGapFlow n r u)
          (fun r => hc.2 u r) s).hasDerivWithinAt (s := Ico 0 (-t + 1))
        simpa only [neg_one_smul] using this)
      (-t) ⟨by linarith, by linarith⟩
    simpa only [neg_zero, neg_neg, hc.1 u] using h

-- BEGIN G1080-DEPENDENT
theorem singleGapFlow_isospectral (n : ℤ) (t : ℝ) (u : PhysicalL2) :
    isospectral u (singleGapFlow n t u) :=
  singleGapFlow_isospectral_of_compact (fun v => (G1_080 v).1) n t u
-- END G1080-DEPENDENT

end
end NlsGge.Atomic.G1081Sup6
