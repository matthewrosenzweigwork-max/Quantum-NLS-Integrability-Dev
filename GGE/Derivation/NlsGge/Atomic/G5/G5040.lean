import Mathlib
import NlsGge.Atomic.G5.G5039
import NlsGge.Atomic.G4.G4041
import NlsGge.Atomic.G1.G1066
import NlsGge.Atomic.G5.G5028Sup2
import NlsGge.Atomic.G5.G5019Sup3
import NlsGge.Atomic.G5.G5029Sup4Core

/- G5-040 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5040.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5040` VERBATIM from followup12 STATEMENTS/G5.md section G5-040 (round 14 cluster 5 retains unrestricted indices).
   No lexical repair.
   Proof (GK Theorem 18.8, "by continuity of the bracket ... it suffices to check on L2r minus (Z_m u Z_n)"):
   each bracket u |-> pairPoissonCLM (dF (realSlice u)) (dG (realSlice u)) is continuous on PhysicalL2 (landed G4041
   analyticity on sourceBetaW, G5029Sup4Aux.continuousAt_fderiv_comp_realSlice, G5019Sup3.continuous_pairPoissonCLM);
   the open-gap locus {gamma2 m != 0, gamma2 n != 0} contains the dense all-gaps-open set of landed G1-066
   (G5028.gamma2_ne_zero_of_lt), where G5039 gives the value; Continuous.ext_on extends it.  See G5040_ROUTE.md for the
   density input (G1-066 instead of the codimension-two statement of GK Prop 7.10; both are TASK_INDEX prerequisites). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5040 (u : PhysicalL2) (m n : ℤ) :
  pairPoisson (cartesianX m) (cartesianX n) (realSlice u) = 0 ∧
  pairPoisson (cartesianX m) (cartesianY n) (realSlice u) =
    -(if m = n then (1 : ℂ) else 0) ∧
  pairPoisson (cartesianY m) (cartesianY n) (realSlice u) = 0 := by
  have hdense : Dense {w : PhysicalL2 | gamma2 (realSlice w) m ≠ 0 ∧
      gamma2 (realSlice w) n ≠ 0} :=
    by
      refine NlsGge.Atomic.G1066.G1_066.1.mono ?_
      intro w hw
      have hw' : ∀ k : ℤ, actualGapLowerAllE02_38 w k < actualGapUpperAllE02_38 w k := hw
      exact ⟨NlsGge.Atomic.G5028.gamma2_ne_zero_of_lt w m (hw' m), NlsGge.Atomic.G5028.gamma2_ne_zero_of_lt w n (hw' n)⟩
  have hD : ∀ f : PotPair → ℂ, AnalyticOnNhd ℂ f sourceBetaW →
      Continuous (fun w : PhysicalL2 => fderiv ℂ f (realSlice w)) := fun f hf =>
    continuous_iff_continuousAt.2 fun w =>
      G5029Sup4Aux.continuousAt_fderiv_comp_realSlice f sourceBetaW sourceFamily.V_open hf w
        (sourceFamily.V_real (Set.mem_range_self w))
  have key : ∀ (f g : PotPair → ℂ) (c : ℂ), AnalyticOnNhd ℂ f sourceBetaW →
      AnalyticOnNhd ℂ g sourceBetaW →
      (∀ w : PhysicalL2, gamma2 (realSlice w) m ≠ 0 ∧ gamma2 (realSlice w) n ≠ 0 →
        pairPoisson f g (realSlice w) = c) →
      pairPoisson f g (realSlice u) = c := by
    intro f g c hf hg h
    have hP : Continuous (fun w : PhysicalL2 => pairPoisson f g (realSlice w)) :=
      G5019Sup3.continuous_pairPoissonCLM.comp ((hD f hf).prodMk (hD g hg))
    exact congrFun (Continuous.ext_on hdense hP continuous_const fun w hw => h w hw) u
  exact ⟨key _ _ _ (G4041 m).1 (G4041 n).1 fun w hw => (G5039 w m n hw.1 hw.2).1,
    key _ _ _ (G4041 m).1 (G4041 n).2 fun w hw => (G5039 w m n hw.1 hw.2).2.1,
    key _ _ _ (G4041 m).2 (G4041 n).2 fun w hw => (G5039 w m n hw.1 hw.2).2.2⟩

end
end NlsGge.GKDefinitionDesign
