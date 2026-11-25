import Mathlib
import NlsGge.Atomic.G1.G1083Host
import NlsGge.Atomic.G1.G1083
import NlsGge.Atomic.G1.G1080
import NlsGge.Atomic.G1.G1082Sup5
import NlsGge.Atomic.G6.G6020

/- G1-084 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1084.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from root/gpt6pro_followup11 STATEMENTS/G1.md section G1-084.
   Route: (1) continuity coordinatewise (analyticOnNhd_gkMu38 / analyticOnNhd_deltaMu38, continuous_pi);
   (2) maps-to: gkMu in the gap (gkMu_mem_gap38 + isospectral endpoints), deltaMu^2 = Re Delta^2 - 4 (deltaMu_squared38);
   (3) surjectivity: nested nonempty compact sets {v in isospectralSet u | coordinates in [-k,k] equal p} (G1-083, G1_080 compact,
   G6020 closed, continuity), nonempty intersection (Cantor). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem continuous_signedDirichletData : Continuous (signedDirichletData : PhysicalL2 → ℤ → ℝ × ℝ) :=
  continuous_pi fun n =>
    ((continuousOn_univ.mp (analyticOnNhd_gkMu38 n).continuousOn).prodMk
      (continuousOn_univ.mp (analyticOnNhd_deltaMu38 n).continuousOn))

theorem signedDirichletData_mem_gapCircle {u v : PhysicalL2} (hv : v ∈ isospectralSet u) (n : ℤ) :
    signedDirichletData v n ∈ gapCircle u n := by
  have h : isospectral u v := hv
  have hm := gkMu_mem_gap38 v n
  rw [isospectral_gapLower_eq h n, isospectral_gapUpper_eq h n] at hm
  refine ⟨hm.1, hm.2, ?_⟩
  have := deltaMu_squared38 v n
  rw [show discrim (realSlice v) = discrim (realSlice u) from funext h] at this
  have e : (signedDirichletData v n).1 = gkMu v n := rfl
  have e2 : (signedDirichletData v n).2 = deltaMu v n := rfl
  rw [e, e2]
  linarith

theorem G1_084 (u : PhysicalL2) :
    ContinuousOn signedDirichletData (isospectralSet u) ∧
    MapsTo signedDirichletData (isospectralSet u) (gapCircleProduct u) ∧
    SurjOn signedDirichletData (isospectralSet u) (gapCircleProduct u) := by
  refine ⟨continuous_signedDirichletData.continuousOn, fun v hv n => signedDirichletData_mem_gapCircle hv n, ?_⟩
  intro p hp
  have hK : IsCompact (isospectralSet u) := (G1_080 u).1
  have hKc : IsClosed (isospectralSet u) := G6020 u
  have hcl : ∀ S : Finset ℤ, IsClosed {v : PhysicalL2 | ∀ n ∈ S, signedDirichletData v n = p n} := fun S => by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply n).comp continuous_signedDirichletData) continuous_const
  let t : ℕ → Set PhysicalL2 := fun k =>
    isospectralSet u ∩ {v | ∀ n ∈ Finset.Icc (-(k : ℤ)) k, signedDirichletData v n = p n}
  have htd : ∀ i, t (i + 1) ⊆ t i := fun i v hv =>
    ⟨hv.1, fun n hn => hv.2 n (by simp only [Finset.mem_Icc] at hn ⊢; push_cast; omega)⟩
  have htn : ∀ i, (t i).Nonempty := fun i => by
    obtain ⟨v, hv, hF, -⟩ := G1_083 u (Finset.Icc (-(i : ℤ)) i) p (fun n _ => hp n)
    exact ⟨v, hv, hF⟩
  have ht0 : IsCompact (t 0) := hK.inter_right (hcl _)
  obtain ⟨v, hv⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0
    (fun i => hKc.inter (hcl _))
  have hv' := Set.mem_iInter.1 hv
  refine ⟨v, (hv' 0).1, funext fun n => (hv' n.natAbs).2 n ?_⟩
  simp only [Finset.mem_Icc]; omega

end
end NlsGge.GKDefinitionDesign
