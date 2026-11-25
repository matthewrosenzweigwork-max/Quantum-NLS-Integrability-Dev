import NlsGge.GK38.AbelianLocalSolutionGraph
import NlsGge.GK38.AbelianClosedSolutionProjection
import Mathlib.Topology.IsLocalHomeomorph

/-! Uncompiled concrete solution projection local charts. The ONLY ordinary
intermediate hypothesis is literal actual hQ at actual gap-zero points;
parent P4 must discharge it before final covering/global P5 credit. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5SolutionProjection_localHomeomorph_of_actual_inverse38 (n : ℤ)
    (hQ : ∀ p : p5RealSolutionSpace38 n,
      (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible) :
    IsLocalHomeomorphOn (p5RealSolutionProjection38 n) univ := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict (s := univ)).mpr
  intro p₀ _
  obtain ⟨U,V,ψ,hUo,huU,hVo,htV,hψbase,hψan,hbranch⟩ :=
    p5Actual_local_analytic_gap_graph_of_inverse38 n p₀.val.1 p₀.val.2
      p₀.property.1 p₀.property.2 (hQ p₀)
  let O : Set (p5RealSolutionSpace38 n) := {p | p.val.1 ∈ U ∧ p.val.2 ∈ V}
  have hOo : IsOpen O :=
    (hUo.preimage (continuous_fst.comp continuous_subtype_val)).inter
      (hVo.preimage (continuous_snd.comp continuous_subtype_val))
  have hpO : p₀ ∈ O := ⟨huU,htV⟩
  let g : U → O := fun u =>
    ⟨⟨(u.val,ψ u.val),(hbranch u.val u.property).2.1,
      (hbranch u.val u.property).2.2.1⟩,u.property,(hbranch u.val u.property).1⟩
  have hψU : Continuous (fun u : U => ψ u.val) := hψan.continuousOn.domRestrict
  have hga : Continuous (fun u : U => (u.val,ψ u.val)) :=
    continuous_subtype_val.prodMk hψU
  have hgs : Continuous (fun u : U => (g u).val) :=
    hga.subtype_mk (fun u => (g u).val.property)
  have hg : Continuous g := hgs.subtype_mk (fun u => (g u).property)
  let H : O ≃ₜ U :=
    { toEquiv :=
        { toFun := fun p => ⟨p.val.val.1,p.property.1⟩
          invFun := g
          left_inv := by
            intro p
            apply Subtype.ext
            apply Subtype.ext
            apply Prod.ext
            · rfl
            · exact (hbranch p.val.val.1 p.property.1).2.2.2 p.val.val.2
                p.property.2 |>.mp p.val.property
          right_inv := by
            intro u
            apply Subtype.ext
            rfl }
      continuous_toFun := (continuous_fst.comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
          (fun p => p.property.1)
      continuous_invFun := hg }
  refine ⟨O,hOo.mem_nhds hpO,?_⟩
  exact hUo.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding

end
end NlsGge.GK38
