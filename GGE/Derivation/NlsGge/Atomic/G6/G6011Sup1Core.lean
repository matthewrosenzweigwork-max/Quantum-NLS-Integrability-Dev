import Mathlib
import NlsGge.Atomic.LIB.LIB085

/- G6-011/012/013/014 SUPPORT core (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6011Sup1Core.lean.  Supporting lemmas only (no new definition, no Birkhoff name).
   GK Theorem 19.3 proof (printed p. 101-102), stated for a general proper map f between real normed spaces whose every
   point carries a local analytic inverse chart of the exact G6-003 shape:
   * singletonFiber_isClosed: "X is closed" -- a limit z of singleton-fiber values lies in the (closed) range of the
     proper map; a second preimage would, through the two local charts, give the nearby values two preimages.
     (The source's subsequence of preimages is replaced by closedness of the range of a proper map, Mathlib
     IsProperMap.isClosed_range; same two-chart uniqueness argument.)
   * singletonFiber_isOpen: "X is open" -- if values z_k -> z* outside X had second preimages psi_k outside the chart
     domain U, properness gives a cluster point psi* of them with f psi* = z*, hence psi* = phi* in U: contradiction.
     (The source's subsequence psi_k -> psi* is the filter cluster point of IsProperMap.clusterPt_of_mapClusterPt.)
   * bijective_of_singletonFiber: X clopen and nonempty, target connected (landed LIB-085), so X = univ.
   * invFun_analyticOnNhd: GK Theorem 19.4, the global inverse agrees near every value with a local analytic chart inverse. -/
set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.GKDefinitionDesign
namespace G6011Aux

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem singletonFiber_isClosed (f : X → Y) (hf : IsProperMap f)
    (hc : ∀ u : X, ∃ (U : Set X) (V : Set Y) (g : Y → X),
      IsOpen U ∧ u ∈ U ∧ IsOpen V ∧ f u ∈ V ∧
      AnalyticOnNhd ℝ f U ∧ AnalyticOnNhd ℝ g V ∧
      Set.MapsTo f U V ∧ Set.MapsTo g V U ∧
      (∀ v ∈ U, g (f v) = v) ∧ (∀ z ∈ V, f (g z) = z)) :
    IsClosed {z : Y | ∃! u : X, f u = z} := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hsub : closure {z : Y | ∃! u : X, f u = z} ⊆ range f :=
    closure_minimal (fun w hw => by
      obtain ⟨u, hu, -⟩ := hw
      exact ⟨u, hu⟩) hf.isClosed_range
  obtain ⟨u, rfl⟩ := hsub hz
  refine ⟨u, rfl, fun u' hu' => ?_⟩
  by_contra hne
  obtain ⟨A', A, hA', hA, hu'A', huA, hAA'⟩ := t2_separation hne
  obtain ⟨U, V, g, -, huU, hV, hfuV, -, hg, -, -, hgf, hfg⟩ := hc u
  obtain ⟨U', V', g', -, hu'U', hV', hfu'V', -, hg', -, -, hg'f, hfg'⟩ := hc u'
  have hWo : IsOpen ((V ∩ g ⁻¹' A) ∩ (V' ∩ g' ⁻¹' A')) :=
    (hg.continuousOn.isOpen_inter_preimage hV hA).inter
      (hg'.continuousOn.isOpen_inter_preimage hV' hA')
  have hzW : f u ∈ (V ∩ g ⁻¹' A) ∩ (V' ∩ g' ⁻¹' A') := by
    refine ⟨⟨hfuV, ?_⟩, ⟨?_, ?_⟩⟩
    · show g (f u) ∈ A
      rw [hgf u huU]
      exact huA
    · rw [← hu']
      exact hfu'V'
    · show g' (f u) ∈ A'
      rw [← hu', hg'f u' hu'U']
      exact hu'A'
  obtain ⟨w, ⟨⟨hwV, hwA⟩, ⟨hwV', hwA'⟩⟩, hwS⟩ := mem_closure_iff.1 hz _ hWo hzW
  obtain ⟨v, -, hv⟩ := hwS
  have h1 : g w = v := hv _ (hfg w hwV)
  have h2 : g' w = v := hv _ (hfg' w hwV')
  have hvA : v ∈ A := h1 ▸ hwA
  have hvA' : v ∈ A' := h2 ▸ hwA'
  exact Set.disjoint_left.1 hAA' hvA' hvA

theorem singletonFiber_isOpen (f : X → Y) (hf : IsProperMap f)
    (hc : ∀ u : X, ∃ (U : Set X) (V : Set Y) (g : Y → X),
      IsOpen U ∧ u ∈ U ∧ IsOpen V ∧ f u ∈ V ∧
      AnalyticOnNhd ℝ f U ∧ AnalyticOnNhd ℝ g V ∧
      Set.MapsTo f U V ∧ Set.MapsTo g V U ∧
      (∀ v ∈ U, g (f v) = v) ∧ (∀ z ∈ V, f (g z) = z)) :
    IsOpen {z : Y | ∃! u : X, f u = z} := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨u, rfl, huniq⟩
  obtain ⟨U, V, g, hU, huU, hV, hfuV, -, -, -, -, hgf, hfg⟩ := hc u
  by_contra hcon
  have hne : (comap f (𝓝 (f u)) ⊓ 𝓟 Uᶜ).NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro s hs
    obtain ⟨N, hN, hNs⟩ := mem_comap.1 hs
    have hNV : N ∩ V ∈ 𝓝 (f u) := inter_mem hN (hV.mem_nhds hfuV)
    have hnot : ¬ (N ∩ V ⊆ {z : Y | ∃! u : X, f u = z}) :=
      fun h => hcon (mem_of_superset hNV h)
    rw [Set.not_subset] at hnot
    obtain ⟨w, ⟨hwN, hwV⟩, hwS⟩ := hnot
    have hex : ∃ v : X, f v = w ∧ v ≠ g w := by
      by_contra hno
      push_neg at hno
      exact hwS ⟨g w, hfg w hwV, hno⟩
    obtain ⟨v, hfv, hvne⟩ := hex
    refine ⟨v, hNs (show f v ∈ N from hfv ▸ hwN), fun hvU => hvne ?_⟩
    rw [← hgf v hvU, hfv]
  have hle : map f (comap f (𝓝 (f u)) ⊓ 𝓟 Uᶜ) ≤ 𝓝 (f u) :=
    (map_mono inf_le_left).trans map_comap_le
  have hmc : MapClusterPt (f u) (comap f (𝓝 (f u)) ⊓ 𝓟 Uᶜ) f :=
    ClusterPt.of_le_nhds hle
  obtain ⟨x, hfx, hx⟩ := hf.clusterPt_of_mapClusterPt hmc
  have hxu : x = u := huniq x hfx
  subst hxu
  have hcl : ClusterPt x (𝓟 Uᶜ) := hx.mono inf_le_right
  rw [clusterPt_principal_iff] at hcl
  obtain ⟨y, hyU, hyUc⟩ := hcl U (hU.mem_nhds huU)
  exact hyUc hyU

theorem bijective_of_singletonFiber (f : X → Y)
    (hS : IsClopen {z : Y | ∃! u : X, f u = z}) (h0 : ∃! u : X, f u = 0) :
    Function.Bijective f := by
  have huniv : {z : Y | ∃! u : X, f u = z} = Set.univ :=
    NlsGge.Atomic.LIB085.nonempty_clopen_eq_univ hS ⟨0, h0⟩
  have hall : ∀ z : Y, ∃! u : X, f u = z := fun z => by
    have hz : z ∈ {z : Y | ∃! u : X, f u = z} := by
      rw [huniv]
      exact Set.mem_univ z
    exact hz
  refine ⟨fun a b hab => (hall (f b)).unique hab rfl, fun z => ?_⟩
  obtain ⟨u, hu, -⟩ := hall z
  exact ⟨u, hu⟩

theorem invFun_analyticOnNhd (f : X → Y) (hbij : Function.Bijective f)
    (hc : ∀ u : X, ∃ (U : Set X) (V : Set Y) (g : Y → X),
      IsOpen U ∧ u ∈ U ∧ IsOpen V ∧ f u ∈ V ∧
      AnalyticOnNhd ℝ f U ∧ AnalyticOnNhd ℝ g V ∧
      Set.MapsTo f U V ∧ Set.MapsTo g V U ∧
      (∀ v ∈ U, g (f v) = v) ∧ (∀ z ∈ V, f (g z) = z)) :
    AnalyticOnNhd ℝ (Function.invFun f) Set.univ := by
  intro z _
  obtain ⟨u, rfl⟩ := hbij.2 z
  obtain ⟨U, V, g, -, -, hV, hfuV, -, hg, -, -, -, hfg⟩ := hc u
  have heq : g =ᶠ[𝓝 (f u)] Function.invFun f := by
    filter_upwards [hV.mem_nhds hfuV] with w hw
    have h := Function.leftInverse_invFun hbij.1 (g w)
    rw [hfg w hw] at h
    exact h.symm
  exact (hg (f u) hfuV).congr heq

end G6011Aux
end NlsGge.GKDefinitionDesign
