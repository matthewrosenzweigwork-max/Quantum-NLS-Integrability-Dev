import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.GK38.IsolatingTopology
import NlsGge.Atomic.Support.ContourCycleCauchy
import NlsGge.Atomic.G2.G2028
import NlsGge.ThirdConsultation.G2.G2037Support1
import NlsGge.ThirdConsultation.G2.G2037Support2
import NlsGge.ThirdConsultation.G2.G2037C5B1
import NlsGge.ThirdConsultation.G2.G2037C5B2
import NlsGge.ThirdConsultation.G2.G2037C5P2C
import NlsGge.ThirdConsultation.G2.G2037C5GAP01

                                                                                                      
                                                                                                   
                                                           
                                                                                                      
                                                                                                       
                                                                                                    
                                                                            
                                                                                                       
                                                                                              
                                                                                    
                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2037P4GapAux

/-- Cycle index of a single closed chain. -/
theorem cycle_index_single {a : ℂ} (c : NlsGge.Atomic.ContourChain.Chain a a) (w : ℂ) :
    (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, c⟩).index w = c.index w := by
  show ∑ _i : Fin 1, c.index w = c.index w
  rw [Fin.sum_univ_one]

/-- Cycle integral of a single closed chain. -/
theorem cycle_integral_single {a : ℂ} (c : NlsGge.Atomic.ContourChain.Chain a a)
    (ω : ℂ → ℂ →L[ℂ] ℂ) :
    (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, c⟩).integral ω = c.integral ω := by
  show ∑ _i : Fin 1, c.integral ω = c.integral ω
  rw [Fin.sum_univ_one]

end G2037P4GapAux

open G2037P4GapAux

/-- (i) A thin gap disc: the gap ellipse lies in the isolating ball of `n` and has zero period. -/
theorem g2037p4_gap_disc_thin (u : PhysicalL2) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hCR : IsolatingFamily38 (realSlice u) C R) (n : ℤ) :
    ∃ D : DiscWithSegment, D.a = lamMinus (realSlice u) n ∧ D.b = lamPlus (realSlice u) n ∧
      (∀ θ : ℝ, ellipseParam D θ ∈ ball (C n) (R n)) ∧
      curveIntegral (complexForm (finiteGapDifferential u S)) (gapCycle D) = 0 := by
  obtain ⟨c, N, hg, hspec⟩ := hCR
  have hc1 : (1 : ℝ) ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcpos : 0 < c⁻¹ / 2 := by
    have := inv_pos.2 hc0
    linarith
  obtain ⟨V, hVo, hφV, -, U0, hUo0, hKU0, -, -, hder⟩ := G2_028 u n
  have hUo : IsOpen (U0 ∩ ball (C n) (R n)) := hUo0.inter isOpen_ball
  have hKball : gapSegment (realSlice u) n ⊆ ball (C n) (R n) := (hspec.1 n).1
  have hKU : gapSegment (realSlice u) n ⊆ U0 ∩ ball (C n) (R n) := subset_inter hKU0 hKball
  have hKc : IsCompact (gapSegment (realSlice u) n) := G2028Aux.isCompact_gapSegment _ _
  obtain ⟨ε, hε, hth⟩ := hKc.exists_thickening_subset_open hUo hKU
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = min (ε / 2) (c⁻¹ / 2) := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hwdef]; exact lt_min (by linarith) hcpos
  have hwε : w < ε := by
    have := min_le_left (ε / 2) (c⁻¹ / 2)
    rw [hwdef]; linarith
  have hwc : w ≤ c⁻¹ / 2 := by rw [hwdef]; exact min_le_right _ _
  set D : DiscWithSegment := g2037gap_disc (lamMinus (realSlice u) n) (lamPlus (realSlice u) n) w hw
    with hD
  have hDw : D.width = w := g2037gap_disc_width _ _ w hw
  -- the gap ellipse lies in U0 ∩ ball and in rootDomain38 (off every gap segment)
  have hray : ∀ θ : ℝ, ellipseParam D θ ∈ U0 ∩ ball (C n) (R n) ∧
      (realSlice u, ellipseParam D θ) ∈ rootDomain38 := by
    intro θ
    obtain ⟨t, ht, hdist⟩ := g2037gap_ellipse_near D θ
    have hz0 : D.midpoint + D.axis * (t : ℂ) ∈ gapSegment (realSlice u) n := by
      have hmem : D.midpoint + D.axis * (t : ℂ) ∈ segment ℝ D.a D.b := by
        rw [(disc_segment_coordinates D).2.2.2]
        exact ⟨t, ht, rfl⟩
      exact hmem
    rw [hDw] at hdist
    have hdistε : dist (ellipseParam D θ) (D.midpoint + D.axis * (t : ℂ)) < ε := by linarith
    have hUθ : ellipseParam D θ ∈ U0 ∩ ball (C n) (R n) :=
      hth (Metric.mem_thickening_iff.2 ⟨_, hz0, hdistε⟩)
    refine ⟨hUθ, realSlice_mem_gkW u, ?_⟩
    intro hmem
    simp only [gapSegments38, Set.mem_iUnion] at hmem
    obtain ⟨k, hk⟩ := hmem
    by_cases hkn : k = n
    · rw [hkn] at hk
      exact g2037gap_ellipse_not_own D θ (by rw [hDw]; exact hw) hk
    · have hz0' : dist (D.midpoint + D.axis * (t : ℂ)) (C n) < R n := by
        have := (hspec.1 n).1 hz0
        exact mem_ball.1 this
      have hdz : dist (ellipseParam D θ) (C n) < R n + c⁻¹ / 2 := by
        have h1 := dist_triangle (ellipseParam D θ) (D.midpoint + D.axis * (t : ℂ)) (C n)
        linarith
      exact g2037gap_tube_miss C R c N hg (realSlice u) hspec n k hkn _ hdz hk
  refine ⟨D, rfl, rfl, fun θ => (hray θ).1.2, ?_⟩
  have hΩo : IsOpen {z : ℂ | (realSlice u, z) ∈ rootDomain38} :=
    isOpen_rootDomain38.preimage (continuous_const.prodMk continuous_id)
  have hrange : Set.range (gapCycle D) ⊆
      (U0 ∩ ball (C n) (R n)) ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38} := by
    rintro _ ⟨t, rfl⟩
    exact hray _
  have hcont : ContinuousOn (finiteGapDifferential u S)
      ((U0 ∩ ball (C n) (R n)) ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38}) := by
    apply ContinuousOn.mono (g2037s1_fgd_analyticOn u S).continuousOn
    intro z hz hc
    rcases hz with ⟨-, hzΩ⟩
    have hz2 : z ∉ gapSegments38 (realSlice u) := by
      obtain ⟨-, h⟩ := hzΩ
      exact h
    unfold finiteGapCuts at hc
    obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.1 hc
    exact hz2 (Set.mem_iUnion.2 ⟨k, hk⟩)
  have hP : ∀ z ∈ (U0 ∩ ball (C n) (R n)) ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38},
      HasDerivAt (localLogDiscriminant n (realSlice u)) (finiteGapDifferential u S z) z := by
    intro z hz
    have hder' := (hder (realSlice u) hφV z hz.1.1 hz.2).2
    rw [g2037s2_deriv_eq_fgd u S hS z hz.2] at hder'
    exact hder'
  have hprim := primitive_curveIntegral (gapCycle D) (gapCycle_piecewise D)
    ((U0 ∩ ball (C n) (R n)) ∩ {z : ℂ | (realSlice u, z) ∈ rootDomain38})
    (finiteGapDifferential u S)
    (localLogDiscriminant n (realSlice u)) (hUo.inter hΩo) hrange hcont hP
  rw [hprim, sub_self]

/-- (ii) **Gap-cycle package for `finiteGapCuts u S`.** -/
theorem g2037p4_hgap (u : PhysicalL2) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) :
    ∃ G : ℤ → NlsGge.Atomic.ContourChain.Cycle,
      (∀ k ∈ S, (G k).range ⊆ (finiteGapCuts u S)ᶜ) ∧
      (∀ k ∈ S, ∀ j ∈ S, ∀ z ∈ gapSegment (realSlice u) j,
        (G k).index z = if j = k then 1 else 0) ∧
      (∀ k ∈ S, (G k).integral
        (fun w => ContinuousLinearMap.toSpanSingleton ℂ (finiteGapDifferential u S w)) = 0) := by
  classical
  obtain ⟨C, R, hCR⟩ : ∃ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 (realSlice u) C R :=
    ⟨_, _, isolating_family38 (realSlice u) (realSlice_mem_gkW u)⟩
  choose D hDa hDb hDball hD0 using fun n => g2037p4_gap_disc_thin u S hS C R hCR n
  choose c hcpath hctrace hcindex using fun n => g2037b2_gapCycle_chain (D n)
  -- no gap cut meets the ellipse of any gap disc
  have hmiss : ∀ k j : ℤ, ∀ z ∈ gapSegment (realSlice u) j, z ∉ Set.range (gapCycle (D k)) := by
    intro k j z hz hzr
    obtain ⟨t, ht⟩ := hzr
    have hz' : z ∈ ball (C k) (R k) := by
      rw [← ht]
      exact hDball k _
    by_cases hjk : j = k
    · have hseg : z ∈ segment ℝ (D k).a (D k).b := by
        rw [hDa k, hDb k, ← hjk]
        exact hz
      rw [← ht] at hseg
      exact g2037gap_ellipse_not_own (D k) (2 * Real.pi * (t : ℝ))
        (disc_segment_coordinates (D k)).1 hseg
    · exact G2037B1Aux.balls_disjoint hCR hjk (g2037b1_gapSegment_subset_ball hCR j hz) hz'
  have hrangeD : ∀ k : ℤ, Set.range (gapCycle (D k)) ⊆ ball (C k) (R k) := by
    rintro k _ ⟨t, rfl⟩
    exact hDball k _
  have htrace_sub : ∀ k : ℤ, (c k).trace ⊆ (finiteGapCuts u S)ᶜ := by
    intro k z hz hzc
    rw [hctrace k] at hz
    unfold finiteGapCuts at hzc
    obtain ⟨j, _, hj⟩ := Set.mem_iUnion₂.1 hzc
    exact hmiss k j z hj hz
  have hfc : ContinuousOn (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ :=
    (g2037s1_fgd_analyticOn u S).continuousOn
  refine ⟨fun k => NlsGge.Atomic.ContourChain.Cycle.single ⟨_, c k⟩, ?_, ?_, ?_⟩
  · intro k _
    rw [NlsGge.Atomic.ContourChain.Cycle.range_single]
    exact htrace_sub k
  · intro k _ j _ z hz
    have hzr : z ∉ Set.range (gapCycle (D k)) := hmiss k j z hz
    by_cases hjk : j = k
    · have hzk : z ∈ gapSegment (realSlice u) k := by
        rw [← hjk]
        exact hz
      rw [if_pos hjk, cycle_index_single, hcindex k z hzr]
      exact g2037p2c_index_one_on_cut k (D k) (hDa k) (hDb k) z hzk
    · rw [if_neg hjk]
      have hzb : z ∉ ball (C k) (R k) := fun h =>
        G2037B1Aux.balls_disjoint hCR hjk (g2037b1_gapSegment_subset_ball hCR j hz) h
      refine NlsGge.Atomic.ContourChain.Cycle.index_eq_zero_of_notMem_ball
        (NlsGge.Atomic.ContourChain.Cycle.single ⟨_, c k⟩) (z₀ := C k) (R := R k) ?_ hzb
      rw [NlsGge.Atomic.ContourChain.Cycle.range_single]
      show (c k).trace ⊆ ball (C k) (R k)
      rw [hctrace k]
      exact hrangeD k
  · intro k _
    have hi := (c k).integrable_toSpanSingleton_of_continuousOn hfc (htrace_sub k)
    rw [cycle_integral_single, NlsGge.Atomic.ContourChain.Chain.integral_eq_curveIntegral hi,
      hcpath k, G2037B2Aux.complexForm_eq_toSpanSingleton (finiteGapDifferential u S)]
    exact hD0 k

end
end NlsGge.GKDefinitionDesign
