import Mathlib
import NlsGge.Atomic.G1.G1083Host
import NlsGge.Atomic.G1.G1083Sup1
import NlsGge.Atomic.G1.G1083Sup2
import NlsGge.Atomic.G1.G1084
import NlsGge.Atomic.G1.G1102
import NlsGge.Atomic.G1.G1082Sup5
import NlsGge.Atomic.G1.G1082Sup6

                                                                                                                                    
                                                                              
                                                                                                                                       
                                                                                                                                         
                                                                                                                                      
                                                                                                                                             
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.Atomic.G1083Sup1
noncomputable section
open Set Filter Topology

variable {g v N D : ℝ → ℝ} {lo hi : ℝ}

theorem OscSetup.v_eq_zero_of_lo (h : OscSetup g v N D lo hi) {t : ℝ} (hg : g t = lo) : v t = 0 := by
  have := h.hen t
  rw [hg, h.hlo0] at this
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (by linarith)

theorem OscSetup.v_eq_zero_of_hi (h : OscSetup g v N D lo hi) {t : ℝ} (hg : g t = hi) : v t = 0 := by
  have := h.hen t
  rw [hg, h.hhi0] at this
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (by linarith)

/-- right after any time the orbit is strictly inside the gap -/
theorem OscSetup.eventually_interior (h : OscSetup g v N D lo hi) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), lo < g t ∧ g t < hi := by
  have hc : ContinuousAt g 0 := h.cont_g.continuousAt
  have hrng := h.hrng 0
  rcases hrng.1.eq_or_lt with h1 | h1
  · have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), g t < hi := hc.eventually (gt_mem_nhds (by rw [← h1]; exact h.lt))
    have hpos := h.after_lo h1.symm (h.v_eq_zero_of_lo h1.symm)
    obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hpos
    filter_upwards [Ioo_mem_nhdsGT hε, hlt.filter_mono nhdsWithin_le_nhds] with t ht ht2
    refine ⟨?_, ht2⟩
    have hmono : StrictMonoOn g (Icc 0 t) :=
      strictMonoOn_of_deriv_pos (convex_Icc 0 t) h.cont_g.continuousOn (fun x hx => by
        rw [interior_Icc] at hx
        rw [(h.hg x).deriv]; exact hsub ⟨hx.1, lt_trans hx.2 ht.2⟩)
    have := hmono (Set.mem_Icc.2 ⟨le_rfl, ht.1.le⟩) (Set.mem_Icc.2 ⟨ht.1.le, le_rfl⟩) ht.1
    rw [← h1] at this
    exact this
  · rcases hrng.2.eq_or_lt with h2 | h2
    · have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), lo < g t := hc.eventually (lt_mem_nhds (by rw [h2]; exact h.lt))
      have hneg := h.after_hi h2 (h.v_eq_zero_of_hi h2)
      obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hneg
      filter_upwards [Ioo_mem_nhdsGT hε, hlt.filter_mono nhdsWithin_le_nhds] with t ht ht2
      refine ⟨ht2, ?_⟩
      have hanti : StrictAntiOn g (Icc 0 t) :=
        strictAntiOn_of_deriv_neg (convex_Icc 0 t) h.cont_g.continuousOn (fun x hx => by
          rw [interior_Icc] at hx
          rw [(h.hg x).deriv]; exact hsub ⟨hx.1, lt_trans hx.2 ht.2⟩)
      have := hanti (Set.mem_Icc.2 ⟨le_rfl, ht.1.le⟩) (Set.mem_Icc.2 ⟨ht.1.le, le_rfl⟩) ht.1
      rw [h2] at this
      exact this
    · have e1 : ∀ᶠ t in 𝓝 (0 : ℝ), lo < g t := hc.eventually (lt_mem_nhds h1)
      have e2 : ∀ᶠ t in 𝓝 (0 : ℝ), g t < hi := hc.eventually (gt_mem_nhds h2)
      exact (e1.and e2).filter_mono nhdsWithin_le_nhds

end
end NlsGge.Atomic.G1083Sup1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem eventually_interior_flow (n : ℤ) (w : PhysicalL2)
    (ho : actualGapLowerAllE02_38 w n < actualGapUpperAllE02_38 w n) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), actualGapLowerAllE02_38 w n < gkMu (singleGapFlow n t w) n ∧
      gkMu (singleGapFlow n t w) n < actualGapUpperAllE02_38 w n :=
  (NlsGge.Atomic.G1083Sup2.oscSetup_flow n w ho).eventually_interior

theorem G1_085 (u : PhysicalL2) :
    Dense {v : {v : PhysicalL2 // v ∈ isospectralSet u} |
      ∀ n : ℤ, actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n →
        actualGapLowerAllE02_38 u n < gkMu v.1 n ∧
        gkMu v.1 n < actualGapUpperAllE02_38 u n} := by
  have hK : IsCompact (isospectralSet u) := (G1_080 u).1
  haveI : CompactSpace {v : PhysicalL2 // v ∈ isospectralSet u} := isCompact_iff_compactSpace.mp hK
  let f : ℤ → Set {v : PhysicalL2 // v ∈ isospectralSet u} := fun n =>
    {v | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n →
      actualGapLowerAllE02_38 u n < gkMu v.1 n ∧ gkMu v.1 n < actualGapUpperAllE02_38 u n}
  have hcont : ∀ n, Continuous (fun v : {v : PhysicalL2 // v ∈ isospectralSet u} => gkMu v.1 n) := fun n =>
    (continuousOn_univ.mp (analyticOnNhd_gkMu38 n).continuousOn).comp continuous_subtype_val
  have hopen : ∀ n, IsOpen (f n) := by
    intro n
    by_cases ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n
    · have : f n = (fun v : {v : PhysicalL2 // v ∈ isospectralSet u} => gkMu v.1 n) ⁻¹'
          Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
        ext v; simp [f, ho]
      rw [this]; exact isOpen_Ioo.preimage (hcont n)
    · have : f n = univ := by ext v; simp [f, ho]
      rw [this]; exact isOpen_univ
  have hdense : ∀ n, Dense (f n) := by
    intro n
    rw [dense_iff_inter_open]
    intro U hU ⟨v, hvU⟩
    by_cases ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n
    · let φ : ℝ → {v : PhysicalL2 // v ∈ isospectralSet u} := fun t =>
        ⟨singleGapFlow n t v.1, isospectral_trans' v.2 (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n t v.1)⟩
      have hφ : Continuous φ :=
        Continuous.subtype_mk (NlsGge.Atomic.G1082Sup6.continuous_flow n v.1) _
      have hφ0 : φ 0 = v := Subtype.ext (NlsGge.Atomic.G1081Sup5.singleGapFlow_zero n v.1)
      have hUn : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ U := hφ.continuousAt.eventually (by
        rw [hφ0]; exact hU.mem_nhds hvU)
      have hho : actualGapLowerAllE02_38 v.1 n < actualGapUpperAllE02_38 v.1 n := by
        rw [isospectral_gapLower_eq v.2 n, isospectral_gapUpper_eq v.2 n]; exact ho
      have hint := eventually_interior_flow n v.1 hho
      rw [isospectral_gapLower_eq v.2 n, isospectral_gapUpper_eq v.2 n] at hint
      obtain ⟨t, ht1, ht2⟩ := ((hUn.filter_mono nhdsWithin_le_nhds).and hint).exists
      exact ⟨φ t, ht1, fun _ => ht2⟩
    · exact ⟨v, hvU, fun h => absurd h ho⟩
  have := dense_iInter_of_isOpen hopen hdense
  convert this using 1
  ext v
  simp [f]

end
end NlsGge.GKDefinitionDesign
