import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G2.G2070
import NlsGge.GK38.AbelianFixedGapCube
import NlsGge.GK38.IsolatingDefs

                                                                                                          
                                         
                                                                                                                        
                                                                                
                                                                                                 
                                                                                                            
                                                                                                           
                                                                                                     
                                                                                                                   
                                                                                                                       
                                                  
                                                                                                              
                                                                                                    
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def normalizedRoot (n m : ℤ) (φ : PotPair) : ℂ :=
  if h : m ≠ n then countingCenter38 m + sourceF n φ (⟨m, h⟩ : P2Index38 n)
  else tauN φ n

namespace G2071S1

/-- Conjuncts 1-5 of the G2_071 head, from the landed X-006 family. -/
theorem structural :
    IsOpen sourceW ∧ Set.range realSlice ⊆ sourceW ∧ sourceW ⊆ gkW ∧
    (∀ n : ℤ, AnalyticOnNhd ℂ (sourceF n) sourceW) ∧
    (∀ n : ℤ, ∀ φ ∈ sourceW, p2Fn38 n (φ, sourceF n φ) = 0) :=
  ⟨sourceFamily.W_open, sourceFamily.W_real, sourceFamily.W_gk, sourceFamily.F_analytic,
    fun n φ hφ => sourceFamily.F_zero n φ hφ⟩

theorem coord_sub_norm_le {n : ℤ} (x y : P2Space38 n) (m : P2Index38 n) :
    ‖x m - y m‖ ≤ ‖x - y‖ := by
  have h := lp.norm_apply_le_norm (p := (2 : ENNReal)) (by norm_num) (x - y) m
  simpa using h

/-- Uniform inverse bound over a family, from the landed G2-070 perturbation lemma. -/
theorem uniform_inverse_family {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (Q : ι → E ≃L[ℂ] E) (δ : ι → E →L[ℂ] E) (B : ℝ) (hB : 0 < B)
    (hQ : ∀ i, ‖(Q i).symm.toContinuousLinearMap‖ ≤ B)
    (hδ : ∀ i, ‖δ i‖ ≤ 1 / (2 * B)) (i : ι) :
    ∃ R : E →L[ℂ] E, R * ((Q i).toContinuousLinearMap + δ i) = 1 ∧
      ((Q i).toContinuousLinearMap + δ i) * R = 1 ∧ ‖R‖ ≤ 2 * B := by
  have hB0 : B ≠ 0 := hB.ne'
  have hprod : ‖(Q i).symm.toContinuousLinearMap‖ * ‖δ i‖ ≤ 1 / 2 := by
    calc ‖(Q i).symm.toContinuousLinearMap‖ * ‖δ i‖ ≤ B * (1 / (2 * B)) :=
          mul_le_mul (hQ i) (hδ i) (norm_nonneg _) hB.le
      _ = 1 / 2 := by field_simp
  obtain ⟨R, h1, h2, h3⟩ := NlsGge.Atomic.G2.inverse_perturbation_half (Q i) (δ i) hprod
  exact ⟨R, h1, h2, h3.trans (by linarith [hQ i])⟩

/-- Margin predicate: perturbations of size below eta of the gap segment of index m stay in its disc. -/
def MarginOK (C : ℤ → ℂ) (R : ℤ → ℝ) (u : PhysicalL2) (m : ℤ) (η : ℝ) : Prop :=
  ∀ z ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m),
    ∀ w : ℂ, dist w z < η → w ∈ Metric.ball (C m) (R m)

/-- One radius for all indices: uses compactness for finitely many indices and the summable
gap envelope with the isolating geometry for the tail. -/
theorem uniform_margin (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ η : ℝ, 0 < η ∧ ∀ m : ℤ, MarginOK C R u m η := by
  obtain ⟨c, N, hgeo, hspec⟩ := hfam
  have hA : ∀ m : ℤ, ∀ᶠ η in 𝓝[>] (0 : ℝ), MarginOK C R u m η := by
    intro m
    obtain ⟨δ, hδ, hsub⟩ :=
      (p5Complex_segment_isCompact38 (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)).exists_thickening_subset_open
        (Metric.isOpen_ball (x := C m) (ε := R m)) (hspec.1 m).1
    filter_upwards [Ioo_mem_nhdsGT hδ] with η hη
    unfold MarginOK
    intro z hz w hw
    exact hsub (mem_thickening_iff.2 ⟨z, hz, hw.trans hη.2⟩)
  have hsum : Summable (fun m : ℤ => p5GapEnvelope38 u m ^ 2) := p5GapEnvelope_summable38 u
  have hpos : (0 : ℝ) < (Real.pi / 16) ^ 2 := by positivity
  have hsmall : ∀ᶠ m in cofinite, p5GapEnvelope38 u m ^ 2 < (Real.pi / 16) ^ 2 :=
    hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
  have hbig : {m : ℤ | ¬ (p5GapEnvelope38 u m ^ 2 < (Real.pi / 16) ^ 2)}.Finite :=
    Filter.eventually_cofinite.1 hsmall
  have hnear : {m : ℤ | |m| ≤ (N : ℤ)}.Finite :=
    (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset (fun m hm => abs_le.1 hm)
  have hS : {m : ℤ | ¬ ((N : ℤ) < |m| ∧ p5GapEnvelope38 u m ^ 2 < (Real.pi / 16) ^ 2)}.Finite := by
    refine (hnear.union hbig).subset ?_
    intro m hm
    by_cases h1 : |m| ≤ (N : ℤ)
    · exact Or.inl h1
    · exact Or.inr (fun h2 => hm ⟨not_le.mp h1, h2⟩)
  have hfin : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ m ∈ {m : ℤ | ¬ ((N : ℤ) < |m| ∧
      p5GapEnvelope38 u m ^ 2 < (Real.pi / 16) ^ 2)}, MarginOK C R u m η :=
    (hS.eventually_all).2 (fun m _ => hA m)
  have hI0 : Set.Ioo (0 : ℝ) (Real.pi / 32) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  have hI : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioo (0 : ℝ) (Real.pi / 32) := hI0
  obtain ⟨η, hηS, hηI⟩ := (hfin.and hI).exists
  refine ⟨η, hηI.1, fun m => ?_⟩
  by_cases hm : (N : ℤ) < |m| ∧ p5GapEnvelope38 u m ^ 2 < (Real.pi / 16) ^ 2
  · obtain ⟨h1, h2⟩ := hm
    have hgm := hgeo.2.2.2.2 m h1
    have h0 : 0 ≤ p5GapEnvelope38 u m := by unfold p5GapEnvelope38; positivity
    have henv : p5GapEnvelope38 u m < Real.pi / 16 := by nlinarith [Real.pi_pos]
    have ha : lamMinus (realSlice u) m ∈ closedBall (countingCenter38 m) (p5GapEnvelope38 u m) := by
      rw [mem_closedBall, dist_eq_norm]; exact le_add_of_nonneg_right (norm_nonneg _)
    have hb : lamPlus (realSlice u) m ∈ closedBall (countingCenter38 m) (p5GapEnvelope38 u m) := by
      rw [mem_closedBall, dist_eq_norm]; exact le_add_of_nonneg_left (norm_nonneg _)
    unfold MarginOK
    intro z hz w hw
    have hzc : dist z (countingCenter38 m) ≤ p5GapEnvelope38 u m :=
      mem_closedBall.1 ((convex_closedBall _ _).segment_subset ha hb hz)
    rw [hgm.1, hgm.2.1, Metric.mem_ball]
    have htri := dist_triangle w z (countingCenter38 m)
    linarith [hηI.2, Real.pi_pos]
  · exact hηS m hm

/-- Conjunct 6 of G2_071, from the real base point (t, ht, heq; the G2_064 conjunct-2 content)
and the uniform l2-closeness premise hUnif. -/
theorem conj6_of_uniform_closeness (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (t : ∀ n : ℤ, P3RealSpace38 n)
    (ht : ∀ n : ℤ, t n ∈ p5RealGapCube38 n u)
    (heq : ∀ n : ℤ, sourceF n (realSlice u) = p3RealInclude38 n (t n))
    (hUnif : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ φ ∈ Metric.ball (realSlice u) ε, ∀ n : ℤ,
      ‖sourceF n φ - sourceF n (realSlice u)‖ < η) :
    ∃ V : Set PotPair, IsOpen V ∧ realSlice u ∈ V ∧ V ⊆ sourceW ∧
      ∀ φ ∈ V, ∀ n : ℤ, ∀ m : P2Index38 n,
        normalizedRoot n m.1 φ ∈ Metric.ball (C m.1) (R m.1) := by
  obtain ⟨η, hη, hmarg⟩ := uniform_margin u C R hfam
  obtain ⟨ε, hε, hclose⟩ := hUnif η hη
  have hW : realSlice u ∈ sourceW := sourceFamily.W_real (Set.mem_range_self u)
  refine ⟨Metric.ball (realSlice u) ε ∩ sourceW, Metric.isOpen_ball.inter structural.1,
    ⟨Metric.mem_ball_self hε, hW⟩, Set.inter_subset_right, ?_⟩
  rintro φ ⟨hφ, -⟩ n mm
  rw [normalizedRoot, dif_pos mm.2]
  show countingCenter38 mm.1 + sourceF n φ mm ∈ Metric.ball (C mm.1) (R mm.1)
  have hbase : sourceF n (realSlice u) mm = ((t n mm : ℝ) : ℂ) := by
    rw [heq n, p3RealInclude_apply38]
  have hz : countingCenter38 mm.1 + ((t n mm : ℝ) : ℂ) ∈
      segment ℝ (lamMinus (realSlice u) mm.1) (lamPlus (realSlice u) mm.1) := ht n mm
  have hc := coord_sub_norm_le (sourceF n φ) (sourceF n (realSlice u)) mm
  rw [hbase] at hc
  have e : countingCenter38 mm.1 + sourceF n φ mm - (countingCenter38 mm.1 + ((t n mm : ℝ) : ℂ))
      = sourceF n φ mm - ((t n mm : ℝ) : ℂ) := by ring
  refine hmarg mm.1 _ hz _ ?_
  rw [dist_eq_norm, e]
  exact lt_of_le_of_lt hc (hclose φ hφ n)

end G2071S1
end
end NlsGge.GKDefinitionDesign
