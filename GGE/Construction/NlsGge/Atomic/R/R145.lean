                                                                                                                    
                                                                                                                                                 
import NlsGge.Birkhoff.W11Equivalence38f

                                                                                                   
                                                                                                              
                                                                                                    
set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.R
noncomputable section

def H2BoundedInProbability
    (νN : ℕ → Measure PhysicalL2) : Prop :=
  Tendsto
    (fun R : ℝ =>
      Filter.limsup
        (fun N : ℕ => νN N (NlsGge.Birkhoff.h2Tail38 R)) atTop)
    atTop (𝓝 (0 : ℝ≥0∞))

def chiR (χ : ℝ → ℝ) (R : ℝ) (u : PhysicalL2) : ℝ :=
  NlsGge.Birkhoff.chiR38 χ R u

namespace R145Aux

theorem chiR38_eq_ite (χ : ℝ → ℝ) {R : ℝ} (hR : 0 < R) (u : PhysicalL2) :
    NlsGge.Birkhoff.chiR38 χ R u =
      if NlsGge.Birkhoff.h2SqENN38 u = ⊤ then 0
      else (fun t : ℝ => χ (max t 0)) (Real.sqrt (NlsGge.Birkhoff.h2SqENN38 u).toReal / R) := by
  classical
  by_cases h : NlsGge.Birkhoff.h2SqENN38 u = ⊤
  · have hnm : ¬ (NlsGge.Birkhoff.fourierSeq38 u ∈
        seqSobolev38 (((1 + 1 : ℕ)) : ℝ)) := fun hm => by
      have := NlsGge.Birkhoff.h2SqENN38_of_mem u hm
      rw [h] at this
      exact ENNReal.top_ne_ofReal this
    unfold NlsGge.Birkhoff.chiR38
    rw [dif_neg hnm, if_pos h]
  · have hm := NlsGge.Birkhoff.mem_of_h2SqENN38_ne_top u h
    have hsq := NlsGge.Birkhoff.h2SqENN38_of_mem u hm
    have hnr : Real.sqrt (NlsGge.Birkhoff.h2SqENN38 u).toReal =
        ‖carrierMk38 (((1 + 1 : ℕ)) : ℝ) (NlsGge.Birkhoff.fourierSeq38 u) hm‖ := by
      rw [hsq, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have hnn : 0 ≤ Real.sqrt (NlsGge.Birkhoff.h2SqENN38 u).toReal / R :=
      div_nonneg (Real.sqrt_nonneg _) hR.le
    simp only [NlsGge.Birkhoff.chiR38, hm, dif_pos, h, if_false]
    rw [hnr] at hnn ⊢
    rw [max_eq_left hnn]

end R145Aux

open R145Aux

theorem measurable_chiR
    (χ : ℝ → ℝ) (hχ : NlsGge.Birkhoff.CutoffProfile38 χ)
    (R : ℝ) (hR : 0 < R) :
    Measurable (chiR χ R) := by
  classical
  have hc : Continuous (fun t : ℝ => χ (max t 0)) :=
    hχ.continuousOn.comp_continuous (continuous_id.max continuous_const)
      (fun t => le_max_right t 0)
  have hm : Measurable (fun u : PhysicalL2 =>
      (fun t : ℝ => χ (max t 0)) (Real.sqrt (NlsGge.Birkhoff.h2SqENN38 u).toReal / R)) :=
    hc.measurable.comp
      (NlsGge.Birkhoff.measurable_h2SqENN38.ennreal_toReal.sqrt.div_const R)
  have hs : MeasurableSet {u : PhysicalL2 | NlsGge.Birkhoff.h2SqENN38 u = ⊤} :=
    NlsGge.Birkhoff.measurable_h2SqENN38 (measurableSet_singleton ⊤)
  have : chiR χ R = fun u => if NlsGge.Birkhoff.h2SqENN38 u = ⊤ then 0
      else (fun t : ℝ => χ (max t 0)) (Real.sqrt (NlsGge.Birkhoff.h2SqENN38 u).toReal / R) := by
    funext u; exact chiR38_eq_ite χ hR u
  rw [this]
  exact Measurable.ite hs measurable_const hm

theorem integrable_chiR
    (ρ : Measure PhysicalL2) [IsProbabilityMeasure ρ]
    (χ : ℝ → ℝ) (hχ : NlsGge.Birkhoff.CutoffProfile38 χ)
    (R : ℝ) (hR : 0 < R) :
    Integrable (chiR χ R) ρ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_chiR χ hχ R hR).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have h := NlsGge.Birkhoff.chiR38_mem_Icc hχ hR u
  show ‖NlsGge.Birkhoff.chiR38 χ R u‖ ≤ 1
  rw [Real.norm_of_nonneg h.1]
  exact h.2

theorem cutoff_mass_of_H2_tight
    (νN : ℕ → Measure PhysicalL2)
    [∀ N : ℕ, IsProbabilityMeasure (νN N)]
    (χ : ℝ → ℝ)
    (hχ : NlsGge.Birkhoff.CutoffProfile38 χ)
    (ht : H2BoundedInProbability νN)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    ∃ R : ℝ, 0 < R ∧
      1 - ε ≤ Filter.liminf
        (fun N : ℕ => ∫ u, chiR χ R u ∂(νN N)) atTop := by
  have hev := ht.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.2 hε.1))
  obtain ⟨R, hRg, hR⟩ := (hev.and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨R, hR, ?_⟩
  have hN : ∀ᶠ N : ℕ in atTop, νN N (NlsGge.Birkhoff.h2Tail38 R) < ENNReal.ofReal ε :=
    eventually_lt_of_limsup_lt hRg
  have hbd : IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => ∫ u, chiR χ R u ∂(νN N)) := by
    refine ⟨1, Filter.eventually_map.2 (Filter.Eventually.of_forall fun N => ?_)⟩
    have hint := integrable_chiR (νN N) χ hχ R hR
    calc ∫ u, chiR χ R u ∂(νN N) ≤ ∫ _u, (1 : ℝ) ∂(νN N) :=
          integral_mono hint (integrable_const 1)
            (fun u => (NlsGge.Birkhoff.chiR38_mem_Icc hχ hR u).2)
      _ = 1 := by simp
  refine le_liminf_of_le hbd.isCoboundedUnder_flip ?_
  filter_upwards [hN] with N hNt
  exact NlsGge.Birkhoff.one_sub_le_integral_chiR_W11 hχ hR (integrable_chiR (νN N) χ hχ R hR)
    hε.1.le hNt.le


end
end NlsGge.ThirdConsultation.R
