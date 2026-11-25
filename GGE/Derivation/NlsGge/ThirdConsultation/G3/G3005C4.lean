import Mathlib
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import NlsGge.ThirdConsultation.G3.G3005UpperHost
import NlsGge.ThirdConsultation.G3.G3005C4Topology
import NlsGge.ThirdConsultation.G3.G3005C4Support
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.DirichletRealBridge

/- G3-005 C4 (proof development, AUTHOR; not self-reviewed). Target NlsGge/ThirdConsultation/G3/G3005C4.lean (proposed).
   Conjunct 4 of Pro round 9 sec. 9 G3_005 (statement verbatim): Nonempty (UpperStartPath m phi) under gap <> 0.
   See G3005C4Support (line/hgt helpers) and G3005C4Topology (sheet_limit, ext_left, ext_right). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38
open NlsGge.GKDefinitionDesign.G3005C4

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3005_c4_nonempty (m : ℤ) (φ : SourcePotential) (hgap : gap φ.1 m ≠ 0) :
    Nonempty (UpperStartPath m φ) := by
  have hgk : φ.1 ∈ gkW := sourceFamily.W_gk φ.2
  obtain ⟨c0, N0, hg0, hspec⟩ := isolating_family38 φ.1 hgk
  have hiso : IsolatingFamily38 φ.1 (discC φ.1) (discR φ.1) := ⟨c0, N0, hg0, hspec⟩
  have hγ : lamPlus φ.1 m - lamMinus φ.1 m ≠ 0 := hgap
  have hbB : lamPlus φ.1 m ∈ ball (discC φ.1 m) (discR φ.1 m) :=
    (hspec.1 m).1 (right_mem_segment ℝ _ _)
  have hμB : muSeq φ.1 m ∈ ball (discC φ.1 m) (discR φ.1 m) := (hspec.1 m).2.1
  have hpb : perChar φ.1 (lamPlus φ.1 m) = 0 := (lamSeq_enumeration38 φ.1).1 (2 * m + 1)
  have hμr : perChar φ.1 (muSeq φ.1 m) = antiDiscrim φ.1 (muSeq φ.1 m) ^ 2 :=
    dirichlet_perChar_eq_anti_sq38 φ.1 _ (muSeq_root38 φ.1 m)
  -- the auxiliary points
  obtain ⟨η, hη, hcB⟩ := exists_small (lamPlus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) _
    isOpen_ball hbB
  generalize hc : lamPlus φ.1 m + (η : ℂ) * (lamPlus φ.1 m - lamMinus φ.1 m) = c at hcB
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = if 0 ≤ hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m)
      (muSeq φ.1 m) then 1 else -1 := ⟨_, rfl⟩
  obtain ⟨κ, hκ, hpB⟩ := exists_small (muSeq φ.1 m)
    ((σ : ℂ) * Complex.I * (lamPlus φ.1 m - lamMinus φ.1 m)) _ isOpen_ball hμB
  generalize hp : muSeq φ.1 m + (κ : ℂ) * ((σ : ℂ) * Complex.I * (lamPlus φ.1 m - lamMinus φ.1 m)) = p
    at hpB
  -- heights
  have hhc : hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) c = 0 := by
    rw [← hc]; exact hgt_beyond _ _ hγ η
  have hhp : hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) p =
      hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (muSeq φ.1 m) + κ * σ := by
    rw [← hp, hgt_add]
    congr 2
    rw [mul_div_cancel_right₀ _ hγ]
    simp
  have hdir : ∀ t : ℝ, 0 ≤ t → t < 1 →
      hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (line p (muSeq φ.1 m) t) ≠ 0 := by
    intro t ht0 ht1
    rw [hgt_line _ _ _ _ hγ, hhp]
    by_cases h0 : 0 ≤ hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (muSeq φ.1 m)
    · have hs : σ = 1 := by rw [hσ, if_pos h0]
      rw [hs]
      have : 0 < (1 - t) * (hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (muSeq φ.1 m) + κ * 1)
          + t * hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (muSeq φ.1 m) := by
        nlinarith [mul_nonneg ht0 h0, mul_pos (sub_pos.2 ht1) hκ]
      exact this.ne'
    · have hs : σ = -1 := by rw [hσ, if_neg h0]
      rw [hs]
      have h0' : hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (muSeq φ.1 m) < 0 := lt_of_not_ge h0
      have : (1 - t) * (hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (muSeq φ.1 m) + κ * -1)
          + t * hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) (muSeq φ.1 m) < 0 := by
        nlinarith [mul_nonneg ht0 (le_of_lt (neg_pos.2 h0')), mul_pos (sub_pos.2 ht1) hκ]
      exact this.ne
  have hpne : hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) p ≠ 0 := by
    have := hdir 0 le_rfl zero_lt_one
    rwa [line_zero] at this
  -- not on the cut, not on any cut
  have hline1 : ∀ t : ℝ, 0 < t →
      line (lamPlus φ.1 m) c t ∉ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m) := by
    intro t ht
    have e : line (lamPlus φ.1 m) c t =
        lamPlus φ.1 m + ((t * η : ℝ) : ℂ) * (lamPlus φ.1 m - lamMinus φ.1 m) := by
      rw [← hc]; unfold line; push_cast; ring
    rw [e]
    exact notseg_beyond _ _ hγ _ (mul_pos ht hη)
  have hc_notseg : c ∉ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m) := by
    rw [← hc]
    simpa using notseg_beyond _ _ hγ η hη
  have hline2 : ∀ t : ℝ, t ∈ Icc (0:ℝ) 1 →
      line c p t ∉ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, line_zero]; exact hc_notseg
    · apply notseg_of_hgt hγ
      rw [hgt_line _ _ _ _ hγ, hhc]
      have : t * hgt (lamMinus φ.1 m) (lamPlus φ.1 m - lamMinus φ.1 m) p ≠ 0 :=
        mul_ne_zero h0.ne' hpne
      simpa using this
  have hline3 : ∀ t : ℝ, t ∈ Ico (0:ℝ) 1 →
      line p (muSeq φ.1 m) t ∉ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m) :=
    fun t ht => notseg_of_hgt hγ (hdir t ht.1 ht.2)
  have hb1 : ∀ t : ℝ, t ∈ Icc (0:ℝ) 1 → line (lamPlus φ.1 m) c t ∈ ball (discC φ.1 m) (discR φ.1 m) :=
    fun t ht => line_mem_ball hbB hcB t ht
  have hb2 : ∀ t : ℝ, t ∈ Icc (0:ℝ) 1 → line c p t ∈ ball (discC φ.1 m) (discR φ.1 m) :=
    fun t ht => line_mem_ball hcB hpB t ht
  have hb3 : ∀ t : ℝ, t ∈ Icc (0:ℝ) 1 → line p (muSeq φ.1 m) t ∈ ball (discC φ.1 m) (discR φ.1 m) :=
    fun t ht => line_mem_ball hpB hμB t ht
  have hng1 : ∀ t ∈ Ioc (0:ℝ) 1, line (lamPlus φ.1 m) c t ∉ gapSegments38 φ.1 :=
    fun t ht => not_gap φ.1 hgk m _ (hb1 t ⟨ht.1.le, ht.2⟩) (hline1 t ht.1)
  have hng2 : ∀ t ∈ Icc (0:ℝ) 1, line c p t ∉ gapSegments38 φ.1 :=
    fun t ht => not_gap φ.1 hgk m _ (hb2 t ht) (hline2 t ht)
  have hng3 : ∀ t ∈ Ico (0:ℝ) 1, line p (muSeq φ.1 m) t ∉ gapSegments38 φ.1 :=
    fun t ht => not_gap φ.1 hgk m _ (hb3 t ⟨ht.1, ht.2.le⟩) (hline3 t ht)
  -- the global sign from the terminal end
  obtain ⟨e, he, hlim⟩ := sheet_limit (fun t => canonRoot38 φ.1 (line p (muSeq φ.1 m) t))
    (fun t => perChar φ.1 (line p (muSeq φ.1 m) t)) (antiDiscrim φ.1 (muSeq φ.1 m))
    (canon_cont φ.1 hgk _ (line_cont _ _) _ hng3)
    ((perChar_cont φ.1).comp_continuousOn (line_cont _ _).continuousOn)
    (fun t ht => canonRoot_sq38 φ.1 hgk _ (hng3 t ht))
    (by rw [line_one]; exact hμr.symm)
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hsq : ∀ z : ℂ, z ∉ gapSegments38 φ.1 → (e * canonRoot38 φ.1 z) ^ 2 = perChar φ.1 z := by
    intro z hz
    rw [mul_pow, he2, one_mul]
    exact canonRoot_sq38 φ.1 hgk z hz
  -- arc 1: lamPlus -> c
  have hf1c : ContinuousOn (fun t : ℝ => e * canonRoot38 φ.1 (line (lamPlus φ.1 m) c t)) (Ioc 0 1) :=
    continuousOn_const.mul (canon_cont φ.1 hgk _ (line_cont _ _) _ hng1)
  have hf1lim : Tendsto (fun t : ℝ => e * canonRoot38 φ.1 (line (lamPlus φ.1 m) c t)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine sq_tendsto_zero _ (fun t => perChar φ.1 (line (lamPlus φ.1 m) c t)) _ ?_ ?_
    · have h := ((perChar_cont φ.1).comp (line_cont (lamPlus φ.1 m) c)).continuousAt (x := (0:ℝ))
      have h' := h.tendsto
      simp only [Function.comp_apply, line_zero, hpb] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with t ht
      exact hsq _ (hng1 t ⟨ht.1, ht.2.le⟩)
  -- arc 3: p -> mu (terminal limit r)
  have hf3c : ContinuousOn (fun t : ℝ => e * canonRoot38 φ.1 (line p (muSeq φ.1 m) t)) (Ico 0 1) :=
    continuousOn_const.mul (canon_cont φ.1 hgk _ (line_cont _ _) _ hng3)
  let arc1 : GKRootedC1Arc38 (sourceGK φ) m :=
    ⟨(line (lamPlus φ.1 m) c,
      fun t => if t = 0 then 0 else e * canonRoot38 φ.1 (line (lamPlus φ.1 m) c t)),
      (line_cont _ _).continuousOn, (line_contDiff _ _).contDiffOn,
      ext_left _ 0 hf1c hf1lim,
      fun t ht => by
        by_cases h0 : t = 0
        · subst h0
          simp only [if_true, line_zero]
          rw [show (0:ℂ) ^ 2 = 0 by norm_num]
          exact hpb.symm
        · simp only [h0, if_false]
          exact hsq _ (hng1 t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩),
      hb1, fun t ht => ⟨hb1 t ⟨ht.1.le, ht.2.le⟩, hline1 t ht.1⟩⟩
  let arc2 : GKRootedC1Arc38 (sourceGK φ) m :=
    ⟨(line c p, fun t => e * canonRoot38 φ.1 (line c p t)),
      (line_cont _ _).continuousOn, (line_contDiff _ _).contDiffOn,
      continuousOn_const.mul (canon_cont φ.1 hgk _ (line_cont _ _) _ hng2),
      fun t ht => hsq _ (hng2 t ht),
      hb2, fun t ht => ⟨hb2 t ⟨ht.1.le, ht.2.le⟩, hline2 t ⟨ht.1.le, ht.2.le⟩⟩⟩
  let arc3 : GKRootedC1Arc38 (sourceGK φ) m :=
    ⟨(line p (muSeq φ.1 m),
      fun t => if t = 1 then antiDiscrim φ.1 (muSeq φ.1 m)
        else e * canonRoot38 φ.1 (line p (muSeq φ.1 m) t)),
      (line_cont _ _).continuousOn, (line_contDiff _ _).contDiffOn,
      ext_right _ _ hf3c hlim,
      fun t ht => by
        by_cases h1 : t = 1
        · subst h1
          simp only [if_true, line_one]
          exact hμr.symm
        · simp only [h1, if_false]
          exact hsq _ (hng3 t ⟨ht.1, lt_of_le_of_ne ht.2 h1⟩),
      hb3, fun t ht => ⟨hb3 t ⟨ht.1.le, ht.2.le⟩, hline3 t ⟨ht.1.le, ht.2⟩⟩⟩
  refine ⟨⟨(arc1, ([arc2], arc3)), hiso, ?_, ?_, ?_, ?_⟩⟩
  · show (_ ∧ _ ∧ _) ∧ (_ ∧ _ ∧ _) ∧ True
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, trivial⟩
    · show line (lamPlus φ.1 m) c 1 = line c p 0
      rw [line_one, line_zero]
    · show (if (1:ℝ) = 0 then 0 else e * canonRoot38 φ.1 (line (lamPlus φ.1 m) c 1)) =
        e * canonRoot38 φ.1 (line c p 0)
      rw [line_one, line_zero]; simp
    · show line (lamPlus φ.1 m) c 1 ∈ GKOriginalSlit38 (sourceGK φ) m
      rw [line_one]; exact ⟨hcB, hc_notseg⟩
    · show line c p 1 = line p (muSeq φ.1 m) 0
      rw [line_one, line_zero]
    · show e * canonRoot38 φ.1 (line c p 1) =
        (if (0:ℝ) = 1 then antiDiscrim φ.1 (muSeq φ.1 m)
          else e * canonRoot38 φ.1 (line p (muSeq φ.1 m) 0))
      rw [line_one, line_zero]; simp
    · show line c p 1 ∈ GKOriginalSlit38 (sourceGK φ) m
      rw [line_one]
      exact ⟨hpB, notseg_of_hgt hγ hpne⟩
  · show line (lamPlus φ.1 m) c 0 = lamPlus φ.1 m
    exact line_zero _ _
  · show line p (muSeq φ.1 m) 1 = muSeq φ.1 m
    exact line_one _ _
  · intro _ _
    show (if (1:ℝ) = 1 then antiDiscrim φ.1 (muSeq φ.1 m)
      else e * canonRoot38 φ.1 (line p (muSeq φ.1 m) 1)) = antiDiscrim φ.1 (muSeq φ.1 m)
    simp

end
end NlsGge.GKDefinitionDesign
