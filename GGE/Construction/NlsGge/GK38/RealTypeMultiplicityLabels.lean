import NlsGge.GK38.RealTypeMultiplicityCounting

/-! # S6: counted real critical witnesses identify the existing canonical labels

GK I.6 Lemma 6.5 and I.7. No critical reality or simplicity is assumed.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem real_cast_sequence_lex_mono38 (ν : ℤ → ℝ) (hν : StrictMono ν) :
    ∀ i j : ℤ, i ≤ j → complexLexLE38 (ν i : ℂ) (ν j : ℂ) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact complexLexLE_refl38 _
  · exact complexLexLE_of_re_lt38 (by simpa only [Complex.ofReal_re] using hν hlt)

theorem gap_critical_label_alignment38 (u : PhysicalL2) (N : ℕ) (ν : ℤ → ℝ)
    (hd : RootCountingAt38 (deriv (discrim (realSlice u))) 1 N) (hν : StrictMono ν)
    (hc : (Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map (fun n => (ν n : ℂ)) =
      Lib.zeroMultiset (deriv (discrim (realSlice u))) (ball (0 : ℂ) (countingRadius38 N)))
    (hf : ∀ n : ℤ, (N : ℤ) < |n| → ({(ν n : ℂ)} : Multiset ℂ) =
      Lib.zeroMultiset (deriv (discrim (realSlice u))) (ball (countingCenter38 n) (Real.pi / 4))) :
    ∀ n : ℤ, lamDot (realSlice u) n = (ν n : ℂ) := by
  rw [lamDot_eq_candidate38 _ hd]
  intro n
  by_cases hn : |n| ≤ (N : ℤ)
  · exact integerWindow_unique38 _ _ (fun _ _ hij => criticalCandidate_mono38 hd hij)
      (real_cast_sequence_lex_mono38 ν hν) _ _
      ((criticalCandidate_central_multiset38 hd).trans hc.symm) (abs_le.mp hn)
  · exact Multiset.singleton_inj.mp
      ((criticalCandidate_small_multiset38 hd (lt_of_not_ge hn)).trans (hf n (lt_of_not_ge hn)).symm)

theorem gap_critical_labels38 (u : PhysicalL2) : ∃ ν : ℤ → ℝ, StrictMono ν ∧
    ∀ n : ℤ, lamDot (realSlice u) n = (ν n : ℂ) ∧
      ν n ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ∧
      deriv (discrim (realSlice u)) (ν n : ℂ) = 0 ∧
      analyticOrderAt (deriv (discrim (realSlice u))) (ν n : ℂ) = 1 := by
  obtain ⟨ν, hv⟩ := gap_critical_witnesses38 u
  obtain ⟨N, hp, hd⟩ := exists_simultaneous_cutoff38 (realSlice u)
  obtain ⟨hmono, hc, hf⟩ := gap_critical_localization38 u N ν hp hd hv
  have hi : Function.Injective (fun n => (ν n : ℂ)) := Complex.ofReal_injective.comp hmono.injective
  have hs := critical_central_saturation38 _ N (fun n => (ν n : ℂ)) hd hi
    (fun n hn => ⟨hc n (abs_le.mpr (Finset.mem_Icc.mp hn)), (hv n).2⟩)
  have hfar := critical_far_saturation38 _ N (fun n => (ν n : ℂ)) hd
    (fun n hn => ⟨hf n hn, (hv n).2⟩)
  have he := gap_critical_label_alignment38 u N ν hd hmono hs.1 (fun n hn => (hfar n hn).1)
  refine ⟨ν, hmono, fun n => ⟨he n, (hv n).1, (hv n).2, ?_⟩⟩
  by_cases hn : |n| ≤ (N : ℤ)
  · exact hs.2 n (Finset.mem_Icc.mpr (abs_le.mp hn))
  · exact (hfar n (lt_of_not_ge hn)).2

theorem lamDot_between (u : PhysicalL2) (n : ℤ) :
    (lamDot (realSlice u) n).im = 0 ∧
    actualGapLowerAllE02_38 u n ≤ (lamDot (realSlice u) n).re ∧
    (lamDot (realSlice u) n).re ≤ actualGapUpperAllE02_38 u n := by
  obtain ⟨ν, _, hv⟩ := gap_critical_labels38 u
  rw [(hv n).1]
  exact ⟨Complex.ofReal_im _, by simpa only [Complex.ofReal_re, mem_Icc] using (hv n).2.1⟩

theorem lamDot_realWitness38 (u : PhysicalL2) (n : ℤ) :
    ∃ x : ℝ, lamDot (realSlice u) n = (x : ℂ) ∧
      x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
  obtain ⟨ν, _, hv⟩ := gap_critical_labels38 u
  exact ⟨ν n, (hv n).1, (hv n).2.1⟩

theorem lamDot_simple38 (u : PhysicalL2) (n : ℤ) :
    analyticOrderAt (deriv (discrim (realSlice u))) (lamDot (realSlice u) n) = 1 := by
  obtain ⟨ν, _, hv⟩ := gap_critical_labels38 u
  rw [(hv n).1]
  exact (hv n).2.2.2

theorem discrimDeriv_real_root38 (u : PhysicalL2) (z : ℂ)
    (hz : deriv (discrim (realSlice u)) z = 0) : z.im = 0 := by
  obtain ⟨n, hn⟩ := ((lamDot_enumeration38 (realSlice u)).2.1 z).mp hz
  rw [← hn]
  exact (lamDot_between u n).1

theorem gap_critical_unique38 (u : PhysicalL2) (n : ℤ) :
    ∃! x : ℝ, x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ∧
      deriv (discrim (realSlice u)) (x : ℂ) = 0 := by
  obtain ⟨ν, _, hv⟩ := gap_critical_labels38 u
  refine ⟨ν n, ⟨(hv n).2.1, (hv n).2.2.1⟩, ?_⟩
  intro x hx
  obtain ⟨m, hm⟩ := ((lamDot_enumeration38 (realSlice u)).2.1 (x : ℂ)).mp hx.2
  have he : ν m = x := Complex.ofReal_injective ((hv m).1.symm.trans hm)
  have hmn : m = n := gap_interval_index_unique38 u (hv m).2.1 (he ▸ hx.1)
  simpa only [hmn] using he.symm

theorem lamDot_between_open38 (u : PhysicalL2) (n : ℤ)
    (ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) :
    actualGapLowerAllE02_38 u n < (lamDot (realSlice u) n).re ∧
    (lamDot (realSlice u) n).re < actualGapUpperAllE02_38 u n := by
  obtain ⟨ν, _, hv⟩ := gap_critical_labels38 u
  have hl := perChar_order_one_noncritical38 _ _ (gap_endpoint_roots38 u n).1
    (by simpa only [ho, ite_true] using order_at_gapEnd u n)
  have hu := perChar_order_one_noncritical38 _ _ (gap_endpoint_roots38 u n).2
    (by simpa only [ho, ite_true] using order_at_gapUpper38 u n)
  have hnl : ν n ≠ actualGapLowerAllE02_38 u n := by
    intro he; exact hl (by simpa only [he] using (hv n).2.2.1)
  have hnu : ν n ≠ actualGapUpperAllE02_38 u n := by
    intro he; exact hu (by simpa only [he] using (hv n).2.2.1)
  rw [(hv n).1, Complex.ofReal_re]
  exact ⟨lt_of_le_of_ne (hv n).2.1.1 hnl.symm, lt_of_le_of_ne (hv n).2.1.2 hnu⟩

theorem lamDot_eq_closedGap38 (u : PhysicalL2) (n : ℤ)
    (hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n) :
    lamDot (realSlice u) n = (actualGapLowerAllE02_38 u n : ℂ) := by
  obtain ⟨x, he, hx⟩ := lamDot_realWitness38 u n
  have hx' : x = actualGapLowerAllE02_38 u n := le_antisymm (by simpa only [← hc] using hx.2) hx.1
  simpa only [hx'] using he

end
end NlsGge.GK38
