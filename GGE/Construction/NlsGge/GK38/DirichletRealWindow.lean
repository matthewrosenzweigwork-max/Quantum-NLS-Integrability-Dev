import NlsGge.GK38.DirichletRealDerivative

/-! Prescribed q=1 Dirichlet counting windows from the actual sine comparison.
Private source anchor: book I.6 counting argument. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_large_counting_cutoff38 (φ₀ : PotPair) (L : ℕ) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, L ≤ N ∧
      ∀ φ ∈ U, RootCountingAt38 (dirichletChar φ) 1 N := by
  obtain ⟨U, hU, R, herr⟩ := dirichletChar_asymp φ₀ (1 / (2 * sineOffDiscsConstant38))
    (one_div_pos.mpr (mul_pos (by norm_num) sineOffDiscsConstant38_pos))
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N := max (K + 1) L
  have hN : 0 < N := lt_of_lt_of_le (Nat.succ_pos K) (le_max_left _ _)
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    have hKN : (K : ℝ) < (N : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self K) (le_max_left _ _)
    unfold countingRadius38
    nlinarith [Real.pi_pos]
  exact ⟨U, hU, N, le_max_right _ _, fun φ hφ =>
    dirichlet_counting_at38 φ N hN (fun z hz hsep =>
      dirichlet_strict_comparison38 (herr φ hφ z (hRN.trans hz)) hsep)⟩

theorem dirichlet_real_fixed_window38 (u₀ : PhysicalL2) (k : ℤ) :
    ∃ U : Set PhysicalL2, U ∈ 𝓝 u₀ ∧ ∃ N : ℕ, 0 < N ∧
      -(N : ℤ) ≤ k ∧ k ≤ (N : ℤ) ∧
      ∀ u ∈ U, RootCountingAt38 (dirichletChar (realSlice u)) 1 N := by
  obtain ⟨V, hV, N, hN, h⟩ :=
    dirichlet_large_counting_cutoff38 (realSlice u₀) (k.natAbs + 1)
  refine ⟨realSlice ⁻¹' V, continuous_realSlice.continuousAt.preimage_mem_nhds hV,
    N, (h _ (mem_of_mem_nhds hV)).1, ?_, ?_, fun u hu => h _ hu⟩
  · have hk : -k ≤ (k.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -k))
    omega
  · have hk : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
    omega

theorem gkMu_injective38 (u : PhysicalL2) : Function.Injective (gkMu u) := by
  intro i j hij
  have h := (muSeq_occurrence38 (realSlice u) (muSeq (realSlice u) i)).2
  rw [muSeq_simple38] at h
  apply (Set.encard_le_one_iff.mp h.le) i j
  · rfl
  · change muSeq (realSlice u) j = muSeq (realSlice u) i
    rw [muSeq_eq_gkMu38, muSeq_eq_gkMu38, hij]

theorem gkMu_strictMono38 (u : PhysicalL2) : StrictMono (gkMu u) := by
  apply Monotone.strictMono_of_injective _ (gkMu_injective38 u)
  intro i j hij
  have h := muSeq_mono38 (realSlice u) hij
  rw [complexLexLE_iff38, muSeq_eq_gkMu38, muSeq_eq_gkMu38] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

end
end NlsGge.GK38
