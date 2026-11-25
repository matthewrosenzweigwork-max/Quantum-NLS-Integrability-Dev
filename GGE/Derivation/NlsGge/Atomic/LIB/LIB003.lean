import NlsGge.Atomic.LIB.LIB001
import NlsGge.Birkhoff.F01Determinant38d

/-! Weighted Fourier truncations on the actual Sobolev sequence carrier. -/

set_option autoImplicit false
noncomputable section

open Filter NlsGge.Birkhoff NlsGge.Pilot NlsGge.Sobolev38 Topology

namespace NlsGge.Atomic.LIB003

/-- A sequence with finite `h^s` square sum belongs to the repository's
actual sequence Sobolev space. -/
theorem weightedSequence_mem_seqSobolev38 (s : ℝ) (u : ℤ → ℂ)
    (hu : Summable (fun n : ℤ => sobolevModeWeight s n * ‖u n‖ ^ 2)) :
    u ∈ seqSobolev38 s := by
  change Memℓp (weightedCoordinates (sobolevModeWeight s) u) 2
  rw [weightedCoordinates_mem_l2_iff (sobolevModeWeight s)
    (fun n => (sobolevModeWeight_pos s n).le) u]
  exact hu

/-- The sequence `(-û(-n))` from LIB-001 has the weighted membership required
to place it in the actual `h^s` carrier. The reflected sign does not change
the coefficient norms. -/
theorem reflectedFourier_mem_seqSobolev38 (s : ℝ) (u : NlsGge.Pilot.PhysicalL2)
    (hu : Summable (fun n : ℤ => sobolevModeWeight s n *
      ‖NlsGge.Atomic.LIB001.reflectedPeriodOneFourierL2 u n‖ ^ 2)) :
    (NlsGge.Atomic.LIB001.reflectedPeriodOneFourierL2 u : ℤ → ℂ) ∈ seqSobolev38 s :=
  weightedSequence_mem_seqSobolev38 s _ hu

/-- Realize a weighted-square-summable sequence in the coherent Sobolev
carrier used by the project. -/
noncomputable def weightedSequenceCarrier38 (s : ℝ) (u : ℤ → ℂ)
    (hu : Summable (fun n : ℤ => sobolevModeWeight s n * ‖u n‖ ^ 2)) :
    SobolevCarrier38 s :=
  carrierMk38 s u (weightedSequence_mem_seqSobolev38 s u hu)

/-- The cutoff acts on sequence coefficients exactly by retaining
`n ∈ symmetricModes N` and setting all other modes to zero. -/
theorem weighted_fourier_truncation_coeff (s : ℝ) (N : ℕ) (u : ℤ → ℂ)
    (hu : Summable (fun n : ℤ => sobolevModeWeight s n * ‖u n‖ ^ 2)) (n : ℤ) :
    carrierCoe38 s (projC38 s N (weightedSequenceCarrier38 s u hu)) n =
      if n ∈ symmetricModes N then u n else 0 := by
  simp [weightedSequenceCarrier38]

/-- Realize the reflected period-one Fourier coefficients from LIB-001 in
the actual Sobolev carrier whenever their weighted square sum is finite. -/
noncomputable def reflectedFourierCarrier38 (s : ℝ) (u : NlsGge.Pilot.PhysicalL2)
    (hu : Summable (fun n : ℤ => sobolevModeWeight s n *
      ‖NlsGge.Atomic.LIB001.reflectedPeriodOneFourierL2 u n‖ ^ 2)) :
    SobolevCarrier38 s :=
  weightedSequenceCarrier38 s (NlsGge.Atomic.LIB001.reflectedPeriodOneFourierL2 u) hu

/-- The symmetric Fourier truncations of every weighted-square-summable
sequence converge in the actual `h^s` norm. The assumption `s ≥ 0` is retained
as in the source contract. -/
theorem weighted_fourier_truncation_tendsto (s : ℝ) (_hs : 0 ≤ s)
    (u : ℤ → ℂ) (hu : Summable (fun n : ℤ => sobolevModeWeight s n * ‖u n‖ ^ 2)) :
    Tendsto (fun N : ℕ => projC38 s N (weightedSequenceCarrier38 s u hu)) atTop
      (𝓝 (weightedSequenceCarrier38 s u hu)) :=
  tendsto_projC38 s (weightedSequenceCarrier38 s u hu)

/-- The `h^s` tail norms of symmetric Fourier truncations tend uniformly to
zero on each compact subset of the actual Sobolev carrier. -/
theorem weighted_tail_uniform_compact (s : ℝ) (_hs : 0 ≤ s)
    {C : Set (SobolevCarrier38 s)} (hC : IsCompact C) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ C, ‖compl38 s N x‖ < ε := by
  have hlip : ∀ (N : ℕ) (x y : SobolevCarrier38 s),
      |‖compl38 s N x‖ - ‖compl38 s N y‖| ≤ dist x y := by
    intro N x y
    calc
      |‖compl38 s N x‖ - ‖compl38 s N y‖| ≤
          ‖compl38 s N x - compl38 s N y‖ := abs_norm_sub_norm_le _ _
      _ = ‖compl38 s N (x - y)‖ := by rw [map_sub]
      _ ≤ ‖x - y‖ := norm_compl38_apply_le s N (x - y)
      _ = dist x y := by rw [dist_eq_norm]
  have hpt : ∀ x : SobolevCarrier38 s,
      Tendsto (fun N : ℕ => ‖compl38 s N x‖) atTop (𝓝 0) := by
    intro x
    simpa using (tendsto_compl38 s x).norm
  have hunif := eventually_abs_lt_of_lipschitz38 hC hlip hpt
  intro ε hε
  filter_upwards [hunif ε hε] with N hN
  intro x hx
  simpa only [abs_of_nonneg (norm_nonneg _)] using hN x hx

end NlsGge.Atomic.LIB003
