import NlsGge.Atomic.DM.DM046

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.DM047

open NlsGge.Atomic.DM046

/-- The logarithmic profile of a positive integer weight. -/
def logProfile (Ω : ℤ → ℝ) (n : ℕ) : ℝ := Real.log (Ω (n : ℤ))

/-- DM's exponentially truncated secondary weight. -/
def secondaryCutoff (Ω : ℤ → ℝ) (ε : ℝ) (k : ℤ) : ℝ :=
  min (Real.exp (ε * (k.natAbs : ℝ))) (Ω k)

private theorem exists_pos_below_finite_values {S : Finset ℕ} (q : ℕ → ℝ)
    (hq : ∀ n ∈ S, 0 < q n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ n ∈ S, ε₀ < q n := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a S ha ih =>
      have hqS : ∀ n ∈ S, 0 < q n := by
        intro n hn
        exact hq n (Finset.mem_insert_of_mem hn)
      obtain ⟨δ, hδ, hδS⟩ := ih hqS
      have hqa : 0 < q a := hq a (Finset.mem_insert_self a S)
      refine ⟨min δ (q a) / 2, by positivity, ?_⟩
      intro n hn
      simp only [Finset.mem_insert] at hn
      rcases hn with hna | hn
      · have hqeq : q n = q a := congrArg q hna
        have hmin : min δ (q a) ≤ q a := min_le_right _ _
        have hlt : min δ (q a) / 2 < q a := by nlinarith
        simpa [hqeq] using hlt
      · have hmin : min δ (q n) ≤ δ := min_le_left _ _
        have hlt : min δ (q a) / 2 < δ := by
          have hmin' : min δ (q a) ≤ δ := min_le_left _ _
          nlinarith
        exact hlt.trans (hδS n hn)

private theorem min_mul_div_of_pos (a b c : ℝ) (hc : 0 < c) :
    min (a * c) b / c = min a (b / c) := by
  by_cases h : a * c ≤ b
  · have h' : a ≤ b / c := (le_div_iff₀ hc).2 (by nlinarith)
    rw [min_eq_left h, min_eq_left h']
    field_simp
  · have h' : b / c < a := by
      rw [div_lt_iff₀ hc]
      exact lt_of_not_ge h
    have hleft : b < a * c := lt_of_not_ge h
    rw [min_eq_right (le_of_lt hleft), min_eq_right (le_of_lt h')]

private theorem exp_min (a b : ℝ) :
    Real.exp (min a b) = min (Real.exp a) (Real.exp b) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (Real.exp_le_exp.mpr h)]
  · have h' : b < a := lt_of_not_ge h
    rw [min_eq_right (le_of_lt h'), min_eq_right (le_of_lt (Real.exp_lt_exp.mpr h'))]

/-- If a normalized monotone submultiplicative weight takes the value one at a
positive index, then it is the constant weight one. -/
theorem weight_eq_one_of_eq_one_at_pos (Ω : ℤ → ℝ)
    (hzero : Ω 0 = 1) (hmono : Monotone (fun n : ℕ => Ω (n : ℤ)))
    (hsub : SubmultiplicativeWeight Ω) {N : ℕ} (hN : 0 < N)
    (hNone : Ω (N : ℤ) = 1) : ∀ n : ℕ, Ω (n : ℤ) = 1 := by
  have hOne : Ω 1 = 1 := by
    have hle : Ω (1 : ℤ) ≤ Ω (N : ℤ) := hmono (show 1 ≤ N by omega)
    rw [hNone] at hle
    have hge : 1 ≤ Ω 1 := by
      simpa [hzero] using hmono (show 0 ≤ 1 by omega)
    exact le_antisymm hle hge
  intro n
  induction n with
  | zero => simpa [hzero]
  | succ n ih =>
      have hs := hsub (n : ℤ) 1
      have hs' : Ω ((n + 1 : ℕ) : ℤ) ≤ Ω (n : ℤ) * Ω 1 := by
        simpa [Nat.cast_add, Int.cast_one] using hs
      have hs'' : Ω ((n + 1 : ℕ) : ℤ) ≤ 1 := by simpa [hOne, ih] using hs'
      have hge : 1 ≤ Ω ((n + 1 : ℕ) : ℤ) := by
        simpa [hzero] using hmono (show 0 ≤ n + 1 by omega)
      exact le_antisymm hs'' hge

theorem secondaryCutoff_eq_one_of_eq_one_profile
    (Ω : ℤ → ℝ)
    (heven : ∀ k, Ω (-k) = Ω k)
    (htrivial : ∀ n : ℕ, Ω (n : ℤ) = 1)
    (ε : ℝ) (hε : 0 < ε) : secondaryCutoff Ω ε = fun _ => 1 := by
  funext k
  simp only [secondaryCutoff]
  have hΩ : Ω k = 1 := by
    cases k with
    | ofNat n => simpa using htrivial n
    | negSucc n =>
        have hn := htrivial (n + 1)
        have hneg : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
        rw [hneg, heven]
        simpa using hn
  rw [hΩ]
  have hexp : 1 ≤ Real.exp (ε * (k.natAbs : ℝ)) := by
    apply Real.one_le_exp_iff.mpr
    positivity
  exact min_eq_right (by exact hexp)

/-- DM Lemma 47, in the exact eventually-antitone log-ratio form.  The cutoff
is submultiplicative for every sufficiently small positive epsilon. -/
theorem dm_secondary_cutoff_submultiplicative
    (Ω : ℤ → ℝ)
    (hzero : Ω 0 = 1)
    (hpos : ∀ k : ℤ, 0 < Ω k)
    (heven : ∀ k : ℤ, Ω (-k) = Ω k)
    (hmono : Monotone (fun n : ℕ => Ω (n : ℤ)))
    (hsub : SubmultiplicativeWeight Ω)
    (hEventually : ∃ N : ℕ, ∀ m n : ℕ+,
      N ≤ (m : ℕ) → (m : ℕ) ≤ (n : ℕ) →
        logProfile Ω n / (n : ℝ) ≤ logProfile Ω m / (m : ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
      SubmultiplicativeWeight (secondaryCutoff Ω ε) := by
  classical
  obtain ⟨N, hN⟩ := hEventually
  let M : ℕ := max N 1
  let q : ℕ → ℝ := fun n => logProfile Ω n / (n : ℝ)
  by_cases htrivial : ∀ n : ℕ, Ω (n : ℤ) = 1
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε
    have hcut : secondaryCutoff Ω ε = fun _ => 1 :=
        secondaryCutoff_eq_one_of_eq_one_profile Ω heven htrivial ε hε.1
    simpa [hcut] using (show SubmultiplicativeWeight (fun _ : ℤ => (1 : ℝ)) by
      intro k l
      norm_num [SubmultiplicativeWeight])
  · have hweight_ge_one (n : ℕ) : 1 ≤ Ω (n : ℤ) := by
      have := hmono (show 0 ≤ n by omega)
      simpa [hzero] using this
    have hweight_gt_one (n : ℕ) (hn : 0 < n) : 1 < Ω (n : ℤ) := by
      have hne : Ω (n : ℤ) ≠ 1 := by
        intro heq
        have hall := weight_eq_one_of_eq_one_at_pos Ω hzero hmono hsub hn heq
        exact htrivial hall
      exact lt_of_le_of_ne (hweight_ge_one n) (Ne.symm hne)
    have hqpos (n : ℕ) (hn : n ∈ Finset.Icc 1 M) : 0 < q n := by
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hlog : 0 < logProfile Ω n := by
        simp only [logProfile]
        exact Real.log_pos (hweight_gt_one n hnpos)
      have hden : 0 < (n : ℝ) := by exact_mod_cast hnpos
      exact div_pos hlog hden
    obtain ⟨ε₀, hε₀, hsmall⟩ :=
      exists_pos_below_finite_values q (by
        intro n hn
        exact hqpos n hn)
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε hε
    let hεprof : ℕ → ℝ := fun n => min (ε * (n : ℝ)) (logProfile Ω n)
    have hprofzero : hεprof 0 = 0 := by
      simp [hεprof, logProfile, hzero]
    have hprofmono : Monotone hεprof := by
      intro a b hab
      apply min_le_min
      · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hab) (le_of_lt hε.1)
      · unfold logProfile
        exact Real.log_le_log (hpos (a : ℤ)) (hmono hab)
    have hratio : Antitone (fun n : ℕ+ => hεprof n / (n : ℝ)) := by
      intro m n hmn
      have hmpos : 0 < (m : ℕ) := m.property
      have hnpos : 0 < (n : ℕ) := n.property
      have hmc : 0 < ((m : ℕ) : ℝ) := by exact_mod_cast hmpos
      have hnc : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast hnpos
      have hratioForm (j : ℕ+) : hεprof j / (j : ℝ) = min ε (q j) := by
        change min (ε * (j : ℝ)) (logProfile Ω j) / (j : ℝ) = _
        exact min_mul_div_of_pos ε (logProfile Ω j) (j : ℝ) (by positivity)
      change hεprof (n : ℕ) / ((n : ℕ) : ℝ) ≤ hεprof (m : ℕ) / ((m : ℕ) : ℝ)
      calc
        hεprof (n : ℕ) / ((n : ℕ) : ℝ) = min ε (q (n : ℕ)) := hratioForm n
        _ ≤ min ε (q (m : ℕ)) := by
          by_cases hmN : N ≤ (m : ℕ)
          · exact min_le_min_left ε (hN m n hmN (by exact_mod_cast hmn))
          · have hmM : (m : ℕ) ≤ M := by
              dsimp [M]
              omega
            have hmSmall' : ε₀ < q (m : ℕ) := hsmall (m : ℕ)
              (Finset.mem_Icc.mpr ⟨by exact_mod_cast hmpos, hmM⟩)
            have hmSmall : ε < q (m : ℕ) := hε.2.trans hmSmall'
            rw [min_eq_left (le_of_lt hmSmall)]
            exact min_le_left _ _
        _ = hεprof (m : ℕ) / ((m : ℕ) : ℝ) := (hratioForm m).symm
    have hcut_eq : secondaryCutoff Ω ε = logRatioWeight hεprof := by
      funext k
      simp only [secondaryCutoff, logRatioWeight, hεprof]
      rw [exp_min]
      have hexplog : Real.exp (logProfile Ω k.natAbs) = Ω ((k.natAbs : ℕ) : ℤ) := by
        change Real.exp (Real.log (Ω ((k.natAbs : ℕ) : ℤ))) = _
        exact Real.exp_log (hpos ((k.natAbs : ℕ) : ℤ))
      rw [hexplog]
      have heq : Ω k = Ω ((k.natAbs : ℕ) : ℤ) := by
        cases k with
        | ofNat n => simp
        | negSucc n =>
            have habs : (Int.negSucc n).natAbs = n + 1 := by rfl
            have hn : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
            rw [habs, hn, heven]
      rw [heq]
    rw [hcut_eq]
    exact logRatio_weight_submultiplicative hεprof hprofzero hprofmono hratio

end NlsGge.Atomic.DM047
