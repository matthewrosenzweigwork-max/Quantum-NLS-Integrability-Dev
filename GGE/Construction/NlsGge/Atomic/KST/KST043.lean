import NlsGge.Atomic.DM.DM047

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.KST043

open NlsGge.Atomic.DM046 NlsGge.Atomic.DM047
open Filter
open scoped Topology

/-- The positive-index logarithmic ratio of an integer weight. -/
def KSTLogRatio (v : ℤ → ℝ) (n : ℕ+) : ℝ :=
  Real.log (v (n : ℤ)) / (n : ℝ)

/-- The source hypotheses for a subexponential secondary weight.  The eventual
monotonicity clause retains both directions; the zero value is only required
to be at least one, as in KST. -/
def KSTSubexponentialWeight (v : ℤ → ℝ) : Prop :=
  1 ≤ v 0 ∧
  (∀ k : ℤ, v (-k) = v k) ∧
  Monotone (fun n : ℕ => v (n : ℤ)) ∧
  SubmultiplicativeWeight v ∧
  Tendsto (KSTLogRatio v) atTop (𝓝 0) ∧
  ∃ N : ℕ,
    (∀ m n : ℕ+, N ≤ (m : ℕ) → (m : ℕ) ≤ (n : ℕ) →
      KSTLogRatio v m ≤ KSTLogRatio v n) ∨
    (∀ m n : ℕ+, N ≤ (m : ℕ) → (m : ℕ) ≤ (n : ℕ) →
      KSTLogRatio v n ≤ KSTLogRatio v m)

private def normalizeAtZero (v : ℤ → ℝ) (k : ℤ) : ℝ :=
  if k = 0 then 1 else v k

private theorem rawWeight_ge_one {v : ℤ → ℝ}
    (hv0 : 1 ≤ v 0) (heven : ∀ k : ℤ, v (-k) = v k)
    (hmono : Monotone (fun n : ℕ => v (n : ℤ))) (k : ℤ) :
    1 ≤ v k := by
  have hn (n : ℕ) : 1 ≤ v (n : ℤ) := by
    exact hv0.trans (hmono (Nat.zero_le n))
  cases k with
  | ofNat n => simpa using hn n
  | negSucc n =>
      have hpos := hn (n + 1)
      have hcast : (((n + 1 : ℕ) : ℤ)) = -((Int.negSucc n : ℤ)) := by omega
      rw [← heven (Int.negSucc n), ← hcast]
      exact hpos

private theorem normalized_zero (v : ℤ → ℝ) : normalizeAtZero v 0 = 1 := by
  simp [normalizeAtZero]

private theorem normalized_ge_one {v : ℤ → ℝ}
    (hv0 : 1 ≤ v 0) (heven : ∀ k : ℤ, v (-k) = v k)
    (hmono : Monotone (fun n : ℕ => v (n : ℤ))) (k : ℤ) :
    1 ≤ normalizeAtZero v k := by
  by_cases hk : k = 0
  · simp [normalizeAtZero, hk]
  · simp [normalizeAtZero, hk]
    exact rawWeight_ge_one hv0 heven hmono k

private theorem normalized_even {v : ℤ → ℝ}
    (heven : ∀ k : ℤ, v (-k) = v k) (k : ℤ) :
    normalizeAtZero v (-k) = normalizeAtZero v k := by
  by_cases hk : k = 0
  · simp [normalizeAtZero, hk]
  · have hneg : -k ≠ 0 := by simpa using hk
    simp [normalizeAtZero, hk, hneg, heven k]

private theorem normalized_monotone {v : ℤ → ℝ}
    (hv0 : 1 ≤ v 0) (hmono : Monotone (fun n : ℕ => v (n : ℤ))) :
    Monotone (fun n : ℕ => normalizeAtZero v (n : ℤ)) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · simp [normalizeAtZero, hb]
    · have hle : 1 ≤ v (b : ℤ) := by
        exact hv0.trans (hmono (Nat.zero_le b))
      simpa [normalizeAtZero, hb] using hle
  · by_cases hb : b = 0
    · subst b
      omega
    · simp [normalizeAtZero, ha, hb]
      exact hmono hab

private theorem normalized_submultiplicative {v : ℤ → ℝ}
    (hv0 : 1 ≤ v 0) (heven : ∀ k : ℤ, v (-k) = v k)
    (hmono : Monotone (fun n : ℕ => v (n : ℤ)))
    (hsub : SubmultiplicativeWeight v) :
    SubmultiplicativeWeight (normalizeAtZero v) := by
  intro k l
  have hge (j : ℤ) : 1 ≤ normalizeAtZero v j :=
    normalized_ge_one hv0 heven hmono j
  by_cases hk : k = 0
  · subst k
    simp only [zero_add, normalized_zero, one_mul]
    exact le_rfl
  · by_cases hl : l = 0
    · subst l
      simp only [add_zero, normalized_zero, mul_one]
      exact le_rfl
    · by_cases hsum : k + l = 0
      · have hleft : normalizeAtZero v (k + l) = 1 := by
          simp [normalizeAtZero, hsum]
        rw [hleft]
        have hprod : 1 ≤ normalizeAtZero v k * normalizeAtZero v l := by
          exact one_le_mul_of_one_le_of_one_le (hge k) (hge l)
        exact hprod
      · rw [show normalizeAtZero v (k + l) = v (k + l) by
            simp [normalizeAtZero, hsum],
          show normalizeAtZero v k = v k by simp [normalizeAtZero, hk],
          show normalizeAtZero v l = v l by simp [normalizeAtZero, hl]]
        exact hsub k l

private theorem normalized_cutoff_eq (v : ℤ → ℝ) (hv0 : 1 ≤ v 0)
    (ε : ℝ) :
    secondaryCutoff (normalizeAtZero v) ε =
      fun k => min (Real.exp (ε * (k.natAbs : ℝ))) (v k) := by
  funext k
  by_cases hk : k = 0
  · subst k
    simp [secondaryCutoff, normalizeAtZero, hv0]
  · simp [secondaryCutoff, normalizeAtZero, hk]

private theorem raw_ratio_nonneg {v : ℤ → ℝ}
    (hv0 : 1 ≤ v 0)
    (hmono : Monotone (fun n : ℕ => v (n : ℤ))) (n : ℕ+) :
    0 ≤ KSTLogRatio v n := by
  have hv : 1 ≤ v (n : ℤ) :=
    hv0.trans (hmono (Nat.zero_le (n : ℕ)))
  unfold KSTLogRatio
  apply div_nonneg
  · exact Real.log_nonneg hv
  · exact_mod_cast n.property.le

/-- Every KST subexponential weight has a submultiplicative exponential cutoff
for all sufficiently small positive rates.  Only the zero coordinate is
normalized for the DM-047 bridge, and the cutoff identity proves this does not
change the stated weight. -/
theorem min_exp_subexp_submultiplicative {v : ℤ → ℝ}
    (hv : KSTSubexponentialWeight v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀,
      SubmultiplicativeWeight
        (fun k => min (Real.exp (ε * (k.natAbs : ℝ))) (v k)) := by
  rcases hv with ⟨hv0, heven, hmono, hsub, hratio_limit, htail⟩
  let Ω := normalizeAtZero v
  have hΩ0 : Ω 0 = 1 := normalized_zero v
  have hΩpos : ∀ k : ℤ, 0 < Ω k := by
    intro k
    have h := normalized_ge_one hv0 heven hmono k
    exact lt_of_lt_of_le (by norm_num) h
  have hΩeven : ∀ k : ℤ, Ω (-k) = Ω k :=
    normalized_even heven
  have hΩmono : Monotone (fun n : ℕ => Ω (n : ℤ)) :=
    normalized_monotone hv0 hmono
  have hΩsub : SubmultiplicativeWeight Ω :=
    normalized_submultiplicative hv0 heven hmono hsub
  have hΩtail : ∃ N : ℕ, ∀ m n : ℕ+,
      N ≤ (m : ℕ) → (m : ℕ) ≤ (n : ℕ) →
        logProfile Ω n / (n : ℝ) ≤ logProfile Ω m / (m : ℝ) := by
    rcases htail with ⟨N, hinc | hanti⟩
    · refine ⟨N, ?_⟩
      intro m n hm hmn
      have hzero : ∀ j : ℕ+, N ≤ (j : ℕ) → KSTLogRatio v j = 0 := by
        intro j hj
        have hupper : KSTLogRatio v j ≤ 0 :=
          le_of_tendsto_of_tendsto
            (tendsto_const_nhds : Filter.Tendsto
              (fun _ : ℕ+ => KSTLogRatio v j) atTop (𝓝 (KSTLogRatio v j)))
            hratio_limit
            (Filter.eventually_atTop.2 ⟨j, fun i hji =>
              hinc j i hj (by exact_mod_cast hji)⟩)
        exact le_antisymm hupper (raw_ratio_nonneg hv0 hmono j)
      have hmzero := hzero m hm
      have hnN : N ≤ (n : ℕ) := le_trans hm (by exact_mod_cast hmn)
      have hnzero := hzero n hnN
      have hΩm : Ω (m : ℤ) = v (m : ℤ) := by
        simp [Ω, normalizeAtZero]
      have hΩn : Ω (n : ℤ) = v (n : ℤ) := by
        simp [Ω, normalizeAtZero]
      change logProfile Ω n / (n : ℝ) ≤ logProfile Ω m / (m : ℝ)
      rw [show logProfile Ω n / (n : ℝ) = KSTLogRatio v n by
        simp [KSTLogRatio, logProfile, hΩn],
        show logProfile Ω m / (m : ℝ) = KSTLogRatio v m by
        simp [KSTLogRatio, logProfile, hΩm], hnzero, hmzero]
    · refine ⟨N, ?_⟩
      intro m n hm hmn
      have hΩm : Ω (m : ℤ) = v (m : ℤ) := by
        simp [Ω, normalizeAtZero]
      have hΩn : Ω (n : ℤ) = v (n : ℤ) := by
        simp [Ω, normalizeAtZero]
      change logProfile Ω n / (n : ℝ) ≤ logProfile Ω m / (m : ℝ)
      simpa [logProfile, hΩn, hΩm, KSTLogRatio] using hanti m n hm hmn
  obtain ⟨ε₀, hε₀, hcut⟩ :=
    dm_secondary_cutoff_submultiplicative Ω hΩ0 hΩpos hΩeven hΩmono hΩsub hΩtail
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε
  have hcut' := hcut ε hε
  change SubmultiplicativeWeight (secondaryCutoff (normalizeAtZero v) ε) at hcut'
  rw [normalized_cutoff_eq v hv0 ε] at hcut'
  exact hcut'

end NlsGge.Atomic.KST043
