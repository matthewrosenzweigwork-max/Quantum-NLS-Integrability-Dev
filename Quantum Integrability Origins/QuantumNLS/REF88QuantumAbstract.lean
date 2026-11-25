import Mathlib

/-!
# REF88QuantumAbstract: the sequential-limit calculus of the printed paragraph "Quantum derivatives at arbitrary
finite mass" (R-EF8C2837, item (iii)) -- pure real analysis, no physical input

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 262-298:
  "The sequential statements imply continuity of the limits and uniform convergence on compact subsets of that
   parameter region.  For continuity, choose at each point of a convergent parameter sequence a sufficiently large
   particle number approximating its own limit; the sequential statement forces convergence to the target limit.
   If uniform convergence on a compact set failed, a violating sequence would have a converging parameter
   subsequence, contradicting the same sequential statement."  and
  "Along a compact line ... the exact telescoping identity ... The uniform adjacent-gap limits turn this identity
   into the Riemann integral of the continuous ω_{ab} along the line.  Endpoint rounding tends to zero ...  The
   fundamental theorem of calculus consequently gives ∂_{e_a-e_b} ℰ = ω_{ab}.  Integrating the exact finite coupling
   identity over a compact interval of K>0 gives K ∂_K ℰ = 𝒯."

* `splice_tendsto`: gluing a subsequence into a convergent background sequence.
* `seq_continuousOn` (printed "for continuity ..."): if for every sequence `i_N` with positions `pos N (i_N) → s ∈ C`
  one has `G N (i_N) → ω s`, and every `s ∈ C` is the limit of some position sequence, then `ω` is continuous on `C`.
* `seq_uniform` (printed "if uniform convergence ... failed ..."): and, `C` compact, `G_N → ω∘pos` uniformly on `C`.
* `line_increment` (printed telescoping/Riemann-sum step, in the form of two-sided increment bounds, which avoids
  Riemann integrals): `E_N(r) - E_N(r-1) = G_N(r)/N`, `G_N(r) → ω(r/N)` uniformly and `E_N(⌊sN⌋) → ℰ(s)` give
  `|ℰ(q) - ℰ(p) - c (q-p)| ≤ ε (q-p)` whenever `|ω - c| ≤ ε` on `[p,q]`.
* `coupling_increment` (printed "integrating the exact finite coupling identity"): same bound from finite functions
  with uniformly convergent derivatives (mean-value inequality).
* `hasDerivAt_of_increments` (printed "the fundamental theorem of calculus consequently gives ..."): increment bounds
  plus continuity of `ω` at `s` give `HasDerivAt ℰ (ω s) s`.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology Set

namespace QuantumNLS.REF88QuantumAbstract

variable {ι : Type*}

/-- Splicing a subsequence into a convergent background sequence keeps convergence. -/
theorem splice_tendsto (pos : ℕ → ι → ℝ) (s : ℝ) (e : ℕ → ι)
    (he : Tendsto (fun N => pos N (e N)) atTop (𝓝 s)) (χ : ℕ → ℕ) (hχ : StrictMono χ)
    (i' : ℕ → ι) (hi' : Tendsto (fun j => pos (χ j) (i' j)) atTop (𝓝 s)) :
    ∃ i : ℕ → ι, (∀ j, i (χ j) = i' j) ∧ Tendsto (fun N => pos N (i N)) atTop (𝓝 s) := by
  classical
  let i : ℕ → ι := fun N => if h : ∃ j, χ j = N then i' h.choose else e N
  have hi : ∀ j, i (χ j) = i' j := by
    intro j
    have h : ∃ j', χ j' = χ j := ⟨j, rfl⟩
    simp only [i, dif_pos h]
    have := hχ.injective h.choose_spec
    rw [this]
  refine ⟨i, hi, ?_⟩
  rw [Metric.tendsto_atTop] at he hi' ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := he ε hε
  obtain ⟨J, hJ⟩ := hi' ε hε
  refine ⟨max N1 (χ J), fun N hN => ?_⟩
  by_cases h : ∃ j, χ j = N
  · obtain ⟨j, rfl⟩ := h
    have hjJ : J ≤ j := by
      by_contra hlt
      push Not at hlt
      have := hχ hlt
      have := le_trans (le_max_right N1 (χ J)) hN
      omega
    rw [hi j]
    exact hJ j hjJ
  · have : i N = e N := by simp only [i, dif_neg h]
    rw [this]
    exact hN1 N (le_trans (le_max_left _ _) hN)

variable (pos G : ℕ → ι → ℝ) (ω : ℝ → ℝ) (C : Set ℝ)

/-- Sequential limit statements (for every convergent-position sequence) imply continuity of the limit. -/
theorem seq_continuousOn
    (hA : ∀ s ∈ C, ∃ e : ℕ → ι, Tendsto (fun N => pos N (e N)) atTop (𝓝 s))
    (hB : ∀ (i : ℕ → ι) (s : ℝ), s ∈ C → Tendsto (fun N => pos N (i N)) atTop (𝓝 s) →
      Tendsto (fun N => G N (i N)) atTop (𝓝 (ω s))) :
    ContinuousOn ω C := by
  intro s hs
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hbad⟩ := hcon
  -- a sequence of points of `C` converging to `s` with `ω` far from `ω s`
  have hseq : ∀ k : ℕ, ∃ t ∈ C, dist t s < 1 / ((k : ℝ) + 1) ∧ ε ≤ dist (ω t) (ω s) := by
    intro k
    exact hbad (1 / ((k : ℝ) + 1)) (by positivity)
  choose t htC htd htε using hseq
  -- for each `k`, realise `ω (t k)` by a sequence
  have hreal : ∀ k : ℕ, ∃ e : ℕ → ι, Tendsto (fun N => pos N (e N)) atTop (𝓝 (t k)) ∧
      Tendsto (fun N => G N (e N)) atTop (𝓝 (ω (t k))) := by
    intro k
    obtain ⟨e, he⟩ := hA (t k) (htC k)
    exact ⟨e, he, hB e _ (htC k) he⟩
  choose e hepos heG using hreal
  -- strictly increasing times
  have hex : ∀ k : ℕ, ∀ N0 : ℕ, ∃ N, N0 < N ∧ dist (pos N (e k N)) (t k) < 1 / ((k : ℝ) + 1) ∧
      dist (G N (e k N)) (ω (t k)) < ε / 3 := by
    intro k N0
    have h1 := (Metric.tendsto_atTop.1 (hepos k)) (1 / ((k : ℝ) + 1)) (by positivity)
    have h2 := (Metric.tendsto_atTop.1 (heG k)) (ε / 3) (by positivity)
    obtain ⟨A, hA'⟩ := h1
    obtain ⟨B, hB'⟩ := h2
    refine ⟨max (max A B) N0 + 1, by omega, hA' _ (by omega), hB' _ (by omega)⟩
  choose Nf hNf1 hNf2 hNf3 using hex
  let χ : ℕ → ℕ := fun k => Nat.rec (Nf 0 0) (fun k prev => Nf (k + 1) prev) k
  have hχs : StrictMono χ := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact hNf1 (k + 1) (χ k)
  have hχ : ∀ k, dist (pos (χ k) (e k (χ k))) (t k) < 1 / ((k : ℝ) + 1) ∧
      dist (G (χ k) (e k (χ k))) (ω (t k)) < ε / 3 := by
    intro k
    cases k with
    | zero => exact ⟨hNf2 0 0, hNf3 0 0⟩
    | succ k => exact ⟨hNf2 (k + 1) (χ k), hNf3 (k + 1) (χ k)⟩
  -- positions converge to `s`
  have hts : Tendsto t atTop (𝓝 s) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨k0, hk0⟩ := exists_nat_gt (1 / η)
    refine ⟨k0, fun k hk => ?_⟩
    have : (1 : ℝ) / ((k : ℝ) + 1) < η := by
      rw [div_lt_iff₀ (by positivity)]
      have : 1 / η < (k : ℝ) + 1 := by
        have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      rw [div_lt_iff₀ hη] at this
      linarith
    exact lt_trans (htd k) this
  have hpos' : Tendsto (fun k => pos (χ k) (e k (χ k))) atTop (𝓝 s) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Metric.tendsto_atTop] at hts ⊢
    intro η hη
    obtain ⟨k1, hk1⟩ := hts (η / 2) (by positivity)
    obtain ⟨k2, hk2⟩ := (Metric.tendsto_atTop.1 h1) (η / 2) (by positivity)
    refine ⟨max k1 k2, fun k hk => ?_⟩
    have a1 := hk1 k (le_trans (le_max_left _ _) hk)
    have a2 := hk2 k (le_trans (le_max_right _ _) hk)
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at a2
    calc dist (pos (χ k) (e k (χ k))) s ≤ dist (pos (χ k) (e k (χ k))) (t k) + dist (t k) s :=
          dist_triangle _ _ _
      _ < η / 2 + η / 2 := add_lt_add (lt_of_lt_of_le (hχ k).1 a2.le) a1
      _ = η := by ring
  obtain ⟨e0, he0⟩ := hA s hs
  obtain ⟨i, hi, hipos⟩ := splice_tendsto pos s e0 he0 χ hχs (fun k => e k (χ k)) hpos'
  have hlim := hB i s hs hipos
  have hlim' : Tendsto (fun k => G (χ k) (e k (χ k))) atTop (𝓝 (ω s)) := by
    have := hlim.comp hχs.tendsto_atTop
    refine this.congr (fun k => ?_)
    simp only [Function.comp, hi]
  -- contradiction
  have h3 := (Metric.tendsto_atTop.1 hlim') (ε / 3) (by positivity)
  obtain ⟨k0, hk0⟩ := h3
  have := hk0 k0 le_rfl
  have h4 := (hχ k0).2
  have h5 := htε k0
  have : dist (ω (t k0)) (ω s) < 2 * (ε / 3) := by
    calc dist (ω (t k0)) (ω s) ≤ dist (ω (t k0)) (G (χ k0) (e k0 (χ k0))) + dist (G (χ k0) (e k0 (χ k0))) (ω s) :=
          dist_triangle _ _ _
      _ < ε / 3 + ε / 3 := add_lt_add (by rw [dist_comm]; exact h4) this
      _ = 2 * (ε / 3) := by ring
  linarith


/-- Uniform convergence on a compact set from the sequential statements. -/
theorem seq_uniform (hCc : IsCompact C)
    (hA : ∀ s ∈ C, ∃ e : ℕ → ι, Tendsto (fun N => pos N (e N)) atTop (𝓝 s))
    (hB : ∀ (i : ℕ → ι) (s : ℝ), s ∈ C → Tendsto (fun N => pos N (i N)) atTop (𝓝 s) →
      Tendsto (fun N => G N (i N)) atTop (𝓝 (ω s)))
    (hcont : ContinuousOn ω C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ι, pos N i ∈ C → |G N i - ω (pos N i)| < ε := by
  by_contra hcon
  have hfreq : ∃ᶠ N : ℕ in atTop, ∃ i : ι, pos N i ∈ C ∧ ε ≤ |G N i - ω (pos N i)| := by
    have h1 := Filter.not_eventually.1 hcon
    refine h1.mono ?_
    intro N hN
    push Not at hN
    exact hN
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose i hiC hiε using hφP
  have hx : ∀ j, pos (φ j) (i j) ∈ C := hiC
  obtain ⟨s, hsC, ψ, hψ, hxψ⟩ := hCc.tendsto_subseq hx
  have hχ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  obtain ⟨e0, he0⟩ := hA s hsC
  obtain ⟨ia, hia, hiapos⟩ := splice_tendsto pos s e0 he0 (φ ∘ ψ) hχ (fun k => i (ψ k))
    hxψ
  have hlim := hB ia s hsC hiapos
  have hlim' : Tendsto (fun k => G (φ (ψ k)) (i (ψ k))) atTop (𝓝 (ω s)) := by
    have := hlim.comp hχ.tendsto_atTop
    refine this.congr (fun k => ?_)
    show G ((φ ∘ ψ) k) (ia ((φ ∘ ψ) k)) = _
    rw [hia k]; rfl
  have hωx : Tendsto (fun k => ω (pos (φ (ψ k)) (i (ψ k)))) atTop (𝓝 (ω s)) := by
    refine (hcont s hsC).tendsto.comp ?_
    exact tendsto_nhdsWithin_iff.2 ⟨hxψ, Filter.Eventually.of_forall fun k => hx (ψ k)⟩
  have h0 : Tendsto (fun k => |G (φ (ψ k)) (i (ψ k)) - ω (pos (φ (ψ k)) (i (ψ k)))|) atTop (𝓝 0) := by
    have := (hlim'.sub hωx)
    rw [sub_self] at this
    simpa using this.abs
  have h1 := (Metric.tendsto_atTop.1 h0) ε hε
  obtain ⟨k0, hk0⟩ := h1
  have := hk0 k0 le_rfl
  rw [Real.dist_eq, sub_zero, abs_abs] at this
  have h2 := (hiε (ψ k0))
  linarith

/-- **Derivative from increment bounds.** If `ω` is continuous at `s` and on a neighbourhood of `s` the
increments of `E` over every subinterval `[p, q]` on which `ω` stays within `ε` of `c` differ from `c (q - p)` by at
most `ε (q - p)`, then `E' (s) = ω s`. -/
theorem hasDerivAt_of_increments (E ω : ℝ → ℝ) (s : ℝ) (hω : ContinuousAt ω s) (δ : ℝ) (hδ : 0 < δ)
    (hinc : ∀ p q : ℝ, s - δ ≤ p → p < q → q ≤ s + δ → ∀ c ε : ℝ,
      (∀ t ∈ Set.Icc p q, |ω t - c| ≤ ε) → |E q - E p - c * (q - p)| ≤ ε * (q - p)) :
    HasDerivAt E (ω s) s := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨η, hη, hηω⟩ := Metric.continuousAt_iff.1 hω ε hε
  have hev : ∀ᶠ h : ℝ in 𝓝 0, ‖E (s + h) - E s - h • ω s‖ ≤ ε * ‖h‖ := by
    have : Set.Ioo (-(min η δ)) (min η δ) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by simp [hη, hδ]) (by simp [hη, hδ])
    filter_upwards [this] with h hh
    have hη' : |h| < η := lt_of_lt_of_le (abs_lt.2 ⟨hh.1, hh.2⟩) (min_le_left _ _)
    have hδ' : |h| < δ := lt_of_lt_of_le (abs_lt.2 ⟨hh.1, hh.2⟩) (min_le_right _ _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
    rcases lt_trichotomy h 0 with hneg | hzero | hpos
    · have hab := abs_of_neg hneg
      have := hinc (s + h) s (by linarith [abs_lt.1 hδ']) (by linarith) (by linarith [hδ])
        (ω s) ε (fun t ht => by
          have : dist t s < η := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2, abs_lt.1 hη']
          have := hηω this
          rw [Real.dist_eq] at this
          exact this.le)
      rw [hab]
      have e : |E s - E (s + h) - ω s * (s - (s + h))| = |E (s + h) - E s - h * ω s| := by
        rw [← abs_neg]; congr 1; ring
      rw [e] at this
      nlinarith [this]
    · subst hzero; simp
    · have hab := abs_of_pos hpos
      have := hinc s (s + h) (by linarith) (by linarith) (by linarith [abs_lt.1 hδ'])
        (ω s) ε (fun t ht => by
          have : dist t s < η := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2, abs_lt.1 hη']
          have := hηω this
          rw [Real.dist_eq] at this
          exact this.le)
      rw [hab]
      have e : E (s + h) - E s - ω s * (s + h - s) = E (s + h) - E s - h * ω s := by ring
      rw [e] at this
      nlinarith [this]
  exact hev


theorem tendsto_floor_div (q : ℝ) :
    Tendsto (fun N : ℕ => ((⌊q * N⌋ : ℤ) : ℝ) / N) atTop (𝓝 q) := by
  have h1 : Tendsto (fun N : ℕ => q - 1 / (N : ℝ)) atTop (𝓝 q) := by
    simpa using tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat (a := q)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN']
    have := Int.lt_floor_add_one (q * N)
    have : q * N - 1 ≤ ⌊q * N⌋ := by linarith
    calc (q - 1 / (N : ℝ)) * N = q * N - 1 := by field_simp
      _ ≤ _ := this
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    exact Int.floor_le (q * N)

/-- **Riemann-sum step**: the telescoping identity `E_N(r) - E_N(r-1) = G_N(r)/N` together with the uniform
convergence `G_N(r) → ω(r/N)` and the endpoint convergence `E_N(⌊sN⌋) → ℰ(s)` give the increment bound for `ℰ`. -/
theorem line_increment (Eseq G : ℕ → ℤ → ℝ) (ω ℰ : ℝ → ℝ) (α β : ℝ)
    (htele : ∀ N : ℕ, 0 < N → ∀ r : ℤ, Eseq N r - Eseq N (r - 1) = G N r / N)
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ r : ℤ, α ≤ (r : ℝ) / N → (r : ℝ) / N ≤ β →
      |G N r - ω ((r : ℝ) / N)| < ε)
    (hend : ∀ s ∈ Set.Icc α β, Tendsto (fun N : ℕ => Eseq N ⌊s * N⌋) atTop (𝓝 (ℰ s)))
    {p q : ℝ} (hαp : α ≤ p) (hpq : p < q) (hqβ : q ≤ β) {c ε : ℝ}
    (hω : ∀ t ∈ Set.Icc p q, |ω t - c| ≤ ε) :
    |ℰ q - ℰ p - c * (q - p)| ≤ ε * (q - p) := by
  have hlim : ∀ ε' : ℝ, 0 < ε' → |ℰ q - ℰ p - c * (q - p)| ≤ (ε + ε') * (q - p) := by
    intro ε' hε'
    have hq := hend q ⟨by linarith, hqβ⟩
    have hp := hend p ⟨hαp, by linarith⟩
    have hfq := tendsto_floor_div q
    have hfp := tendsto_floor_div p
    have hL : Tendsto (fun N : ℕ => |Eseq N ⌊q * N⌋ - Eseq N ⌊p * N⌋ -
        c * ((((⌊q * N⌋ : ℤ) : ℝ) / N) - (((⌊p * N⌋ : ℤ) : ℝ) / N))|) atTop
        (𝓝 |ℰ q - ℰ p - c * (q - p)|) :=
      ((hq.sub hp).sub ((hfq.sub hfp).const_mul c)).abs
    have hR : Tendsto (fun N : ℕ => (ε + ε') * ((((⌊q * N⌋ : ℤ) : ℝ) / N) - (((⌊p * N⌋ : ℤ) : ℝ) / N)))
        atTop (𝓝 ((ε + ε') * (q - p))) := (hfq.sub hfp).const_mul _
    refine le_of_tendsto_of_tendsto hL hR ?_
    filter_upwards [hunif ε' hε', eventually_gt_atTop 0] with N hU hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    set rp := ⌊p * N⌋ with hrp
    set rq := ⌊q * N⌋ with hrq
    have hrpq : rp ≤ rq := Int.floor_le_floor (by nlinarith)
    -- induction on the number of steps
    have key : ∀ n : ℕ, rp + n ≤ rq →
        |Eseq N (rp + n) - Eseq N rp - c * (n / N)| ≤ (ε + ε') * (n / N) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hn' : rp + n ≤ rq := by omega
        have ih' := ih hn'
        have hr := htele N hN (rp + (n + 1 : ℕ))
        have hr' : rp + ((n + 1 : ℕ) : ℤ) - 1 = rp + n := by push_cast; ring
        rw [hr'] at hr
        set r : ℤ := rp + ((n + 1 : ℕ) : ℤ) with hrdef
        have hr1 : p < (r : ℝ) / N := by
          rw [lt_div_iff₀ hN']
          have : p * N < (rp : ℝ) + 1 := Int.lt_floor_add_one (p * N)
          have hr2 : (rp : ℝ) + 1 ≤ r := by
            rw [hrdef]; push_cast; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
          linarith
        have hr3 : (r : ℝ) / N ≤ q := by
          rw [div_le_iff₀ hN']
          have : (r : ℝ) ≤ rq := by exact_mod_cast (by omega : r ≤ rq)
          have := Int.floor_le (q * N)
          linarith
        have hG := hU r (by linarith) (by linarith)
        have hωr := hω ((r : ℝ) / N) ⟨hr1.le, hr3⟩
        have hGc : |G N r - c| ≤ ε + ε' := by
          calc |G N r - c| = |(G N r - ω ((r : ℝ) / N)) + (ω ((r : ℝ) / N) - c)| := by ring_nf
            _ ≤ |G N r - ω ((r : ℝ) / N)| + |ω ((r : ℝ) / N) - c| := abs_add_le _ _
            _ ≤ ε + ε' := by linarith
        have hstep : |Eseq N r - Eseq N (rp + n) - c / N| ≤ (ε + ε') / N := by
          rw [show Eseq N r - Eseq N (rp + n) = G N r / N from hr]
          rw [show G N r / N - c / N = (G N r - c) / N by ring, abs_div, abs_of_pos hN']
          exact div_le_div_of_nonneg_right hGc hN'.le
        have e1 : (((n + 1 : ℕ) : ℝ) / N) = (n / N) + 1 / N := by push_cast; ring
        calc |Eseq N (rp + ((n + 1 : ℕ) : ℤ)) - Eseq N rp - c * (((n + 1 : ℕ) : ℝ) / N)|
            = |(Eseq N (rp + n) - Eseq N rp - c * (n / N)) + (Eseq N r - Eseq N (rp + n) - c / N)| := by
              rw [e1, hrdef]; push_cast; ring_nf
          _ ≤ |Eseq N (rp + n) - Eseq N rp - c * (n / N)| + |Eseq N r - Eseq N (rp + n) - c / N| :=
              abs_add_le _ _
          _ ≤ (ε + ε') * (n / N) + (ε + ε') / N := add_le_add ih' hstep
          _ = (ε + ε') * (((n + 1 : ℕ) : ℝ) / N) := by rw [e1]; ring
    have hk := key (rq - rp).toNat (by omega)
    have e2 : rp + ((rq - rp).toNat : ℤ) = rq := by omega
    rw [e2] at hk
    have e3 : (((rq - rp).toNat : ℕ) : ℝ) = (rq : ℝ) - rp := by
      have : (((rq - rp).toNat : ℕ) : ℤ) = rq - rp := by omega
      have h5 : ((((rq - rp).toNat : ℕ) : ℤ) : ℝ) = ((rq - rp : ℤ) : ℝ) := by rw [this]
      push_cast at h5 ⊢
      exact h5
    rw [e3] at hk
    have e4 : ((rq : ℝ) - rp) / N = (rq : ℝ) / N - (rp : ℝ) / N := by ring
    rw [e4] at hk
    exact hk
  by_contra hcon
  push Not at hcon
  have hqp : 0 < q - p := by linarith
  have := hlim ((|ℰ q - ℰ p - c * (q - p)| - ε * (q - p)) / (2 * (q - p))) (by
    apply div_pos <;> nlinarith)
  have h2 : (ε + (|ℰ q - ℰ p - c * (q - p)| - ε * (q - p)) / (2 * (q - p))) * (q - p) =
      ε * (q - p) + (|ℰ q - ℰ p - c * (q - p)| - ε * (q - p)) / 2 := by
    field_simp
  rw [h2] at this
  linarith


/-- **Integrated-derivative step** (coupling direction): finite functions `E_N` with derivatives `D_N` that converge
uniformly to `g` on `[p, q]`, and `E_N(p) → ℰ(p)`, `E_N(q) → ℰ(q)`, give the increment bound for `ℰ`. -/
theorem coupling_increment (E D : ℕ → ℝ → ℝ) (g ℰ : ℝ → ℝ) {p q : ℝ} (hpq : p < q)
    (hder : ∀ N : ℕ, ∀ K ∈ Set.Icc p q, HasDerivAt (E N) (D N K) K)
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ K ∈ Set.Icc p q, |D N K - g K| < ε)
    (hp : Tendsto (fun N => E N p) atTop (𝓝 (ℰ p))) (hq : Tendsto (fun N => E N q) atTop (𝓝 (ℰ q)))
    {c ε : ℝ} (hg : ∀ t ∈ Set.Icc p q, |g t - c| ≤ ε) :
    |ℰ q - ℰ p - c * (q - p)| ≤ ε * (q - p) := by
  have hlim : ∀ ε' : ℝ, 0 < ε' → |ℰ q - ℰ p - c * (q - p)| ≤ (ε + ε') * (q - p) := by
    intro ε' hε'
    have hL : Tendsto (fun N : ℕ => |E N q - E N p - c * (q - p)|) atTop
        (𝓝 |ℰ q - ℰ p - c * (q - p)|) := ((hq.sub hp).sub tendsto_const_nhds).abs
    refine le_of_tendsto_of_tendsto hL tendsto_const_nhds ?_
    filter_upwards [hunif ε' hε'] with N hU
    have hpI : p ∈ Set.Icc p q := ⟨le_rfl, hpq.le⟩
    have hqI : q ∈ Set.Icc p q := ⟨hpq.le, le_rfl⟩
    have hd : ∀ K ∈ Set.Icc p q, HasDerivWithinAt (fun K => E N K - c * K) (D N K - c) (Set.Icc p q) K := by
      intro K hK
      have h1 : HasDerivAt (fun K : ℝ => E N K - c * K) (D N K - c) K := by
        have h2 : HasDerivAt (fun y : ℝ => c * y) c K := by
          simpa using (hasDerivAt_id' K).const_mul c
        have := (hder N K hK).fun_sub h2
        simpa using this
      exact h1.hasDerivWithinAt
    have hb : ∀ K ∈ Set.Icc p q, ‖D N K - c‖ ≤ ε + ε' := by
      intro K hK
      rw [Real.norm_eq_abs]
      calc |D N K - c| = |(D N K - g K) + (g K - c)| := by ring_nf
        _ ≤ |D N K - g K| + |g K - c| := abs_add_le _ _
        _ ≤ ε + ε' := by linarith [hU K hK, hg K hK]
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc p q) hpI hqI
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < q - p)] at this
    calc |E N q - E N p - c * (q - p)| = |E N q - c * q - (E N p - c * p)| := by ring_nf
      _ ≤ _ := this
  by_contra hcon
  push Not at hcon
  have hqp : 0 < q - p := by linarith
  have := hlim ((|ℰ q - ℰ p - c * (q - p)| - ε * (q - p)) / (2 * (q - p))) (by
    apply div_pos <;> nlinarith)
  have h2 : (ε + (|ℰ q - ℰ p - c * (q - p)| - ε * (q - p)) / (2 * (q - p))) * (q - p) =
      ε * (q - p) + (|ℰ q - ℰ p - c * (q - p)| - ε * (q - p)) / 2 := by
    field_simp
  rw [h2] at this
  linarith

end QuantumNLS.REF88QuantumAbstract

#print axioms QuantumNLS.REF88QuantumAbstract.splice_tendsto
#print axioms QuantumNLS.REF88QuantumAbstract.seq_continuousOn
#print axioms QuantumNLS.REF88QuantumAbstract.seq_uniform
#print axioms QuantumNLS.REF88QuantumAbstract.hasDerivAt_of_increments
#print axioms QuantumNLS.REF88QuantumAbstract.tendsto_floor_div
#print axioms QuantumNLS.REF88QuantumAbstract.line_increment
#print axioms QuantumNLS.REF88QuantumAbstract.coupling_increment
