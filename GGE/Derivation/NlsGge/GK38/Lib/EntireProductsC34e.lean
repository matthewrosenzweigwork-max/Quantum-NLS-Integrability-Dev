import NlsGge.GK38.Lib.EntireProductsC34d

/-!
# L4c part 2b, module e: helper lemmas for the Hilbert-transform term of Lemma C.3

* `exists_l2_of_sq_summable`: a square-summable sequence is an element of `ℓ²(ℤ)`.
* `sup_sq_le`: if for every *choice* `λ_n ∈ D_n` the finite sums `Σ_n g_n(λ_n)²` are bounded, then so
  are the sums of the squares of the suprema `s_n = sup_{λ∈D_n} g_n(λ)` (the book's passage from "for any
  sequence `λ_n ∈ D_n`" to `sup_{λ∈D_n}`).
* `sep_pad`: the padded nodes `σ'_n = nπ + i(M+1)` used to extend the hypothesis (C.2), valid only
  for `|n| ≥ N`, to all `n` as required by Lemma F.6 (the book's "slightly modify, if necessary,
  some `D_n` with `|n| < N`"); the constant depends only on `M`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

theorem exists_l2_of_sq_summable {f : ℤ → ℂ} (hf : Summable fun m => ‖f m‖ ^ 2) :
    ∃ x : L2Z, (∀ m, (x : ℤ → ℂ) m = f m) ∧ ‖x‖ ^ 2 = ∑' m, ‖f m‖ ^ 2 := by
  have hm : Memℓp f 2 := by
    refine (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr ?_
    simpa using hf
  refine ⟨⟨f, hm⟩, fun m => rfl, ?_⟩
  have := hasSum_sq_l2 (⟨f, hm⟩ : L2Seq)
  exact this.tsum_eq.symm

theorem sup_sq_le {P : ℤ → Prop} {D : ℤ → Set ℂ} {g : ℤ → ℂ → ℝ} {B D0 : ℝ}
    (hne : ∀ n, P n → (D n).Nonempty) (hg0 : ∀ n lam, 0 ≤ g n lam)
    (hgB : ∀ n, P n → ∀ lam ∈ D n, g n lam ≤ B)
    (hsel : ∀ lamSeq : ℤ → ℂ, (∀ n, P n → lamSeq n ∈ D n) → ∀ T : Finset ℤ, (∀ n ∈ T, P n) →
      ∑ n ∈ T, g n (lamSeq n) ^ 2 ≤ D0)
    (T : Finset ℤ) (hT : ∀ n ∈ T, P n) :
    ∑ n ∈ T, (⨆ lam : D n, g n lam) ^ 2 ≤ D0 := by
  set s : ℤ → ℝ := fun n => ⨆ lam : D n, g n lam with hs
  have hbdd : ∀ n, P n → BddAbove (Set.range fun lam : D n => g n lam) := fun n hn =>
    ⟨B, by rintro _ ⟨lam, rfl⟩; exact hgB n hn lam lam.2⟩
  have hsel' : ∀ ε : ℝ, 0 < ε → ∑ n ∈ T, (max (s n - ε) 0) ^ 2 ≤ D0 := by
    intro ε hε
    have hex : ∀ n : ℤ, ∃ lam : ℂ, P n → lam ∈ D n ∧ s n - ε < g n lam := by
      intro n
      by_cases hn : P n
      · have : Nonempty (D n) := (hne n hn).to_subtype
        obtain ⟨lam, hlam⟩ := exists_lt_of_lt_ciSup (f := fun lam : D n => g n lam)
          (show s n - ε < ⨆ lam : D n, g n lam by simp only [hs]; linarith)
        exact ⟨lam, fun _ => ⟨lam.2, hlam⟩⟩
      · exact ⟨0, fun h => absurd h hn⟩
    choose lamSeq hlam using hex
    refine le_trans ?_ (hsel lamSeq (fun n hn => (hlam n hn).1) T hT)
    refine Finset.sum_le_sum fun n hn => ?_
    have h2 := (hlam n (hT n hn)).2
    have h0 := hg0 n (lamSeq n)
    have : max (s n - ε) 0 ≤ g n (lamSeq n) := max_le h2.le h0
    exact pow_le_pow_left₀ (le_max_right _ _) this 2
  have hcont : Continuous fun ε : ℝ => ∑ n ∈ T, (max (s n - ε) 0) ^ 2 := by fun_prop
  have hle : ∑ n ∈ T, (max (s n - 0) 0) ^ 2 ≤ D0 := by
    have h1 : Tendsto (fun ε : ℝ => ∑ n ∈ T, (max (s n - ε) 0) ^ 2) (𝓝[>] 0)
        (𝓝 (∑ n ∈ T, (max (s n - 0) 0) ^ 2)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact le_of_tendsto h1 (eventually_nhdsWithin_of_forall fun ε hε => hsel' ε hε)
  have hs0 : ∀ n ∈ T, 0 ≤ s n := fun n hn => Real.iSup_nonneg fun lam => hg0 n lam
  calc ∑ n ∈ T, s n ^ 2 = ∑ n ∈ T, (max (s n - 0) 0) ^ 2 :=
        Finset.sum_congr rfl fun n hn => by rw [sub_zero, max_eq_left (hs0 n hn)]
    _ ≤ D0 := hle

end

end NlsGge.GK38.Lib
