import NlsGge.GK38.Lib.EntireProductsC34f

/-!
# L4c part 2b, module g: Lemma C.3

`ratioProd_l2` (book Lemma C.3): `∏_{m≠n} (σ_m - λ)/(ρ_m - λ) = 1 + ℓ²_n` on `D_n`, `|n| ≥ N`, with
an explicit `ℓ²` majorant `b` and a bound `C` depending only on `M ≥ ‖ρ̃‖_∞`, `K ≥ ‖σ - ρ‖²_{ℓ²}`
and `c` (not on `N`, `σ`, `ρ`).

Route (the book's): split off the exceptional finite set `E` (module c), apply the sharp Lemma C.2
(L4c part 1) to the rest, bound `Σ_n B_n² ≤ (Σ B_n)²` (module d) and the Hilbert-transform terms
`A_n(λ_n) = Σ_{m≠n} α_m/(ρ_m - λ_n)` by `hilbertGen_bdd` (book Lemma F.6, L4b), with the padded
nodes of module f for `|n| < N`; the supremum over `D_n` is handled by `sup_sq_le` (module e).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

theorem norm_c3A_le {σ ρ : ℤ → ℂ} {n : ℤ} {lam : ℂ} {c K : ℝ} {E : Finset ℤ} (hc : 0 < c)
    (ha : Summable fun m => ‖σ m - ρ m‖ ^ 2) (haK : ∑' m, ‖σ m - ρ m‖ ^ 2 ≤ K)
    (hsep : ∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖ρ m - lam‖) :
    ‖c3A σ ρ E n lam‖ ≤ c3S c K := by
  obtain ⟨hu, huS⟩ := summable_ratioU (n := n) (lam := lam) hc ha haK hsep
  have hG' : Summable fun m => ‖uG E (ratioU σ ρ n lam) m‖ :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_uG_le E _)
  unfold c3A
  exact (norm_tsum_le_tsum_norm hG').trans
    ((hG'.tsum_le_tsum (norm_uG_le E _) hu).trans huS)

theorem summable_sub_sq {σ ρ : ℤ → ℂ} (hσ : Summable fun n => ‖prodDev σ n‖ ^ 2)
    (hρ : Summable fun n => ‖prodDev ρ n‖ ^ 2) : Summable fun m => ‖σ m - ρ m‖ ^ 2 := by
  refine ((hσ.add hρ).mul_left 2).of_nonneg_of_le (fun _ => sq_nonneg _) fun m => ?_
  have e : σ m - ρ m = prodDev σ m - prodDev ρ m := by unfold prodDev; ring
  rw [e]
  have h := norm_sub_le (prodDev σ m) (prodDev ρ m)
  nlinarith [norm_nonneg (prodDev σ m), norm_nonneg (prodDev ρ m), norm_nonneg (prodDev σ m - prodDev ρ m),
    sq_nonneg (‖prodDev σ m‖ - ‖prodDev ρ m‖)]

/-- **Book Lemma C.3.**  See the module docstring. -/
theorem ratioProd_l2 (M K c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ (σ ρ : ℤ → ℂ) (N : ℕ), (Summable fun n => ‖prodDev σ n‖ ^ 2) →
      (Summable fun n => ‖prodDev ρ n‖ ^ 2) → Function.Injective ρ →
      (∀ n, ‖prodDev ρ n‖ ≤ M) → (∑' n, ‖σ n - ρ n‖ ^ 2) ≤ K →
      (∀ n : ℤ, (N : ℝ) ≤ |(n : ℝ)| → ∀ m, m ≠ n → ∀ lam ∈ Dn n,
        c⁻¹ * |(m : ℝ) - n| ≤ ‖ρ m - lam‖) →
      ∃ b : ℤ → ℝ, (∀ n : ℤ, (N : ℝ) ≤ |(n : ℝ)| → ∀ lam ∈ Dn n,
        Multipliable (fun m : ℤ => if m = n then 1 else (σ m - lam) / (ρ m - lam))
          (symmetricIcc ℤ) ∧
        ‖(∏'[symmetricIcc ℤ] m : ℤ, if m = n then 1 else (σ m - lam) / (ρ m - lam)) - 1‖ ≤ b n) ∧
        Summable (fun n => b n ^ 2) ∧ ∑' n, b n ^ 2 ≤ C := by
  have hpi := Real.pi_pos
  set M' : ℝ := max M 0 with hM'
  set K' : ℝ := max K 0 with hK'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set c' : ℝ := min c⁻¹ (Real.pi / (2 * (2 * M' + 1))) with hc'
  have hc'pos : 0 < c' := lt_min (inv_pos.mpr hc) (by positivity)
  obtain ⟨CF, hCF⟩ := hilbertGen_bdd (M' + 1) M' c' hc'pos
  set Λ : ℝ := c3Lam c K' with hΛ
  refine ⟨3 * (Λ ^ 4 * (4 * c ^ 2 * K' * (c ^ 2 * K' * invSqSum))
    + Λ ^ 2 * (CF ^ 2 * (K' / Real.pi ^ 2)) + Λ ^ 2 * ((c ^ 2 * K') ^ 2 * invSqSum)), ?_⟩
  intro σ ρ N hσ hρ _hinj hM hK hsepN
  have ha := summable_sub_sq hσ hρ
  have haK : ∑' m, ‖σ m - ρ m‖ ^ 2 ≤ K' := hK.trans (le_max_left _ _)
  obtain ⟨E, hE, hEcard, hEsum⟩ := exists_exc_set ha hc haK
  -- the good part and the `ℓ²` vector `x`
  set aG : ℤ → ℂ := fun m => if m ∈ E then 0 else σ m - ρ m with haGdef
  have haG_le : ∀ m, ‖aG m‖ ^ 2 ≤ ‖σ m - ρ m‖ ^ 2 := fun m => by
    simp only [haGdef]; split_ifs <;> simp
  have haG : Summable fun m => ‖aG m‖ ^ 2 :=
    ha.of_nonneg_of_le (fun _ => sq_nonneg _) haG_le
  have haGK : ∑' m, ‖aG m‖ ^ 2 ≤ K' := ((haG.tsum_le_tsum haG_le ha).trans haK)
  have hxs : Summable fun m => ‖aG m / (Real.pi : ℂ)‖ ^ 2 := by
    refine (haG.div_const (Real.pi ^ 2)).congr fun m => ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpi.le, div_pow]
  obtain ⟨x, hx, hxn⟩ := exists_l2_of_sq_summable hxs
  have hxn' : ‖x‖ ^ 2 ≤ K' / Real.pi ^ 2 := by
    rw [hxn]
    have : ∑' m, ‖aG m / (Real.pi : ℂ)‖ ^ 2 = (∑' m, ‖aG m‖ ^ 2) / Real.pi ^ 2 := by
      rw [← tsum_div_const]
      refine tsum_congr fun m => ?_
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpi.le, div_pow]
    rw [this]
    exact div_le_div_of_nonneg_right haGK (by positivity)
  -- the Hilbert-transform estimate for arbitrary choices of nodes
  have hsel : ∀ lamSeq : ℤ → ℂ, (∀ n : ℤ, (N : ℝ) ≤ |(n : ℝ)| → lamSeq n ∈ Dn n) →
      ∀ T : Finset ℤ, (∀ n ∈ T, (N : ℝ) ≤ |(n : ℝ)|) →
      ∑ n ∈ T, ‖c3A σ ρ E n (lamSeq n)‖ ^ 2 ≤ CF ^ 2 * (K' / Real.pi ^ 2) := by
    intro lamSeq hlam T hT
    set σ' : ℤ → ℂ := fun n => if (N : ℝ) ≤ |(n : ℝ)| then lamSeq n else padNode M' n with hσ'
    have h1 : ∀ n : ℤ, ‖σ' n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ M' + 1 := by
      intro n
      simp only [hσ']
      split_ifs with hn
      · have := hlam n hn
        have h2 : ‖lamSeq n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := by
          simpa [Dn, Metric.mem_ball, dist_eq_norm] using this
        have : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
        linarith
      · have e : padNode M' n - (n : ℂ) * (Real.pi : ℂ) = Complex.I * ((M' + 1 : ℝ) : ℂ) := by
          simp [padNode]
        rw [e, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h2 : ∀ n : ℤ, ‖ρ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ M' := fun n => (hM n).trans (le_max_left _ _)
    have h3 : ∀ m n : ℤ, m ≠ n → c' * |(m : ℝ) - n| ≤ ‖ρ m - σ' n‖ := by
      intro m n hmn
      simp only [hσ']
      split_ifs with hn
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)).trans
          (hsepN n hn m hmn _ (hlam n hn))
      · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)).trans
          (sep_pad hM'0 h2 n m hmn)
    obtain ⟨A, hA, hAx⟩ := hCF σ' ρ h1 h2 h3
    have key : ∀ n ∈ T, c3A σ ρ E n (lamSeq n) = (A x : ℤ → ℂ) n := by
      intro n hn
      rw [(hAx x n).2]
      have hP := hT n hn
      have hσn : σ' n = lamSeq n := by simp only [hσ', hP, ite_true]
      rw [hσn, ← tsum_mul_left]
      unfold c3A
      refine tsum_congr fun m => ?_
      unfold uG ratioU
      have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      rw [hx m]
      by_cases hm : m = n
      · simp [hm]
      · by_cases hmE : m ∈ E
        · simp [hm, hmE, haGdef]
        · simp only [hm, hmE, haGdef, ite_false]
          field_simp
    have hAn : ‖A x‖ ≤ CF * ‖x‖ := (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    have hCF0 : 0 ≤ CF := (norm_nonneg A).trans hA
    calc ∑ n ∈ T, ‖c3A σ ρ E n (lamSeq n)‖ ^ 2 = ∑ n ∈ T, ‖(A x : ℤ → ℂ) n‖ ^ 2 :=
          Finset.sum_congr rfl fun n hn => by rw [key n hn]
      _ ≤ ‖A x‖ ^ 2 := sum_sq_le_norm_sq (A x) T
      _ ≤ (CF * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hAn 2
      _ = CF ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ CF ^ 2 * (K' / Real.pi ^ 2) := mul_le_mul_of_nonneg_left hxn' (sq_nonneg _)
  -- the supremum over `D_n`
  set s : ℤ → ℝ := fun n => ⨆ lam : Dn n, ‖c3A σ ρ E n lam‖ with hs
  have hbdd : ∀ n : ℤ, (N : ℝ) ≤ |(n : ℝ)| →
      BddAbove (Set.range fun lam : Dn n => ‖c3A σ ρ E n lam‖) := fun n hn =>
    ⟨c3S c K', by
      rintro _ ⟨lam, rfl⟩
      exact norm_c3A_le hc ha haK (fun m hm => hsepN n hn m hm lam lam.2)⟩
  have hs0 : ∀ n, 0 ≤ s n := fun n => Real.iSup_nonneg fun _ => norm_nonneg _
  have hsup : ∀ T : Finset ℤ, (∀ n ∈ T, (N : ℝ) ≤ |(n : ℝ)|) →
      ∑ n ∈ T, s n ^ 2 ≤ CF ^ 2 * (K' / Real.pi ^ 2) := fun T hT =>
    sup_sq_le (P := fun n => (N : ℝ) ≤ |(n : ℝ)|) (D := Dn) (g := fun n lam => ‖c3A σ ρ E n lam‖)
      (B := c3S c K') (D0 := CF ^ 2 * (K' / Real.pi ^ 2))
      (fun n _ => ⟨(n : ℂ) * (Real.pi : ℂ), Metric.mem_ball_self (by positivity)⟩)
      (fun _ _ => norm_nonneg _)
      (fun n hn lam hlam => norm_c3A_le hc ha haK (fun m hm => hsepN n hn m hm lam hlam))
      hsel T hT
  -- the majorant
  set b : ℤ → ℝ := fun n => if (N : ℝ) ≤ |(n : ℝ)| then
      Λ ^ 2 * c3eX c σ ρ E n + Λ * s n + Λ * c3B c σ ρ n else 0 with hb
  have hΛ0 : 0 < Λ := c3Lam_pos c K'
  have heX0 : ∀ n, 0 ≤ c3eX c σ ρ E n := fun n =>
    Finset.sum_nonneg fun m _ => by have := c3w_nonneg n m; positivity
  have hfin : ∀ T : Finset ℤ, ∑ n ∈ T, b n ^ 2 ≤
      3 * (Λ ^ 4 * (4 * c ^ 2 * K' * (c ^ 2 * K' * invSqSum))
        + Λ ^ 2 * (CF ^ 2 * (K' / Real.pi ^ 2)) + Λ ^ 2 * ((c ^ 2 * K') ^ 2 * invSqSum)) := by
    intro T
    set T' : Finset ℤ := T.filter fun n => (N : ℝ) ≤ |(n : ℝ)| with hT'
    have hT'P : ∀ n ∈ T', (N : ℝ) ≤ |(n : ℝ)| := fun n hn => (Finset.mem_filter.mp hn).2
    have e1 : ∑ n ∈ T, b n ^ 2 = ∑ n ∈ T', b n ^ 2 := by
      rw [hT', Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hb]; split_ifs <;> simp
    rw [e1]
    have e2 : ∑ n ∈ T', b n ^ 2 = ∑ n ∈ T', (Λ ^ 2 * c3eX c σ ρ E n + Λ * s n + Λ * c3B c σ ρ n) ^ 2 :=
      Finset.sum_congr rfl fun n hn => by simp only [hb, hT'P n hn, ite_true]
    rw [e2]
    have hq : ∀ x y z : ℝ, (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := fun x y z => by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
    calc ∑ n ∈ T', (Λ ^ 2 * c3eX c σ ρ E n + Λ * s n + Λ * c3B c σ ρ n) ^ 2
        ≤ ∑ n ∈ T', 3 * (Λ ^ 4 * c3eX c σ ρ E n ^ 2 + Λ ^ 2 * s n ^ 2 + Λ ^ 2 * c3B c σ ρ n ^ 2) := by
          refine Finset.sum_le_sum fun n _ => (hq _ _ _).trans (le_of_eq ?_)
          ring
      _ = 3 * (Λ ^ 4 * ∑ n ∈ T', c3eX c σ ρ E n ^ 2 + Λ ^ 2 * ∑ n ∈ T', s n ^ 2
            + Λ ^ 2 * ∑ n ∈ T', c3B c σ ρ n ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
          have hE1 := sum_c3eX_sq_le c σ ρ E T'
          have hE2 : (E.card : ℝ) * (c ^ 2 * (∑ m ∈ E, ‖σ m - ρ m‖ ^ 2) * invSqSum)
              ≤ 4 * c ^ 2 * K' * (c ^ 2 * K' * invSqSum) := by
            have hc2 : 0 ≤ c ^ 2 * K' * invSqSum :=
              mul_nonneg (mul_nonneg (sq_nonneg _) hK'0) invSqSum_nonneg
            refine mul_le_mul hEcard ?_ (mul_nonneg (mul_nonneg (sq_nonneg _)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)) invSqSum_nonneg)
              (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hK'0)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEsum (sq_nonneg _))
              invSqSum_nonneg
          have hS := hsup T' hT'P
          have hB := sum_c3B_sq_le (c := c) ha haK T'
          gcongr
          exact hE1.trans hE2
  have hnn : ∀ n, 0 ≤ b n ^ 2 := fun n => sq_nonneg _
  refine ⟨b, ?_, summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩
  intro n hn lam hlam
  have hsep := hsepN n hn
  have hsepl : ∀ m : ℤ, m ≠ n → c⁻¹ * |(m : ℝ) - n| ≤ ‖ρ m - lam‖ := fun m hm => hsep m hm lam hlam
  obtain ⟨hmul, hbound⟩ := ratio_pointwise (E := E) hc ha haK hsepl hE
  refine ⟨hmul, ?_⟩
  have hbn : b n = Λ ^ 2 * c3eX c σ ρ E n + Λ * s n + Λ * c3B c σ ρ n := by
    simp only [hb, hn, ite_true]
  rw [hbn]
  have hle : ‖c3A σ ρ E n lam‖ ≤ s n :=
    le_ciSup (f := fun lam : Dn n => ‖c3A σ ρ E n lam‖) (hbdd n hn) ⟨lam, hlam⟩
  have := mul_le_mul_of_nonneg_left hle hΛ0.le
  exact hbound.trans (by linarith)

end

end NlsGge.GK38.Lib
