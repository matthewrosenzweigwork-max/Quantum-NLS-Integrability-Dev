import QuantumNLS.HaarKernelTailBounds

/-!
# R-3B18A493 QG:prop:haar-kernel-tail, Part 2: pointwise uniform tail for a fixed vector

Uses the frozen Part 1 (`HaarKernelTailBounds`, 66cbcbcf) and the frozen GridStrongSum / HilbertDiagOp modules.

Proved here:
* `pointwise_tail`: for any vector `g` and `ε > 0` there is `R₀` such that for every `R ≥ R₀` and every
  `t` with `‖t‖_∞ ≤ 1` and `t_m = 0` for `|m| ≤ R`, `‖T_r(t) g‖ ≤ ε`, where `T` is any family of strong limits
  of the symmetric partial sums. The bound is uniform in `t`.

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology Finset
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym
open QuantumNLS.GridEigen QuantumNLS.GridBounds QuantumNLS.HilbertDiagOp QuantumNLS.GridStrongSum
open QuantumNLS.HaarKernelTailBounds
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer

namespace QuantumNLS.HaarKernelTailPointwise

variable (L : ℝ) [Fact (0 < L)]

/-- The prefactor `2^{r+2}/(r! ω^r (r−1))` of the even tail bound, with `r = n+1`. -/
def tailConst (n : ℕ) : ℝ :=
  2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) * (n : ℝ))

theorem tailConst_nonneg (n : ℕ) : 0 ≤ tailConst L n := by
  have hL : (0 : ℝ) < L := Fact.out
  unfold tailConst
  apply div_nonneg (by positivity)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (div_nonneg (by positivity) hL.le) _)) (Nat.cast_nonneg _)

/-- The even tail prefactor times `(R−1)^{1−r}` is at most `tailConst/(R−1)` (for `n ≥ 1`, `R ≥ 2`). -/
theorem zeta_tail_le (n : ℕ) (hn : Odd n) (R : ℕ) (hR : 2 ≤ R) :
    tailConst L n * ((R : ℝ) - 1) ^ (1 - ((n + 1 : ℕ) : ℤ)) ≤ tailConst L n / ((R : ℝ) - 1) := by
  have hn1 : 1 ≤ n := by
    obtain ⟨j, hj⟩ := hn
    omega
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hRm : (1 : ℝ) ≤ (R : ℝ) - 1 := by linarith
  have hzp : ((R : ℝ) - 1) ^ (1 - ((n + 1 : ℕ) : ℤ)) = 1 / ((R : ℝ) - 1) ^ n := by
    rw [show (1 - ((n + 1 : ℕ) : ℤ)) = -(n : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, one_div]
  have hpow : (R : ℝ) - 1 ≤ ((R : ℝ) - 1) ^ n := by
    have := pow_le_pow_right₀ hRm hn1
    simpa using this
  have hle : 1 / ((R : ℝ) - 1) ^ n ≤ 1 / ((R : ℝ) - 1) :=
    one_div_le_one_div_of_le (by linarith) hpow
  rw [hzp]
  calc tailConst L n * (1 / ((R : ℝ) - 1) ^ n) ≤ tailConst L n * (1 / ((R : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hle (tailConst_nonneg L n)
    _ = tailConst L n / ((R : ℝ) - 1) := by ring

/-- Odd `r` (`n` even): the eigenvalue vanishes when all labels lie in `[−R, R]` and `t` vanishes there. -/
theorem odd_muGrid_zero (n : ℕ) (hn : Even n) (R : ℕ) (k : Idx (n + 1))
    (hk : ∀ j : Fin (n + 1), |k.1 j| ≤ (R : ℤ))
    (t : ℤ → ℂ) (ht0 : ∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) :
    muGrid L n t k = 0 := by
  have hterm : ∀ m : ℤ, t m * lamTilde L n k (gridPt L m) = 0 := by
    intro m
    by_cases hm : |m| ≤ (R : ℤ)
    · rw [ht0 m hm, zero_mul]
    · rw [lamTilde_grid_odd_zero L hn k m, mul_zero]
      intro i hi
      apply hm
      rw [← hi]
      exact hk i
  unfold muGrid
  simp only [hterm, tsum_zero]

set_option maxHeartbeats 1000000 in
/-- **Pointwise uniform tail.** For a fixed vector `g` and `ε > 0`, `‖T_r(t) g‖ ≤ ε` for all bounded `t`
vanishing on `|m| ≤ R`, once `R` is large (uniformly in `t`). -/
theorem pointwise_tail (n : ℕ) (T : (ℤ → ℂ) → (Hn L n →L[ℂ] Hn L n))
    (hT : ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → ∀ v,
      Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T t v)))
    (g : Hn L n) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) →
      (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) → ‖T t g‖ ≤ ε := by
  have hB0 : 0 ≤ Bd L (n + 1) := Bd_nonneg L (n + 1)
  have hpar := parseval_hasSum (physBasis L n) g
  have hsumm := hpar.summable
  set B := Bd L (n + 1) with hBdef
  set δ : ℝ := ε ^ 2 / (4 * (B ^ 2 + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set η : ℝ := ε / (2 * (‖g‖ + 1)) with hη
  have hηpos : 0 < η := by positivity
  -- a finite set carrying all but `δ` of the mass of `g`
  have hev : ∀ᶠ s : Finset (Idx (n + 1)) in atTop,
      ‖g‖ ^ 2 - δ < ∑ x ∈ s, ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 :=
    (hpar : Tendsto (fun s : Finset (Idx (n + 1)) => ∑ x ∈ s, ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2)
      atTop (𝓝 (‖g‖ ^ 2))).eventually (lt_mem_nhds (by linarith))
  obtain ⟨s, hs⟩ := hev.exists
  have hsplit := hsumm.sum_add_tsum_subtype_compl s
  rw [hpar.tsum_eq] at hsplit
  have htail : ∑' x : {x // x ∉ s}, ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 ≤ δ := by linarith
  -- label bound on `s`
  set M : ℝ := ∑ x ∈ s, ∑ j : Fin (n + 1), |(x.1 j : ℝ) + 1 / 2| with hMdef
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hMx : ∀ x ∈ s, ∀ j : Fin (n + 1), |(x.1 j : ℝ) + 1 / 2| ≤ M := by
    intro x hx j
    calc |(x.1 j : ℝ) + 1 / 2| ≤ ∑ j' : Fin (n + 1), |(x.1 j' : ℝ) + 1 / 2| :=
          Finset.single_le_sum (f := fun j' => |(x.1 j' : ℝ) + 1 / 2|)
            (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ M := Finset.single_le_sum (f := fun x' => ∑ j' : Fin (n + 1), |(x'.1 j' : ℝ) + 1 / 2|)
            (fun x' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg _)) hx
  set K : ℝ := tailConst L n with hK
  have hK0 : 0 ≤ K := tailConst_nonneg L n
  refine ⟨⌈2 * M + 2 + K / η⌉₊ + 2, fun R hR t ht ht0 => ?_⟩
  have hRreal : 2 * M + 2 + K / η ≤ (R : ℝ) := by
    have h1 := Nat.le_ceil (2 * M + 2 + K / η)
    have h2 : ((⌈2 * M + 2 + K / η⌉₊ + 2 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    push_cast at h2
    linarith
  have hKη : K / η ≤ (R : ℝ) - 1 := by linarith [hRreal, hM0]
  have hKη0 : 0 ≤ K / η := div_nonneg hK0 hηpos.le
  have hR2 : 2 * M + 1 < (R : ℝ) := by linarith [hKη0]
  have hR2n : 2 ≤ R := by
    have : (2 : ℝ) ≤ R := by linarith [hM0, hKη0]
    exact_mod_cast this
  -- every eigenvalue on `s` is at most `η`
  have hμ : ∀ x ∈ s, ‖muGrid L n t x‖ ≤ η := by
    intro x hx
    rcases Nat.even_or_odd n with hn | hn
    · have hk : ∀ j : Fin (n + 1), |x.1 j| ≤ (R : ℤ) := by
        intro j
        have h1 := abs_le.mp (hMx x hx j)
        have hRM : M + 1 / 2 ≤ (R : ℝ) := by linarith [hRreal, hKη0]
        have hz : |(x.1 j : ℝ)| ≤ (R : ℝ) :=
          abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
        exact_mod_cast hz
      rw [odd_muGrid_zero L n hn R x hk t ht0, norm_zero]
      exact hηpos.le
    · have hb := even_tail_eigen_bound L n hn x M (hMx x hx) R hR2 t ht ht0
      have hz := zeta_tail_le L n hn R hR2n
      have hKη' : tailConst L n / ((R : ℝ) - 1) ≤ η := by
        rw [div_le_iff₀ (by linarith)]
        have := (div_le_iff₀ hηpos).mp hKη
        linarith
      exact hb.trans (hz.trans hKη')
  -- Parseval for `T_r(t) g` in the basis, split at `s`
  have hTg := parseval_hasSum (physBasis L n) (T t g)
  have hcoef : ∀ x : Idx (n + 1), ‖⟪physBasis L n x, T t g⟫_ℂ‖ ^ 2 =
      ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 := by
    intro x
    rw [strong_coeff L n t ht (T t) (hT t ht) x g, norm_mul, mul_pow]
  have hTg' : HasSum (fun x : Idx (n + 1) => ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2)
      (‖T t g‖ ^ 2) := by
    have e : (fun x : Idx (n + 1) => ‖⟪physBasis L n x, T t g⟫_ℂ‖ ^ 2) =
        fun x : Idx (n + 1) => ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 := funext hcoef
    rw [← e]
    exact hTg
  have hsplitT := hTg'.summable.sum_add_tsum_subtype_compl s
  rw [hTg'.tsum_eq] at hsplitT
  have hfin : ∑ x ∈ s, ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 ≤ η ^ 2 * ‖g‖ ^ 2 := by
    calc ∑ x ∈ s, ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2
        ≤ ∑ x ∈ s, η ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 :=
          Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hμ x hx) 2) (sq_nonneg _))
      _ = η ^ 2 * ∑ x ∈ s, ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ η ^ 2 * ‖g‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_hasSum s (fun x _ => sq_nonneg _) hpar) (sq_nonneg _)
  have hsumtail : Summable (fun x : {x // x ∉ s} =>
      ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2) :=
    hTg'.summable.subtype {x | x ∉ s}
  have htailT : ∑' x : {x // x ∉ s}, ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 ≤ B ^ 2 * δ := by
    calc ∑' x : {x // x ∉ s}, ‖muGrid L n t x‖ ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2
        ≤ ∑' x : {x // x ∉ s}, B ^ 2 * ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 :=
          Summable.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (norm_muGrid_le L n t ht x) 2) (sq_nonneg _))
            hsumtail ((hsumm.subtype {x | x ∉ s}).mul_left _)
      _ = B ^ 2 * ∑' x : {x // x ∉ s}, ‖⟪physBasis L n x, g⟫_ℂ‖ ^ 2 := tsum_mul_left
      _ ≤ B ^ 2 * δ := mul_le_mul_of_nonneg_left htail (sq_nonneg _)
  -- numerical bound
  have hηg : η * (‖g‖ + 1) = ε / 2 := by
    rw [hη]
    field_simp
  have hηg2 : η * ‖g‖ ≤ ε / 2 := by
    have : η * ‖g‖ ≤ η * (‖g‖ + 1) := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg g]) hηpos.le
    linarith
  have hsq1 : η ^ 2 * ‖g‖ ^ 2 ≤ ε ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (mul_nonneg hηpos.le (norm_nonneg g)) hηg2 2
    have e : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
    have e2 : (η * ‖g‖) ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by ring
    linarith [h, e, e2]
  have hsq2 : B ^ 2 * δ ≤ ε ^ 2 / 4 := by
    have hfrac : B ^ 2 / (B ^ 2 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have e : B ^ 2 * δ = (ε ^ 2 / 4) * (B ^ 2 / (B ^ 2 + 1)) := by
      rw [hδ]
      field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity) hfrac
  have hfinal : ‖T t g‖ ^ 2 ≤ ε ^ 2 := by
    have := sq_nonneg ε
    linarith [hsplitT, hfin, htailT, hsq1, hsq2]
  exact le_of_sq_le_sq_nonneg hε.le hfinal

end QuantumNLS.HaarKernelTailPointwise

#print axioms QuantumNLS.HaarKernelTailPointwise.pointwise_tail
#print axioms QuantumNLS.HaarKernelTailPointwise.zeta_tail_le
#print axioms QuantumNLS.HaarKernelTailPointwise.odd_muGrid_zero
