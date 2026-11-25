import QuantumNLS.HighMomentsOps
import QuantumNLS.HighMomentsCount

/-!
# PROP-008 `lem:B4-high-moments`, stage B (assembly): the `2p`-word bound
(source/chapters/propagation/spectral_calculus.tex:24-60)

`Yfull u A N` is `Y_N = Σ_{r=1}^N c_r (U_{N,r}(A_r) − a_r)` as an operator on the full completed tensor power
(`coe_Yop`: it restricts to the `Y_N` of stage A on `Sym^N`).  Expanding every factor as a weighted sum over
literal slot sets (`Yfull_eq_sum`: `Y_N = Σ_{|s|≥1} (c_{|s|}/C(N,|s|)) (Pl A s − a_{|s|})`), the product-state
expectation of a word of `m = 2p` factors is a weighted sum over tuples of slot sets; tuples with an isolated
slot set contribute `0` (`word_iso`), the others are counted by `card_noiso_le`.  Result (`word_bound`):

`|⟨u^N, Y_{B_0}⋯Y_{B_{m-1}} u^N⟩| ≤ m^m (2 S_{2m})^m / N^p`,   `S_q = Σ_r r^q ‖A_r‖`, `‖B_j r‖ ≤ ‖A r‖`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementGrouping QuantumNLS.RootOverlapCommutator QuantumNLS.RootOverlapLimit
  QuantumNLS.HighMomentsWord QuantumNLS.HighMomentsOps QuantumNLS.HighMomentsRank
  QuantumNLS.HighMomentsCount

namespace QuantumNLS.HighMomentsAssembly

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The full-tensor average `U_{N,r}(A_r)`, `0` for `r > N`. -/
def rawAvgF (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N r : ℕ) : Op H N :=
  if h : r ≤ N then rawSubsetAverage N r h (A r) else 0

/-- `Y_N` on the full completed tensor power. -/
def Yfull (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) : Op H N :=
  ∑ j ∈ Finset.range N, ((fallR N (j + 1) : ℝ) : ℂ) •
    (rawAvgF A N (j + 1) - aa u A (j + 1) • (1 : Op H N))

theorem coe_Yop (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) (x : SymSector ℂ H N) :
    ((Yop u A N x : SymSector ℂ H N) : HilbertTensorPower ℂ H N) =
      Yfull u A N (x : HilbertTensorPower ℂ H N) := by
  unfold Yop Yfull
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjN : j + 1 ≤ N := Finset.mem_range.mp hj
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, Submodule.coe_smul]
  unfold placed rawAvgF
  rw [dif_pos hjN, dif_pos hjN, Submodule.coe_sub, coe_genericU]
  simp [Submodule.coe_smul]

/-- Slot sets of cardinality `≥ 1`. -/
def S1 (N : ℕ) : Finset (Finset (Fin N)) := Finset.univ.filter (fun s => 1 ≤ s.card)

/-- The weight `c_{|s|}/C(N,|s|)` of a slot set. -/
def wt (N : ℕ) (s : Finset (Fin N)) : ℝ := fallR N s.card / (N.choose s.card : ℝ)

theorem Yfull_eq_sum (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    Yfull u A N = ∑ s ∈ S1 N, ((wt N s : ℝ) : ℂ) • Tf u A N s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Finset (Fin N) => s.card - 1)
    (t := Finset.range N) (s := S1 N) ?_]
  · unfold Yfull
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjN : j + 1 ≤ N := Finset.mem_range.mp hj
    have hfil : (S1 N).filter (fun s => s.card - 1 = j) =
        Finset.powersetCard (j + 1) (Finset.univ : Finset (Fin N)) := by
      ext s
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      omega
    refine Eq.trans ?_ (Finset.sum_congr hfil.symm (fun _ _ => rfl))
    have hC : (N.choose (j + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hjN).ne'
    have hterm : ∀ s ∈ Finset.powersetCard (j + 1) (Finset.univ : Finset (Fin N)),
        ((wt N s : ℝ) : ℂ) • Tf u A N s =
          (((fallR N (j + 1) : ℝ) : ℂ) * (N.choose (j + 1) : ℂ)⁻¹) •
            (Pl A N s - aa u A (j + 1) • (1 : Op H N)) := by
      intro s hs
      have hcard : s.card = j + 1 := (Finset.mem_powersetCard.mp hs).2
      unfold Tf wt
      rw [hcard]
      push_cast
      rw [div_eq_mul_inv]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    unfold rawAvgF
    rw [dif_pos hjN, rawAvg_eq_sum]
    have e : (((N.choose (j + 1)) • (aa u A (j + 1) • (1 : Op H N))) : Op H N) =
        ((N.choose (j + 1) : ℂ) * aa u A (j + 1)) • (1 : Op H N) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h1 : ((fallR N (j + 1) : ℝ) : ℂ) * (N.choose (j + 1) : ℂ)⁻¹ *
        ((N.choose (j + 1) : ℂ) * aa u A (j + 1)) = ((fallR N (j + 1) : ℝ) : ℂ) * aa u A (j + 1) := by
      field_simp
    rw [e, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, h1]
  · intro s hs
    simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [Finset.mem_range]
    have := hcard s
    omega

theorem wt_nonneg (N : ℕ) (s : Finset (Fin N)) (hN : 0 < N) : 0 ≤ wt N s := by
  unfold wt
  have := (fallR_bounds N hN s.card (hcard s)).1
  positivity

theorem expect_expand {m N : ℕ} (u : H) (B : Fin m → ∀ r : ℕ, BoundedSymmetricKernel H r)
    (O : Fin m → Op H N) (hO : ∀ j, O j = Yfull u (B j) N) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N), wprod m O (htpow N u)⟫_ℂ =
      ∑ s ∈ Fintype.piFinset (fun _ : Fin m => S1 N),
        (∏ j, ((wt N (s j) : ℝ) : ℂ)) *
          ⟪(htpow N u : HilbertTensorPower ℂ H N),
            wprod m (fun j => Tf u (B j) N (s j)) (htpow N u)⟫_ℂ := by
  have hO' : O = fun j => ∑ s ∈ S1 N, ((wt N s : ℝ) : ℂ) • Tf u (B j) N s := by
    funext j; rw [hO j, Yfull_eq_sum]
  rw [hO', wprod_sum (M := Op H N) m (fun _ => S1 N)
    (fun j s => ((wt N s : ℝ) : ℂ) • Tf u (B j) N s)]
  rw [ContinuousLinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [wprod_smul (R := ℂ) m (fun j => ((wt N (s j) : ℝ) : ℂ)) (fun j => Tf u (B j) N (s j))]
  simp [inner_smul_right]

theorem norm_Tf_le (u : H) (hu : ‖u‖ = 1) (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ)
    (s : Finset (Fin N)) : ‖Tf u B N s‖ ≤ 2 * ‖B s.card‖ := by
  unfold Tf
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_Pl_le B s
  have h2 : ‖(aa u B s.card) • (1 : Op H N)‖ ≤ ‖B s.card‖ := by
    refine (norm_smul_le (aa u B s.card) (1 : Op H N)).trans ?_
    have := norm_aa_le u hu B s.card
    have h3 : ‖(1 : Op H N)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc ‖aa u B s.card‖ * ‖(1 : Op H N)‖ ≤ ‖aa u B s.card‖ * 1 :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ ≤ ‖B s.card‖ := by rw [mul_one]; exact this
  linarith

theorem norm_htpow_one (u : H) (hu : ‖u‖ = 1) (N : ℕ) :
    ‖(htpow N u : HilbertTensorPower ℂ H N)‖ = 1 := by
  rw [norm_htpow, hu, one_pow]

/-- Per-tuple bound: zero if some slot set is isolated, `∏ 2‖B_j‖` otherwise. -/
theorem tuple_bound {m N : ℕ} (u : H) (hu : ‖u‖ = 1) (hm : 1 ≤ m)
    (B : Fin m → ∀ r : ℕ, BoundedSymmetricKernel H r) (s : Fin m → Finset (Fin N)) :
    ‖⟪(htpow N u : HilbertTensorPower ℂ H N),
        wprod m (fun j => Tf u (B j) N (s j)) (htpow N u)⟫_ℂ‖ ≤
      if (∀ j, ∃ i, i ≠ j ∧ (s j ∩ s i).Nonempty) then ∏ j, (2 * ‖B j (s j).card‖) else 0 := by
  split_ifs with h
  · refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_htpow_one u hu, one_mul]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_htpow_one u hu, mul_one]
    refine (wprod_norm_le m _).trans ?_
    exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => norm_Tf_le u hu (B j) N (s j))
  · push_neg at h
    obtain ⟨j, hj⟩ := h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hdis : ∀ i, i ≠ j → Disjoint (s j) (s i) := by
      intro i hi
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hj i hi
    rw [word_iso u hu B s j hdis]
    simp

/-- Fibre bound: tuples with prescribed sizes `ρ`. -/
theorem fiber_bound {m N : ℕ} (hN : 0 < N) (p : ℕ) (hm : m = 2 * p) (G : Fin m → ℕ → ℝ)
    (hG : ∀ j r, 0 ≤ G j r) (ρ : Fin m → ℕ) (hρ1 : ∀ j, 1 ≤ ρ j) (hρN : ∀ j, ρ j ≤ N) :
    ∑ s ∈ Fintype.piFinset (fun j => Finset.powersetCard (ρ j) (Finset.univ : Finset (Fin N))),
        (if (∀ j, ∃ i, i ≠ j ∧ (s j ∩ s i).Nonempty)
          then ∏ j, (G j (ρ j) / (N.choose (ρ j) : ℝ)) else 0) ≤
      (∏ j, G j (ρ j)) * (((m ^ m : ℕ) : ℝ) * ((∏ j, (ρ j : ℝ)) ^ (2 * m) / (N : ℝ) ^ p)) := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc := card_noiso_le hN p hm ρ hρ1 hρN
  have hcard : ∀ j, ((Finset.powersetCard (ρ j) (Finset.univ : Finset (Fin N))).card : ℝ) =
      (N.choose (ρ j) : ℝ) := by
    intro j
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  simp only [hcard] at hc
  have hCpos : ∀ j, (0 : ℝ) < (N.choose (ρ j) : ℝ) := fun j => by
    exact_mod_cast Nat.choose_pos (hρN j)
  have hnn : 0 ≤ ∏ j, (G j (ρ j) / (N.choose (ρ j) : ℝ)) :=
    Finset.prod_nonneg (fun j _ => div_nonneg (hG _ _) (hCpos j).le)
  calc _ = (((Fintype.piFinset (fun j => Finset.powersetCard (ρ j) (Finset.univ : Finset (Fin N)))).filter
        (fun s => ∀ j, ∃ i, i ≠ j ∧ (s j ∩ s i).Nonempty)).card : ℝ) *
        ∏ j, (G j (ρ j) / (N.choose (ρ j) : ℝ)) := rfl
    _ ≤ ((∏ j, (N.choose (ρ j) : ℝ)) * (((m ^ m : ℕ) : ℝ) *
          ((∏ j, (ρ j : ℝ)) ^ (2 * m) / (N : ℝ) ^ p))) *
        ∏ j, (G j (ρ j) / (N.choose (ρ j) : ℝ)) := mul_le_mul_of_nonneg_right hc hnn
    _ = _ := by
        rw [Finset.prod_div_distrib]
        have hne : (∏ j, (N.choose (ρ j) : ℝ)) ≠ 0 :=
          (Finset.prod_pos (fun j _ => hCpos j)).ne'
        field_simp

theorem fallR_nonneg (N r : ℕ) : 0 ≤ fallR N r := by
  unfold fallR; positivity

theorem sum_Ico_one (N : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Ico 1 (N + 1), f r = ∑ x ∈ Finset.range N, f (x + 1) := by
  have := Finset.sum_Ico_add' f 0 N 1
  rw [zero_add] at this
  rw [← this, Finset.range_eq_Ico]

/-- **`2p`-word bound.** -/
theorem word_bound {m N : ℕ} (hN : 0 < N) (p : ℕ) (hm : m = 2 * p) (hp : 1 ≤ p) (u : H)
    (hu : ‖u‖ = 1) (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (B : Fin m → ∀ r : ℕ, BoundedSymmetricKernel H r) (hB : ∀ j r, ‖B j r‖ ≤ ‖A r‖) (S : ℝ)
    (hS : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (2 * m) * ‖A (j + 1)‖) S)
    (O : Fin m → Op H N) (hO : ∀ j, O j = Yfull u (B j) N) :
    ‖⟪(htpow N u : HilbertTensorPower ℂ H N), wprod m O (htpow N u)⟫_ℂ‖ ≤
      ((m ^ m : ℕ) : ℝ) * (2 * S) ^ m / (N : ℝ) ^ p := by
  classical
  have hm1 : 1 ≤ m := by omega
  rw [expect_expand u B O hO]
  set G : Fin m → ℕ → ℝ := fun j r => fallR N r * (2 * ‖B j r‖) with hGdef
  have hG0 : ∀ j r, 0 ≤ G j r := fun j r => mul_nonneg (fallR_nonneg N r) (by positivity)
  have hCpos : ∀ (s : Finset (Fin N)), (0 : ℝ) < (N.choose s.card : ℝ) := fun s => by
    exact_mod_cast Nat.choose_pos (hcard s)
  have hstep : ∀ s ∈ Fintype.piFinset (fun _ : Fin m => S1 N),
      ‖(∏ j, ((wt N (s j) : ℝ) : ℂ)) *
          ⟪(htpow N u : HilbertTensorPower ℂ H N),
            wprod m (fun j => Tf u (B j) N (s j)) (htpow N u)⟫_ℂ‖ ≤
        (if (∀ j, ∃ i, i ≠ j ∧ (s j ∩ s i).Nonempty)
          then ∏ j, (G j (s j).card / (N.choose (s j).card : ℝ)) else 0) := by
    intro s _
    rw [norm_mul]
    have hw : ‖(∏ j, ((wt N (s j) : ℝ) : ℂ))‖ = ∏ j, wt N (s j) := by
      rw [norm_prod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Complex.norm_real, Real.norm_of_nonneg (wt_nonneg N (s j) hN)]
    rw [hw]
    have htb := tuple_bound u hu hm1 B s
    split_ifs with h
    · rw [if_pos h] at htb
      calc (∏ j, wt N (s j)) * _ ≤ (∏ j, wt N (s j)) * ∏ j, (2 * ‖B j (s j).card‖) :=
            mul_le_mul_of_nonneg_left htb (Finset.prod_nonneg (fun j _ => wt_nonneg N (s j) hN))
        _ = ∏ j, (G j (s j).card / (N.choose (s j).card : ℝ)) := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl (fun j _ => ?_)
            simp only [hGdef, wt]
            ring
    · rw [if_neg h] at htb
      have : ‖⟪(htpow N u : HilbertTensorPower ℂ H N),
            wprod m (fun j => Tf u (B j) N (s j)) (htpow N u)⟫_ℂ‖ = 0 :=
        le_antisymm htb (norm_nonneg _)
      rw [this, mul_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
  have hmaps : ∀ s ∈ Fintype.piFinset (fun _ : Fin m => S1 N),
      (fun j => (s j).card) ∈ Fintype.piFinset (fun _ : Fin m => Finset.Ico 1 (N + 1)) := by
    intro s hs
    rw [Fintype.mem_piFinset] at hs ⊢
    intro j
    have := hs j
    simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at this
    rw [Finset.mem_Ico]
    have := hcard (s j)
    omega
  have hsum : ∑ s ∈ Fintype.piFinset (fun _ : Fin m => S1 N),
      (if (∀ j, ∃ i, i ≠ j ∧ (s j ∩ s i).Nonempty)
        then ∏ j, (G j (s j).card / (N.choose (s j).card : ℝ)) else 0) =
      ∑ ρ ∈ Fintype.piFinset (fun _ : Fin m => Finset.Ico 1 (N + 1)),
        ∑ s ∈ Fintype.piFinset (fun j => Finset.powersetCard (ρ j) (Finset.univ : Finset (Fin N))),
          (if (∀ j, ∃ i, i ≠ j ∧ (s j ∩ s i).Nonempty)
            then ∏ j, (G j (ρ j) / (N.choose (ρ j) : ℝ)) else 0) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun (s : Fin m → Finset (Fin N)) j => (s j).card)
      (t := Fintype.piFinset (fun _ : Fin m => Finset.Ico 1 (N + 1)))
      (s := Fintype.piFinset (fun _ : Fin m => S1 N)) hmaps]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    rw [Fintype.mem_piFinset] at hρ
    have hfib : (Fintype.piFinset (fun _ : Fin m => S1 N)).filter
        (fun s => (fun j => (s j).card) = ρ) =
        Fintype.piFinset (fun j => Finset.powersetCard (ρ j) (Finset.univ : Finset (Fin N))) := by
      ext s
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, S1, Finset.mem_univ]
      constructor
      · rintro ⟨_, h⟩ j
        exact congrFun h j
      · intro h
        refine ⟨fun j => ?_, funext h⟩
        have := hρ j
        rw [Finset.mem_Ico] at this
        rw [h j]; exact this.1
    rw [hfib]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Fintype.mem_piFinset] at hs
    have hc : ∀ j, (s j).card = ρ j := fun j => (Finset.mem_powersetCard.mp (hs j)).2
    simp only [hc]
  rw [hsum]
  have hfiber : ∀ ρ ∈ Fintype.piFinset (fun _ : Fin m => Finset.Ico 1 (N + 1)),
      ∑ s ∈ Fintype.piFinset (fun j => Finset.powersetCard (ρ j) (Finset.univ : Finset (Fin N))),
          (if (∀ j, ∃ i, i ≠ j ∧ (s j ∩ s i).Nonempty)
            then ∏ j, (G j (ρ j) / (N.choose (ρ j) : ℝ)) else 0) ≤
        ((m ^ m : ℕ) : ℝ) / (N : ℝ) ^ p * ∏ j, (G j (ρ j) * (ρ j : ℝ) ^ (2 * m)) := by
    intro ρ hρ
    rw [Fintype.mem_piFinset] at hρ
    have h1 : ∀ j, 1 ≤ ρ j := fun j => by have := hρ j; rw [Finset.mem_Ico] at this; omega
    have h2 : ∀ j, ρ j ≤ N := fun j => by have := hρ j; rw [Finset.mem_Ico] at this; omega
    refine (fiber_bound hN p hm G hG0 ρ h1 h2).trans (le_of_eq ?_)
    have e1 : ∏ j, (G j (ρ j) * (ρ j : ℝ) ^ (2 * m)) =
        (∏ j, G j (ρ j)) * ∏ j, (ρ j : ℝ) ^ (2 * m) := Finset.prod_mul_distrib
    have e2 : (∏ j, (ρ j : ℝ)) ^ (2 * m) = ∏ j, (ρ j : ℝ) ^ (2 * m) :=
      (Finset.prod_pow _ _ _).symm
    rw [e1, e2]
    ring
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun _ : Fin m => Finset.Ico 1 (N + 1))
    (fun j r => G j r * (r : ℝ) ^ (2 * m))]
  have hcol : ∀ j, ∑ r ∈ Finset.Ico 1 (N + 1), G j r * (r : ℝ) ^ (2 * m) ≤ 2 * S := by
    intro j
    rw [sum_Ico_one]
    have hterm : ∀ x ∈ Finset.range N, G j (x + 1) * ((x + 1 : ℕ) : ℝ) ^ (2 * m) ≤
        2 * (((x + 1 : ℕ) : ℝ) ^ (2 * m) * ‖A (x + 1)‖) := by
      intro x hx
      have hxN : x + 1 ≤ N := Finset.mem_range.mp hx
      have hf1 := (fallR_bounds N hN (x + 1) hxN).2.2
      have hf0 := fallR_nonneg N (x + 1)
      have hb := hB j (x + 1)
      have hpow : (0 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) ^ (2 * m) := by positivity
      simp only [hGdef]
      calc fallR N (x + 1) * (2 * ‖B j (x + 1)‖) * ((x + 1 : ℕ) : ℝ) ^ (2 * m)
          ≤ 1 * (2 * ‖A (x + 1)‖) * ((x + 1 : ℕ) : ℝ) ^ (2 * m) := by
            gcongr
        _ = _ := by ring
    calc _ ≤ ∑ x ∈ Finset.range N, 2 * (((x + 1 : ℕ) : ℝ) ^ (2 * m) * ‖A (x + 1)‖) :=
          Finset.sum_le_sum hterm
      _ = 2 * ∑ x ∈ Finset.range N, (((x + 1 : ℕ) : ℝ) ^ (2 * m) * ‖A (x + 1)‖) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * S := by
          have := sum_le_hasSum (Finset.range N) (fun i _ => by positivity) hS
          linarith
  have hprod : ∏ j : Fin m, ∑ r ∈ Finset.Ico 1 (N + 1), G j r * (r : ℝ) ^ (2 * m) ≤ (2 * S) ^ m := by
    calc _ ≤ ∏ _j : Fin m, (2 * S) :=
          Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg (fun r _ => mul_nonneg (hG0 j r)
            (by positivity))) (fun j _ => hcol j)
      _ = (2 * S) ^ m := by simp
  have hNp : (0 : ℝ) ≤ ((m ^ m : ℕ) : ℝ) / (N : ℝ) ^ p := by positivity
  calc ((m ^ m : ℕ) : ℝ) / (N : ℝ) ^ p * ∏ j : Fin m,
        ∑ r ∈ Finset.Ico 1 (N + 1), G j r * (r : ℝ) ^ (2 * m)
      ≤ ((m ^ m : ℕ) : ℝ) / (N : ℝ) ^ p * (2 * S) ^ m := mul_le_mul_of_nonneg_left hprod hNp
    _ = _ := by ring

#print axioms word_bound
#print axioms Yfull_eq_sum
#print axioms coe_Yop

end QuantumNLS.HighMomentsAssembly
