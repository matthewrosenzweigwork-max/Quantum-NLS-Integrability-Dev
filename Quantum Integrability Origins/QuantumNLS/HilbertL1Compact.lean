import Mathlib

/-!
# R-1D98F7EC (`lem:global-Hilbert-l1-compact`): bounded maps from a Hilbert space into `ℓ¹(ℤ)`

Source: `source/chapters/global/product_torus.tex` lines 70–110 (statement and sequence-space proof).

Statement (source-literal form: `hilbert_l1_compact_complex`). Let `H` be a separable complex Hilbert space
(`source/chapters/global/product_torus.tex` line 11), regarded as a real Hilbert space by restriction of scalars.
Let `𝕜` be `ℝ` or `ℂ`. Let `S : ℕ → Finset ℤ` be increasing with every `m : ℤ` eventually in `S N` (the
"increasing finite sets exhausting ℤ"), and let `P_N` be the coordinate projection onto `S N`. For every bounded
real-linear `A : H → ℓ¹(ℤ;𝕜)`:
1. `A` is compact (`IsCompactOperator A`);
2. `‖(1 − P_N) ∘ A‖ → 0`;
3. this convergence is uniform over any norm-compact family of such operators.

Generalization (`hilbert_l1_compact`): the same three conclusions for an arbitrary real (not necessarily complex or
separable) inner-product space `E`. The separability hypothesis of the source is used there only through the
countable sequence at hand (the closed span of a bounded sequence is separable), so it is not needed.

Proof route (printed argument; the two Lean facts the source leaves to the reader are proved, not assumed):
* Schur property of `ℓ¹` (weakly null ⇒ norm null) by the printed gliding-hump block argument: §3,
  `schur_L1`, with the block estimate `block_bound`.
* Weak sequential compactness of bounded sequences in a Hilbert space (printed: "every bounded sequence ...
  has a weakly convergent subsequence"): §5, `weak_subseq`, by diagonal extraction on the sequence, a Riesz
  representation on the closed span of the sequence, and orthogonal projection. The Lean proof is for any
  complete real inner-product space, so no separable orthonormal basis is used.
* Compactness of `A` (printed "A bounded linear operator carries weak convergence to weak convergence"): §6,
  `compact_image_closedBall`, via `weak_to_functional`, `schur_L1` and the finite approximation of the image.
* (2) and (3) by finite-net arguments: §7, `tail_norm_tendsto` and `tail_family_uniform`.

No unproved placeholder declarations, no assumed Schur or weak-compactness property, no new axiom.
-/

namespace HilbertL1Compact

open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The sequence space `ℓ¹(ℤ; 𝕜)`. -/
abbrev L1 (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℤ => 𝕜) 1

/-! ## 1. Basic facts about `ℓ¹` -/

lemma L1_summable (x : L1 𝕜) : Summable (fun m => ‖(x : ℤ → 𝕜) m‖) := by
  have h := (memℓp_gen_iff (p := (1 : ENNReal)) (by simp)).mp x.2
  simpa using h

lemma L1_norm (x : L1 𝕜) : ‖x‖ = ∑' m, ‖(x : ℤ → 𝕜) m‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp) x]
  simp

/-- Restriction of `x` to a finite set `S` of coordinates (the printed `P_N`). -/
noncomputable def restrictFS (S : Finset ℤ) (x : L1 𝕜) : L1 𝕜 :=
  ⟨fun m => if m ∈ S then (x : ℤ → 𝕜) m else 0, by
    apply memℓp_gen (p := (1 : ENNReal))
    simp only [ENNReal.toReal_one, Real.rpow_one]
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (L1_summable x)
    split_ifs <;> simp⟩

lemma restrictFS_apply (S : Finset ℤ) (x : L1 𝕜) (m : ℤ) :
    (restrictFS S x : ℤ → 𝕜) m = if m ∈ S then (x : ℤ → 𝕜) m else 0 := rfl

/-- The restriction as a real-linear map. -/
noncomputable def restrictLin (S : Finset ℤ) : L1 𝕜 →ₗ[ℝ] L1 𝕜 where
  toFun := restrictFS S
  map_add' x y := by
    apply Subtype.ext
    funext m
    simp only [restrictFS_apply, lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    apply Subtype.ext
    funext m
    simp only [restrictFS_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

lemma restrictLin_apply (S : Finset ℤ) (x : L1 𝕜) : restrictLin S x = restrictFS S x := rfl

lemma restrictLin_norm_le (S : Finset ℤ) (x : L1 𝕜) : ‖restrictLin S x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul, L1_norm, L1_norm, restrictLin_apply]
  refine Summable.tsum_le_tsum (fun m => ?_) (L1_summable _) (L1_summable x)
  show ‖(restrictFS S x : ℤ → 𝕜) m‖ ≤ ‖(x : ℤ → 𝕜) m‖
  rw [restrictFS_apply]
  split_ifs <;> simp

/-- The restriction projection `P_S` as a bounded real-linear operator on `ℓ¹`, `‖P_S‖ ≤ 1`. -/
noncomputable def restrictCLM (S : Finset ℤ) : L1 𝕜 →L[ℝ] L1 𝕜 :=
  (restrictLin S).mkContinuous 1 (fun x => by simpa using restrictLin_norm_le S x)

/-- The complementary projection `1 − P_S`, the printed `(1 − P_N)`. -/
noncomputable def tailCLM (S : Finset ℤ) : L1 𝕜 →L[ℝ] L1 𝕜 :=
  ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM S

lemma tailCLM_apply_coe (S : Finset ℤ) (x : L1 𝕜) (m : ℤ) :
    (tailCLM S x : ℤ → 𝕜) m = (x : ℤ → 𝕜) m - (restrictFS S x : ℤ → 𝕜) m := by
  simp [tailCLM, restrictCLM, restrictLin_apply]

lemma tailCLM_norm_le (S : Finset ℤ) (x : L1 𝕜) : ‖tailCLM S x‖ ≤ ‖x‖ := by
  rw [L1_norm (tailCLM S x), L1_norm x]
  refine Summable.tsum_le_tsum (fun m => ?_) (L1_summable _) (L1_summable x)
  rw [tailCLM_apply_coe, restrictFS_apply]
  split_ifs <;> simp

/-- Tail mass of `x` outside `S`, as a sum over the complement subtype. -/
lemma tail_norm_eq (S : Finset ℤ) (x : L1 𝕜) :
    ∑' m, ‖(x : ℤ → 𝕜) m - (restrictFS S x : ℤ → 𝕜) m‖
      = ∑' a : ↥((S : Set ℤ)ᶜ), ‖(x : ℤ → 𝕜) a‖ := by
  have e : ∀ m : ℤ, ‖(x : ℤ → 𝕜) m - (restrictFS S x : ℤ → 𝕜) m‖
      = (((S : Set ℤ))ᶜ).indicator (fun m => ‖(x : ℤ → 𝕜) m‖) m := by
    intro m
    by_cases h : m ∈ S
    · simp [restrictFS_apply, h, Set.indicator]
    · simp [restrictFS_apply, h, Set.indicator]
  simp only [e]
  exact (tsum_subtype (((S : Set ℤ))ᶜ) (fun m => ‖(x : ℤ → 𝕜) m‖)).symm

/-- Tails of a fixed `ℓ¹` element vanish along an exhausting increasing sequence of finite sets. -/
lemma tail_tendsto (S : ℕ → Finset ℤ) (hS : Monotone S) (hexh : ∀ m : ℤ, ∃ N, m ∈ S N)
    (x : L1 𝕜) :
    Tendsto (fun N => ∑' m, ‖(x : ℤ → 𝕜) m - (restrictFS (S N) x : ℤ → 𝕜) m‖) atTop (𝓝 0) := by
  have h1 := (tendsto_tsum_compl_atTop_zero (fun m => ‖(x : ℤ → 𝕜) m‖)).comp
    (tendsto_atTop_finset_of_monotone hS hexh)
  refine h1.congr (fun N => ?_)
  simp only [Function.comp]
  rw [tail_norm_eq]
  rfl

/-- Pairing with a bounded sequence is summable. -/
lemma pair_summable {g : ℤ → 𝕜} {C : ℝ} (hg : ∀ m, ‖g m‖ ≤ C) (x : L1 𝕜) :
    Summable (fun m => g m * (x : ℤ → 𝕜) m) :=
  Summable.of_norm_bounded ((L1_summable x).mul_left C) (fun m => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hg m) (norm_nonneg _))

/-- The bounded pairing `x ↦ ∑ g_m x_m` as a real-linear functional. -/
noncomputable def pairLin {g : ℤ → 𝕜} {C : ℝ} (hg : ∀ m, ‖g m‖ ≤ C) :
    L1 𝕜 →ₗ[ℝ] 𝕜 where
  toFun x := ∑' m, g m * (x : ℤ → 𝕜) m
  map_add' x y := by
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
    exact Summable.tsum_add (pair_summable hg x) (pair_summable hg y)
  map_smul' c x := by
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, RCLike.real_smul_eq_coe_mul]
    rw [← tsum_mul_left]
    congr 1
    funext m
    ring

/-! ## 2. Elementary lemmas used in the gliding hump -/

lemma split3 {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (u : ℤ → E) (hu : Summable u)
    (s1 s2 : Finset ℤ) (h12 : s1 ⊆ s2) :
    ∑' m, u m = ∑ m ∈ s1, u m + ∑ m ∈ s2 \ s1, u m + ∑' m : ↥((s2 : Set ℤ)ᶜ), u m := by
  rw [← hu.sum_add_tsum_compl (s := s2), ← Finset.sum_sdiff h12]
  abel

lemma norm_mul_div_self (z : 𝕜) : ((‖z‖ : ℝ) : 𝕜) / z * z = ((‖z‖ : ℝ) : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz]
  · exact div_mul_cancel₀ _ hz

lemma norm_div_self_le (z : 𝕜) : ‖((‖z‖ : ℝ) : 𝕜) / z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [norm_div, RCLike.norm_ofReal, abs_norm]
    exact le_of_eq (div_self (norm_ne_zero_iff.mpr hz))

/-- **Block lower bound (printed gliding hump).** Let `Y ∈ ℓ¹`, `g` bounded by `1`, `s₁ ⊆ s₂`. If `g` is the
phase of `Y` on the block `s₂ \ s₁`, and `Y` has mass `< δ` on `s₁` and mass `< δ` outside `s₂`, and `‖Y‖ ≥ ε`,
then `‖∑ g Y‖ ≥ ε − 4δ`. -/
lemma block_bound (Y : L1 𝕜) (g : ℤ → 𝕜) (hg : ∀ m, ‖g m‖ ≤ 1) (s1 s2 : Finset ℤ) (h12 : s1 ⊆ s2)
    (hB : ∀ m ∈ s2 \ s1, g m * (Y : ℤ → 𝕜) m = ((‖(Y : ℤ → 𝕜) m‖ : ℝ) : 𝕜))
    (ε δ : ℝ) (hY : ε ≤ ‖Y‖)
    (h1 : ∑ m ∈ s1, ‖(Y : ℤ → 𝕜) m‖ < δ)
    (h2 : ∑' m : ↥((s2 : Set ℤ)ᶜ), ‖(Y : ℤ → 𝕜) m‖ < δ) :
    ε - 4 * δ ≤ ‖∑' m, g m * (Y : ℤ → 𝕜) m‖ := by
  have hfs : Summable (fun m => g m * (Y : ℤ → 𝕜) m) := pair_summable (C := 1) hg Y
  have hns : Summable (fun m => ‖(Y : ℤ → 𝕜) m‖) := L1_summable Y
  have hnf : ∀ m, ‖g m * (Y : ℤ → 𝕜) m‖ ≤ ‖(Y : ℤ → 𝕜) m‖ := fun m => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hg m)
  -- real split of ‖Y‖
  have hsplitY := split3 (fun m => ‖(Y : ℤ → 𝕜) m‖) hns s1 s2 h12
  have hYn := L1_norm Y
  simp only at hsplitY
  rw [← hYn] at hsplitY
  -- complex split of the pairing
  have hsplitF := split3 (fun m => g m * (Y : ℤ → 𝕜) m) hfs s1 s2 h12
  simp only at hsplitF
  -- block value
  have hBsum : ∑ m ∈ s2 \ s1, g m * (Y : ℤ → 𝕜) m
      = ((∑ m ∈ s2 \ s1, ‖(Y : ℤ → 𝕜) m‖ : ℝ) : 𝕜) := by
    push_cast
    exact Finset.sum_congr rfl (fun m hm => hB m hm)
  -- the three pieces
  have hA : ‖∑ m ∈ s1, g m * (Y : ℤ → 𝕜) m‖ ≤ ∑ m ∈ s1, ‖(Y : ℤ → 𝕜) m‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => hnf m)
  have hsumnorm : Summable (fun m : ↥((s2 : Set ℤ)ᶜ) => ‖g m * (Y : ℤ → 𝕜) m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hnf m) (hns.subtype _)
  have hT : ‖∑' m : ↥((s2 : Set ℤ)ᶜ), g m * (Y : ℤ → 𝕜) m‖
      ≤ ∑' m : ↥((s2 : Set ℤ)ᶜ), ‖(Y : ℤ → 𝕜) m‖ :=
    (norm_tsum_le_tsum_norm hsumnorm).trans (Summable.tsum_le_tsum (fun m => hnf m) hsumnorm
      (hns.subtype _))
  -- the real part of the total
  set A := ∑ m ∈ s1, g m * (Y : ℤ → 𝕜) m with hAdef
  set T := ∑' m : ↥((s2 : Set ℤ)ᶜ), g m * (Y : ℤ → 𝕜) m with hTdef
  set r := ∑ m ∈ s2 \ s1, ‖(Y : ℤ → 𝕜) m‖ with hrdef
  have hZ : ∑' m, g m * (Y : ℤ → 𝕜) m = A + ((r : ℝ) : 𝕜) + T := by
    rw [hsplitF, hBsum]
  have hre : r - ‖T‖ - ‖A‖ ≤ RCLike.re (∑' m, g m * (Y : ℤ → 𝕜) m) := by
    rw [hZ]
    have e : RCLike.re (A + ((r : ℝ) : 𝕜) + T) = RCLike.re A + r + RCLike.re T := by simp
    rw [e]
    have h1' := (abs_le.mp (RCLike.abs_re_le_norm A)).1
    have h2' := (abs_le.mp (RCLike.abs_re_le_norm T)).1
    linarith
  have hnorm := RCLike.re_le_norm (∑' m, g m * (Y : ℤ → 𝕜) m)
  have hr : ε - 2 * δ ≤ r := by
    have := hsplitY
    linarith
  have h1' : ‖A‖ < δ := lt_of_le_of_lt hA h1
  have h2' : ‖T‖ < δ := lt_of_le_of_lt hT h2
  have hre' : ‖∑' m, g m * (Y : ℤ → 𝕜) m‖ ≥ RCLike.re (∑' m, g m * (Y : ℤ → 𝕜) m) := hnorm
  linarith

/-! ## 3. Schur property of `ℓ¹(ℤ)` (printed gliding-hump argument) -/

/-- **Schur property, sequential form.** If `y n → 0` weakly in `ℓ¹` (tested against every bounded `g`), then
`‖y n‖ → 0`. Printed proof: otherwise choose successive elements and disjoint finite blocks so that the mass
before a block and after it is small, and the mass on the block is large; a single bounded phase function
pairs with each selected element with real part `≥ ε/2`. -/
theorem schur_L1 (y : ℕ → L1 𝕜)
    (hy : ∀ g : ℤ → 𝕜, (∀ m, ‖g m‖ ≤ 1) →
      Tendsto (fun n => ∑' m, g m * (y n : ℤ → 𝕜) m) atTop (𝓝 0)) :
    Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by
  classical
  by_contra hcon
  obtain ⟨ε, hε, hfreq⟩ : ∃ ε > 0, ∃ᶠ n in atTop, ε ≤ ‖y n‖ := by
    rw [Metric.tendsto_nhds] at hcon
    push_neg at hcon
    obtain ⟨ε, hε, h⟩ := hcon
    exact ⟨ε, hε, h.mono fun n hn => by simpa [dist_zero_right] using hn⟩
  set δ : ℝ := ε / 8 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  -- finite windows
  let S : ℕ → Finset ℤ := fun M => Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hSmono : Monotone S := fun a b hab =>
    Finset.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)
  have hSexh : ∀ m : ℤ, ∃ M, m ∈ S M := fun m => ⟨m.natAbs, by
    simp only [S, Finset.mem_Icc]
    omega⟩
  -- coordinatewise and finite-window smallness
  have hcoord : ∀ m : ℤ, Tendsto (fun n => ‖(y n : ℤ → 𝕜) m‖) atTop (𝓝 0) := by
    intro m
    have h := hy (fun k => if k = m then 1 else 0) (fun k => by split_ifs <;> simp)
    have h2 : (fun n => ∑' k, (if k = m then (1 : 𝕜) else 0) * (y n : ℤ → 𝕜) k)
        = fun n => (y n : ℤ → 𝕜) m := by
      funext n
      simp [ite_mul, tsum_ite_eq]
    rw [h2] at h
    simpa using h.norm
  have hsmall : ∀ F : Finset ℤ, ∀ d : ℝ, 0 < d → ∀ᶠ n in atTop, ∑ m ∈ F, ‖(y n : ℤ → 𝕜) m‖ < d := by
    intro F d hd
    have ht : Tendsto (fun n => ∑ m ∈ F, ‖(y n : ℤ → 𝕜) m‖) atTop (𝓝 0) := by
      have := tendsto_finset_sum F (fun m _ => hcoord m)
      simpa using this
    exact ht.eventually (gt_mem_nhds hd)
  -- one step of the construction
  have step : ∀ p : ℕ × ℕ, ∃ q : ℕ × ℕ, p.1 < q.1 ∧ p.2 < q.2 ∧ ε ≤ ‖y q.1‖ ∧
      ∑ m ∈ S p.2, ‖(y q.1 : ℤ → 𝕜) m‖ < δ ∧
      ∑' m : ↥((S q.2 : Set ℤ)ᶜ), ‖(y q.1 : ℤ → 𝕜) m‖ < δ := by
    intro p
    obtain ⟨n, hn1, hn2, hn3⟩ :=
      (hfreq.and_eventually ((hsmall (S p.2) δ hδpos).and (eventually_gt_atTop p.1))).exists
    have hT := tail_tendsto S hSmono hSexh (y n)
    obtain ⟨M, hM1, hM2⟩ :=
      ((hT.eventually (gt_mem_nhds hδpos)).and (eventually_gt_atTop p.2)).exists
    refine ⟨(n, M), hn3, hM2, hn1, hn2, ?_⟩
    show ∑' m : ↥((S M : Set ℤ)ᶜ), ‖(y n : ℤ → 𝕜) m‖ < δ
    rw [← tail_norm_eq]
    exact hM1
  choose F hF using step
  -- the iterated sequence of pairs
  let seq : ℕ → ℕ × ℕ := fun k => F^[k] (0, 0)
  have hseq : ∀ k, seq (k + 1) = F (seq k) := fun k => Function.iterate_succ_apply' F k (0, 0)
  have hseq_lt : ∀ k, (seq k).1 < (seq (k + 1)).1 ∧ (seq k).2 < (seq (k + 1)).2 := fun k => by
    rw [hseq k]
    exact ⟨(hF (seq k)).1, (hF (seq k)).2.1⟩
  let μ : ℕ → ℕ := fun k => (seq k).2
  let ν : ℕ → ℕ := fun k => (seq (k + 1)).1
  have hμ : StrictMono μ := strictMono_nat_of_lt_succ (fun k => (hseq_lt k).2)
  have hν : StrictMono ν := strictMono_nat_of_lt_succ (fun k => (hseq_lt (k + 1)).1)
  have hYa : ∀ k, ε ≤ ‖y (ν k)‖ := fun k => by
    have h := (hF (seq k)).2.2.1
    rw [← hseq k] at h
    exact h
  have hYb : ∀ k, ∑ m ∈ S (μ k), ‖(y (ν k) : ℤ → 𝕜) m‖ < δ := fun k => by
    have h := (hF (seq k)).2.2.2.1
    rw [← hseq k] at h
    exact h
  have hYc : ∀ k, ∑' m : ↥((S (μ (k + 1)) : Set ℤ)ᶜ), ‖(y (ν k) : ℤ → 𝕜) m‖ < δ := fun k => by
    have h := (hF (seq k)).2.2.2.2
    rw [← hseq k] at h
    exact h
  -- block index of each integer
  have hblock_ex : ∀ m : ℤ, ∃ j, m ∈ S (μ (j + 1)) := fun m => by
    refine ⟨m.natAbs, ?_⟩
    have hM : m.natAbs + 1 ≤ μ (m.natAbs + 1) := hμ.id_le _
    simp only [S, Finset.mem_Icc]
    omega
  let kf : ℤ → ℕ := fun m => Nat.find (hblock_ex m)
  have hkf_spec : ∀ m, m ∈ S (μ (kf m + 1)) := fun m => Nat.find_spec (hblock_ex m)
  have hkf_block : ∀ j m, m ∈ S (μ (j + 1)) → m ∉ S (μ j) → kf m = j := by
    intro j m h1 h2
    apply le_antisymm
    · exact Nat.find_min' (hblock_ex m) h1
    · by_contra hlt
      push_neg at hlt
      apply h2
      have hle : μ (kf m + 1) ≤ μ j := hμ.monotone hlt
      exact hSmono hle (hkf_spec m)
  -- the bounded phase function
  let g : ℤ → 𝕜 := fun m =>
    ((‖(y (ν (kf m)) : ℤ → 𝕜) m‖ : ℝ) : 𝕜) / (y (ν (kf m)) : ℤ → 𝕜) m
  have hg_norm : ∀ m, ‖g m‖ ≤ 1 := fun m => norm_div_self_le _
  have hg_block : ∀ j, ∀ m ∈ S (μ (j + 1)) \ S (μ j),
      g m * (y (ν j) : ℤ → 𝕜) m = ((‖(y (ν j) : ℤ → 𝕜) m‖ : ℝ) : 𝕜) := by
    intro j m hm
    rw [Finset.mem_sdiff] at hm
    have hk := hkf_block j m hm.1 hm.2
    show ((‖(y (ν (kf m)) : ℤ → 𝕜) m‖ : ℝ) : 𝕜) / (y (ν (kf m)) : ℤ → 𝕜) m
        * (y (ν j) : ℤ → 𝕜) m = _
    rw [hk]
    exact norm_mul_div_self _
  -- each selected element carries a block of real mass ≥ ε/2
  have hbound : ∀ j, ε - 4 * δ ≤ ‖∑' m, g m * (y (ν j) : ℤ → 𝕜) m‖ := fun j =>
    block_bound (y (ν j)) g hg_norm (S (μ j)) (S (μ (j + 1)))
      (Finset.le_iff_subset.mp (hSmono (hμ.monotone (Nat.le_succ j))))
      (hg_block j) ε δ (hYa j) (hYb j) (hYc j)
  -- but the pairings tend to zero along ν
  have hlim : Tendsto (fun j => ∑' m, g m * (y (ν j) : ℤ → 𝕜) m) atTop (𝓝 0) :=
    (hy g hg_norm).comp hν.tendsto_atTop
  have hev := (Metric.tendsto_nhds.mp hlim) (ε - 4 * δ) (by rw [hδdef]; linarith)
  obtain ⟨j, hj⟩ := hev.exists
  have hb := hbound j
  rw [dist_zero_right] at hj
  linarith

/-! ## 4. Bounded pairings as operators on `ℓ¹` -/

lemma pairLin_norm_le {g : ℤ → 𝕜} {C : ℝ} (hg : ∀ m, ‖g m‖ ≤ C) (hC : 0 ≤ C) (x : L1 𝕜) :
    ‖(pairLin hg : L1 𝕜 →ₗ[ℝ] 𝕜) x‖ ≤ C * ‖x‖ := by
  have hs : Summable (fun m => ‖g m * (x : ℤ → 𝕜) m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hg m) (norm_nonneg _))
      ((L1_summable x).mul_left C)
  show ‖∑' m, g m * (x : ℤ → 𝕜) m‖ ≤ C * ‖x‖
  rw [L1_norm x, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum (fun m => ?_) hs
    ((L1_summable x).mul_left C))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hg m) (norm_nonneg _)

/-- The bounded pairing as a continuous real-linear functional on `ℓ¹`. -/
noncomputable def pairCLM {g : ℤ → 𝕜} {C : ℝ} (hg : ∀ m, ‖g m‖ ≤ C) (hC : 0 ≤ C) :
    L1 𝕜 →L[ℝ] 𝕜 :=
  (pairLin hg).mkContinuous C (fun x => pairLin_norm_le hg hC x)

lemma pairCLM_apply {g : ℤ → 𝕜} {C : ℝ} (hg : ∀ m, ‖g m‖ ≤ C) (hC : 0 ≤ C) (x : L1 𝕜) :
    pairCLM hg hC x = ∑' m, g m * (x : ℤ → 𝕜) m := rfl

/-! ## 5. Weak sequential compactness of bounded sequences in a real Hilbert space -/

section Weak

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Weak subsequence (printed: "every bounded sequence ... has a weakly convergent subsequence").**
Proved without separability: diagonal extraction on the countable family `h m`, then a Riesz representation on
the closed span of the sequence, and the orthogonal decomposition. -/
theorem weak_subseq (h : ℕ → E) (R : ℝ) (hR : ∀ n, ‖h n‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : E, ∀ v : E,
      Tendsto (fun n => (inner ℝ (h (φ n)) v : ℝ)) atTop (𝓝 (inner ℝ w v)) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0)
  -- Step 1: diagonal extraction over the countable family `{h m}`
  have hx : ∀ n : ℕ, (fun m : ℕ => (inner ℝ (h n) (h m) : ℝ)) ∈
      Set.univ.pi (fun _ : ℕ => Set.Icc (-(R * R)) (R * R)) := by
    intro n m _
    have hb := abs_real_inner_le_norm (h n) (h m)
    have h1 : ‖h n‖ * ‖h m‖ ≤ R * R := mul_le_mul (hR n) (hR m) (norm_nonneg _) hR0
    exact abs_le.mp (hb.trans h1)
  obtain ⟨a, -, φ1, hφ1, hlim⟩ :=
    (isCompact_univ_pi (fun _ : ℕ => (isCompact_Icc : IsCompact (Set.Icc (-(R * R)) (R * R))))).tendsto_subseq hx
  have hdiag : ∀ m : ℕ, Tendsto (fun n => (inner ℝ (h (φ1 n)) (h m) : ℝ)) atTop (𝓝 (a m)) :=
    fun m => (tendsto_pi_nhds.mp hlim) m
  -- Step 2: convergence on the span
  have hspan : ∀ u ∈ Submodule.span ℝ (Set.range h),
      ∃ L : ℝ, Tendsto (fun n => (inner ℝ (h (φ1 n)) u : ℝ)) atTop (𝓝 L) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact ⟨a m, hdiag m⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨L1', h1⟩ := hx
      obtain ⟨L2', h2⟩ := hy
      exact ⟨L1' + L2', by simpa only [inner_add_right] using h1.add h2⟩
    | smul c x _ hx =>
      obtain ⟨L', h1⟩ := hx
      exact ⟨c * L', by simpa only [inner_smul_right] using h1.const_mul c⟩
  -- Step 3: convergence on the closure of the span (Cauchy, using the bound `R`)
  have hclos : ∀ v ∈ closure ((Submodule.span ℝ (Set.range h) : Submodule ℝ E) : Set E),
      ∃ L : ℝ, Tendsto (fun n => (inner ℝ (h (φ1 n)) v : ℝ)) atTop (𝓝 L) := by
    intro v hv
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (3 * (R + 1)) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    obtain ⟨u, hu, hvu⟩ := Metric.mem_closure_iff.mp hv δ hδpos
    obtain ⟨L, hL⟩ := hspan u hu
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hL.cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hRδ : R * δ < ε / 3 := by
      rw [hδdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    have hvu' : ‖v - u‖ ≤ δ := by rw [← dist_eq_norm]; exact hvu.le
    have key : (inner ℝ (h (φ1 m)) v : ℝ) - inner ℝ (h (φ1 n)) v
        = ((inner ℝ (h (φ1 m)) u : ℝ) - inner ℝ (h (φ1 n)) u)
          + ((inner ℝ (h (φ1 m)) (v - u) : ℝ) - inner ℝ (h (φ1 n)) (v - u)) := by
      simp only [inner_sub_right]
      ring
    have b1 := hN m hm n hn
    rw [Real.dist_eq] at b1
    have b2 : |(inner ℝ (h (φ1 m)) (v - u) : ℝ)| ≤ R * δ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hR _) hvu' (norm_nonneg _) hR0)
    have b3 : |(inner ℝ (h (φ1 n)) (v - u) : ℝ)| ≤ R * δ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hR _) hvu' (norm_nonneg _) hR0)
    rw [Real.dist_eq]
    calc |(inner ℝ (h (φ1 m)) v : ℝ) - inner ℝ (h (φ1 n)) v|
        = |((inner ℝ (h (φ1 m)) u : ℝ) - inner ℝ (h (φ1 n)) u)
            + ((inner ℝ (h (φ1 m)) (v - u) : ℝ) - inner ℝ (h (φ1 n)) (v - u))| := by rw [key]
      _ ≤ |(inner ℝ (h (φ1 m)) u : ℝ) - inner ℝ (h (φ1 n)) u|
            + |(inner ℝ (h (φ1 m)) (v - u) : ℝ) - inner ℝ (h (φ1 n)) (v - u)| := abs_add_le _ _
      _ ≤ |(inner ℝ (h (φ1 m)) u : ℝ) - inner ℝ (h (φ1 n)) u|
            + (|(inner ℝ (h (φ1 m)) (v - u) : ℝ)| + |(inner ℝ (h (φ1 n)) (v - u) : ℝ)|) := by
          gcongr
          exact abs_sub _ _
      _ < ε := by linarith
  -- Step 4: the limit functional on the closed span `K`
  let K : Submodule ℝ E := (Submodule.span ℝ (Set.range h)).topologicalClosure
  have hKcl : ∀ v ∈ K, v ∈ closure ((Submodule.span ℝ (Set.range h) : Submodule ℝ E) : Set E) := by
    intro v hv
    have e : (K : Set E) = closure ((Submodule.span ℝ (Set.range h) : Submodule ℝ E) : Set E) :=
      Submodule.topologicalClosure_coe _
    exact e ▸ hv
  haveI : CompleteSpace K := by
    haveI := Submodule.isClosed_topologicalClosure (Submodule.span ℝ (Set.range h))
    exact IsClosed.completeSpace_coe
  have hK0mem : ∀ n, h n ∈ K := fun n =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  let ψ0 : K → ℝ := fun v => Filter.limUnder atTop (fun n => (inner ℝ (h (φ1 n)) (v : E) : ℝ))
  have hψspec : ∀ v : K, Tendsto (fun n => (inner ℝ (h (φ1 n)) (v : E) : ℝ)) atTop (𝓝 (ψ0 v)) :=
    fun v => tendsto_nhds_limUnder (hclos v (hKcl v v.2))
  have hψadd : ∀ v w : K, ψ0 (v + w) = ψ0 v + ψ0 w := by
    intro v w
    have h1 := (hψspec v).add (hψspec w)
    have h2 : Tendsto (fun n => (inner ℝ (h (φ1 n)) ((v + w : K) : E) : ℝ)) atTop
        (𝓝 (ψ0 v + ψ0 w)) := by
      refine h1.congr (fun n => ?_)
      simp only [Submodule.coe_add, inner_add_right]
    exact tendsto_nhds_unique (hψspec (v + w)) h2
  have hψsmul : ∀ (c : ℝ) (v : K), ψ0 (c • v) = c * ψ0 v := by
    intro c v
    have h2 : Tendsto (fun n => (inner ℝ (h (φ1 n)) ((c • v : K) : E) : ℝ)) atTop
        (𝓝 (c * ψ0 v)) := by
      refine ((hψspec v).const_mul c).congr (fun n => ?_)
      simp only [Submodule.coe_smul, inner_smul_right]
    exact tendsto_nhds_unique (hψspec (c • v)) h2
  let ψL : K →ₗ[ℝ] ℝ :=
    { toFun := ψ0
      map_add' := hψadd
      map_smul' := fun c v => by simpa [smul_eq_mul] using hψsmul c v }
  have hψbound : ∀ v : K, ‖ψL v‖ ≤ R * ‖v‖ := by
    intro v
    have hab : |ψ0 v| ≤ R * ‖(v : E)‖ :=
      le_of_tendsto (hψspec v).abs (Eventually.of_forall fun n =>
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR _) (norm_nonneg _)))
    rw [Real.norm_eq_abs, Submodule.norm_coe] at *
    exact hab
  let ψC : K →L[ℝ] ℝ := ψL.mkContinuous R hψbound
  let hs : K := (InnerProductSpace.toDual ℝ K).symm ψC
  have hs_inner : ∀ v : K, (inner ℝ hs v : ℝ) = ψC v := fun v =>
    InnerProductSpace.toDual_symm_apply
  have hs_mem : (hs : E) ∈ K := hs.2
  -- Step 5: weak convergence for every `v ∈ E`, via the orthogonal projection onto `K`
  refine ⟨φ1, hφ1, (hs : E), fun v => ?_⟩
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  set p : E := K.starProjection v with hpdef
  have hp : p ∈ K := by
    rw [hpdef, Submodule.starProjection_apply]
    exact (K.orthogonalProjectionOnto v).2
  have hfix : ∀ u : E, u ∈ K → (inner ℝ u v : ℝ) = inner ℝ u p := by
    intro u hu
    have hperp : (inner ℝ u (v - p) : ℝ) = 0 :=
      Submodule.inner_right_of_mem_orthogonal hu (Submodule.sub_starProjection_mem_orthogonal v)
    rw [inner_sub_right] at hperp
    linarith
  have hlim_p : Tendsto (fun n => (inner ℝ (h (φ1 n)) p : ℝ)) atTop
      (𝓝 (inner ℝ (hs : E) p)) := by
    have e1 : (inner ℝ (hs : E) p : ℝ) = ψ0 ⟨p, hp⟩ :=
      ((Submodule.coe_inner K hs ⟨p, hp⟩).symm).trans (hs_inner ⟨p, hp⟩)
    rw [e1]
    exact hψspec ⟨p, hp⟩
  have hfun : (fun n => (inner ℝ (h (φ1 n)) v : ℝ)) = fun n => (inner ℝ (h (φ1 n)) p : ℝ) :=
    funext fun n => hfix _ (hK0mem (φ1 n))
  rw [hfun, hfix _ hs_mem]
  exact hlim_p

/-- **Weak-to-functional.** If `u_n ⇀ w` weakly, then `F u_n → F w` for every continuous real-linear `F : E → 𝕜`. -/
lemma weak_to_functional {u : ℕ → E} {w : E}
    (hw : ∀ v : E, Tendsto (fun n => (inner ℝ (u n) v : ℝ)) atTop (𝓝 (inner ℝ w v)))
    (F : E →L[ℝ] 𝕜) : Tendsto (fun n => F (u n)) atTop (𝓝 (F w)) := by
  have hreal : ∀ G : E →L[ℝ] ℝ, Tendsto (fun n => G (u n)) atTop (𝓝 (G w)) := by
    intro G
    have hG : ∀ x : E, G x = inner ℝ x ((InnerProductSpace.toDual ℝ E).symm G) := by
      intro x
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simp only [hG]
    exact hw _
  let G1 : E →L[ℝ] ℝ := (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).comp F
  let G2 : E →L[ℝ] ℝ := (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).comp F
  have h1 := hreal G1
  have h2 := hreal G2
  have hT := (((RCLike.continuous_ofReal (K := 𝕜)).tendsto _).comp h1).add
    ((((RCLike.continuous_ofReal (K := 𝕜)).tendsto _).comp h2).mul_const RCLike.I)
  have key : ∀ x : E, F x = ((RCLike.re (F x) : ℝ) : 𝕜) + ((RCLike.im (F x) : ℝ) : 𝕜) * RCLike.I :=
    fun x => (RCLike.re_add_im (F x)).symm
  have hfin := hT
  simp only [Function.comp, G1, G2, ContinuousLinearMap.comp_apply, RCLike.reCLM_apply,
    RCLike.imCLM_apply, RCLike.re_add_im] at hfin
  simpa only [RCLike.re_add_im] using hfin

end Weak

/-! ## 6. Compactness of bounded operators into `ℓ¹` -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Compactness of the image of bounded sets (printed: "the preceding paragraph makes its image subsequence
norm convergent").** For `A : E → ℓ¹` bounded real-linear, `closure (A '' closedBall 0 R)` is compact. -/
theorem compact_image_closedBall (A : E →L[ℝ] L1 𝕜) (R : ℝ) :
    IsCompact (closure (A '' Metric.closedBall 0 R)) := by
  apply IsSeqCompact.isCompact
  intro y hy
  have happrox : ∀ n : ℕ, ∃ u : E, ‖u‖ ≤ R ∧ dist (y n) (A u) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp (hy n) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨u, hu, rfl⟩ := hb
    exact ⟨u, mem_closedBall_zero_iff.mp hu, hd⟩
  choose u hu hd using happrox
  obtain ⟨φ, hφ, w, hw⟩ := weak_subseq u R hu
  -- the printed Schur step: the images converge in norm
  have hA : Tendsto (fun n => A (u (φ n))) atTop (𝓝 (A w)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hschur := schur_L1 (fun n => A (u (φ n)) - A w) (fun g hg => by
      let Λ : L1 𝕜 →L[ℝ] 𝕜 := pairCLM (C := 1) hg zero_le_one
      have hF := weak_to_functional (u := fun n => u (φ n)) hw (Λ.comp A)
      have e : ∀ n, ∑' m, g m * ((A (u (φ n)) - A w : L1 𝕜) : ℤ → 𝕜) m
          = (Λ.comp A) (u (φ n)) - (Λ.comp A) w := fun n =>
        map_sub Λ (A (u (φ n))) (A w)
      simp only [e]
      simpa using hF.sub_const ((Λ.comp A) w))
    exact hschur
  -- transport to the original sequence along `φ`
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝 (A w)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hd1 : Tendsto (fun n => dist (y (φ n)) (A (u (φ n)))) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat)
      exact (hd (φ n)).le.trans (one_div_le_one_div_of_le (by positivity)
        (by have := hφ.id_le n; exact_mod_cast (Nat.add_le_add_right this 1)))
    have hd2 : Tendsto (fun n => dist (A (u (φ n))) (A w)) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hA
    have hsum := hd1.add hd2
    rw [add_zero] at hsum
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hsum
    exact dist_triangle _ _ _
  exact ⟨A w, IsClosed.mem_of_tendsto isClosed_closure hyφ
      (Eventually.of_forall fun n => hy (φ n)), φ, hφ, hyφ⟩

end Compact

/-! ## 7. The three assertions of the lemma -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **(1) Compactness.** Every bounded real-linear `A : E → ℓ¹(ℤ;𝕜)` is compact (Mathlib's
`IsCompactOperator`: some compact `K` with `A⁻¹' K` a neighbourhood of `0`). -/
theorem isCompactOperator_of (A : E →L[ℝ] L1 𝕜) : IsCompactOperator A :=
  ⟨closure (A '' Metric.closedBall 0 1), compact_image_closedBall A 1,
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) one_pos)
      (fun x hx => subset_closure ⟨x, hx, rfl⟩)⟩

lemma tailCLM_norm_eq (S : Finset ℤ) (z : L1 𝕜) :
    ‖tailCLM S z‖ = ∑' m, ‖(z : ℤ → 𝕜) m - (restrictFS S z : ℤ → 𝕜) m‖ := by
  rw [L1_norm (tailCLM S z)]
  simp only [tailCLM_apply_coe]

/-- Pointwise tails of a fixed `ℓ¹` element vanish (printed: the projections converge strongly to zero). -/
lemma tail_pointwise (S : ℕ → Finset ℤ) (hS : Monotone S) (hexh : ∀ m : ℤ, ∃ N, m ∈ S N)
    (z : L1 𝕜) : Tendsto (fun N => ‖tailCLM (S N) z‖) atTop (𝓝 0) := by
  simp_rw [tailCLM_norm_eq]
  exact tail_tendsto S hS hexh z

/-- Uniform tails on a compact set of `ℓ¹` (printed: finite-net argument). -/
lemma tail_uniform_compact {K : Set (L1 𝕜)} (hK : IsCompact K) (S : ℕ → Finset ℤ) (hS : Monotone S)
    (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ z ∈ K, ‖tailCLM (S N) z‖ ≤ ε := by
  obtain ⟨t, _htK, htf, hcov⟩ := hK.finite_cover_balls (half_pos hε)
  have hev : ∀ᶠ N in atTop, ∀ z ∈ t, ‖tailCLM (S N) z‖ < ε / 2 := by
    rw [Filter.eventually_all_finite htf]
    intro z _
    exact (tail_pointwise S hS hexh z).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with N hN
  intro z hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp (hcov hz)
  rw [Metric.mem_ball, dist_eq_norm] at hzc
  have hsplit : tailCLM (S N) z = tailCLM (S N) (z - c) + tailCLM (S N) c := by
    rw [← map_add, sub_add_cancel]
  have h1 := tailCLM_norm_le (S N) (z - c)
  have h2 := hN c hc
  calc ‖tailCLM (S N) z‖ ≤ ‖tailCLM (S N) (z - c)‖ + ‖tailCLM (S N) c‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ε := by linarith

/-- Operator-norm tails on the image of the unit ball (printed: uniformity on the compact closure of `A(B)`). -/
lemma tail_comp_uniform (A : E →L[ℝ] L1 𝕜) (S : ℕ → Finset ℤ) (hS : Monotone S)
    (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ‖(tailCLM (S N)).comp A‖ ≤ ε := by
  filter_upwards [tail_uniform_compact (compact_image_closedBall A 1) S hS hexh hε] with N hN
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  rw [ContinuousLinearMap.comp_apply]
  exact hN _ (subset_closure ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩)

/-- **(2) Strong convergence of the tails, in operator norm.** For `A : E → ℓ¹` bounded, `‖(1 − P_N) A‖ → 0`
for coordinate projections `P_N` onto an increasing sequence of finite sets exhausting `ℤ`. -/
theorem tail_norm_tendsto (A : E →L[ℝ] L1 𝕜) (S : ℕ → Finset ℤ) (hS : Monotone S)
    (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) :
    Tendsto (fun N => ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [tail_comp_uniform A S hS hexh (half_pos hε)] with N hN
  have hN' : ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ ≤ ε / 2 := hN
  have hn : 0 ≤ ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  linarith

/-- **(3) Uniformity over a norm-compact family.** Finite-net argument in operator norm; the estimate is
checked pointwise on unit vectors, using the `ℓ¹` triangle inequality and `le_opNorm`. -/
theorem tail_family_uniform (𝒜 : Set (E →L[ℝ] L1 𝕜)) (hcomp : IsCompact 𝒜) (S : ℕ → Finset ℤ)
    (hS : Monotone S) (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A ∈ 𝒜,
      ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ ≤ ε := by
  intro ε hε
  obtain ⟨t, _htA, htf, hcov⟩ :=
    IsCompact.finite_cover_balls (X := E →L[ℝ] L1 𝕜) hcomp (half_pos hε)
  have hev : ∀ᶠ N in atTop, ∀ C ∈ t, ‖(tailCLM (S N)).comp C‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finite htf]
    intro C _
    exact tail_comp_uniform C S hS hexh (half_pos hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N₀, fun N hN A hA => ?_⟩
  obtain ⟨C, hC, hAC⟩ := Set.mem_iUnion₂.mp (hcov hA)
  have hdist : dist A C < ε / 2 := Metric.mem_ball.mp hAC
  have hdn := @dist_eq_norm (E →L[ℝ] L1 𝕜) _ A C
  have hAC' : ‖A - C‖ < ε / 2 := by linarith
  have hTC := hN₀ N hN C hC
  show ‖(tailCLM (S N)).comp A‖ ≤ ε
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  have hsplit : (tailCLM (S N)) (A x) = tailCLM (S N) ((A - C) x) + tailCLM (S N) (C x) := by
    rw [← map_add]
    congr 1
    rw [ContinuousLinearMap.sub_apply, sub_add_cancel]
  have h1 : ‖tailCLM (S N) ((A - C) x)‖ ≤ ‖(A - C) x‖ := tailCLM_norm_le (S N) _
  have h2 : ‖(A - C) x‖ ≤ ‖A - C‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  have h3 : ‖tailCLM (S N) (C x)‖ ≤ ‖(tailCLM (S N)).comp C‖ * ‖x‖ := by
    have := ContinuousLinearMap.le_opNorm ((tailCLM (S N)).comp C) x
    simpa using this
  rw [ContinuousLinearMap.comp_apply, hsplit]
  calc ‖tailCLM (S N) ((A - C) x) + tailCLM (S N) (C x)‖
      ≤ ‖tailCLM (S N) ((A - C) x)‖ + ‖tailCLM (S N) (C x)‖ := norm_add_le _ _
    _ ≤ ‖A - C‖ * ‖x‖ + ‖(tailCLM (S N)).comp C‖ * ‖x‖ := by linarith
    _ ≤ ε / 2 + ε / 2 := by
        rw [hx, mul_one, mul_one]
        linarith
    _ = ε := by ring

end Main

/-! ## 8. The lemma, literally -/

/-- **R-1D98F7EC (`lem:global-Hilbert-l1-compact`).** Let `E` be a real Hilbert space (`InnerProductSpace ℝ E`,
complete), `𝕜 ∈ {ℝ, ℂ}`, and `S : ℕ → Finset ℤ` increasing with every integer eventually in `S N` (the increasing
finite sets exhausting `ℤ`). Then, for bounded real-linear maps `A : E → ℓ¹(ℤ;𝕜)`:
(1) each `A` is compact; (2) `‖(1 − P_N) ∘ A‖ → 0`; (3) this convergence is uniform over any norm-compact
family of such `A`. -/
theorem hilbert_l1_compact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {𝕜 : Type*} [RCLike 𝕜] (S : ℕ → Finset ℤ) (hS : Monotone S) (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) :
    (∀ A : E →L[ℝ] L1 𝕜, IsCompactOperator A) ∧
    (∀ A : E →L[ℝ] L1 𝕜, Tendsto (fun N => ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖)
      atTop (𝓝 0)) ∧
    (∀ 𝒜 : Set (E →L[ℝ] L1 𝕜), IsCompact 𝒜 → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A ∈ 𝒜,
      ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ ≤ ε) :=
  ⟨fun A => isCompactOperator_of A,
   fun A => tail_norm_tendsto A S hS hexh,
   fun 𝒜 hcomp ε hε => tail_family_uniform 𝒜 hcomp S hS hexh ε hε⟩

/-- **R-1D98F7EC, source-literal form.** Let `H` be a separable complex Hilbert space (source line 11), regarded as
a real Hilbert space by restriction of scalars (`InnerProductSpace.complexToReal`, activated locally). Then the
three conclusions hold for every bounded real-linear `A : H → ℓ¹(ℤ;𝕜)`, `𝕜 ∈ {ℝ, ℂ}`. The separability
hypothesis is stated but not needed by the proof. -/
theorem hilbert_l1_compact_complex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {𝕜 : Type*} [RCLike 𝕜] (S : ℕ → Finset ℤ) (hS : Monotone S) (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) :
    (∀ A : H →L[ℝ] L1 𝕜, IsCompactOperator A) ∧
    (∀ A : H →L[ℝ] L1 𝕜, Tendsto (fun N => ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖)
      atTop (𝓝 0)) ∧
    (∀ 𝒜 : Set (H →L[ℝ] L1 𝕜), IsCompact 𝒜 → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A ∈ 𝒜,
      ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ ≤ ε) := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  exact hilbert_l1_compact S hS hexh

end HilbertL1Compact

#print axioms HilbertL1Compact.hilbert_l1_compact
#print axioms HilbertL1Compact.hilbert_l1_compact_complex
#print axioms HilbertL1Compact.isCompactOperator_of
#print axioms HilbertL1Compact.tail_norm_tendsto
#print axioms HilbertL1Compact.tail_family_uniform
#print axioms HilbertL1Compact.compact_image_closedBall
#print axioms HilbertL1Compact.schur_L1
#print axioms HilbertL1Compact.weak_subseq
