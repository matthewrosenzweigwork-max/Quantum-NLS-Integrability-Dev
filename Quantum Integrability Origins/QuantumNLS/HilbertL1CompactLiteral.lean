import Mathlib
import QuantumNLS.HilbertL1Compact

/-!
# R-1D98F7EC, literal printed route: bounded maps from a Hilbert space into `ℓ¹(ℤ)`

Source: `source/chapters/global/product_torus.tex` lines 70–110 (`lem:global-Hilbert-l1-compact`).
Frozen input: `HilbertL1Compact` (`resolvent_snapshots/HilbertL1Compact_ea2db1d4.lean`), imported read-only.

Headline: `HilbertL1CompactLiteral.hilbert_l1_compact_complex_literal`. Let `H` be a separable complex Hilbert
space regarded as a real Hilbert space by restriction of scalars, `𝕜 ∈ {ℝ, ℂ}`, `S : ℕ → Finset ℤ` monotone and
exhausting `ℤ`. For bounded real-linear `A : H → ℓ¹(ℤ;𝕜)`: (1) `A` is compact; (2) `‖(1 − P_N) ∘ A‖ → 0`;
(3) this convergence is uniform over any norm-compact family of such operators.

Printed weak-subsequence step (source line 70 onward, "every bounded sequence in a separable Hilbert space has a
weakly convergent subsequence ... by diagonal extraction of its coordinates in an orthonormal basis: boundedness
makes the limiting coordinates square summable, and a finite-head and Cauchy–Schwarz tail argument gives weak
convergence to that vector"). Implemented as:
* `orthonormal_countable_of_separable`: a countable Hilbert basis exists (separability), proved by packing.
* `diag_extract`: explicit diagonal extraction of the coordinate sequences `k ↦ ⟪b (e k), h n⟫`
  (nested subsequences `T k`, diagonal `n ↦ T n n`).
* `weak_subseq_of_basis`: limiting coordinates `a i` bounded by Bessel, `∑ a_i² ≤ R²` (square summable),
  the vector `w = ∑ a_i b_i` in `E` via `HilbertBasis.repr`, and weak convergence by the finite head `F` plus the
  Cauchy–Schwarz tail `tail_bound_hasSum` (`cs_finset`, `tail_small`).
* `weak_subseq_onb`: the separable-space statement used by the compactness argument.

No Riesz representation, no closed span of the sequence, no orthogonal projection is used in this route.

Compactness (printed "a bounded linear operator carries weak convergence to weak convergence"):
`compact_image_closedBall_lit` uses `weak_subseq_onb` and the frozen Schur/gliding-hump lemma
`HilbertL1Compact.schur_L1` (reused unchanged), together with `HilbertL1Compact.weak_to_functional`.
The tail/finite-net wrappers `tailComp_uniform_lit`, `tail_norm_tendsto_lit`, `tail_family_uniform_lit` are
re-proved (same proofs as the frozen file, with the new compactness input) because the frozen wrappers reach the
old Riesz-span `HilbertL1Compact.weak_subseq`. Generic tail lemmas (`tail_uniform_compact`, `tailCLM_norm_le`)
are reused. A compile-time audit at the end checks that the headline does not reach the old chain.

No `sorry`, no `admit`, no custom axioms, no `native_decide`.
-/

namespace HilbertL1CompactLiteral

open Filter Topology HilbertL1Compact

/-! ## 0. Countable Hilbert basis in a separable space -/

/-- In a separable real inner-product space every orthonormal family is countable. Packing argument: choose
for each index a point of a countable dense set within distance `1/2`; distinct orthonormal vectors are at
distance `√2`, so the chosen points are distinct. -/
lemma orthonormal_countable_of_separable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] {ι : Type*} {v : ι → E} (hv : Orthonormal ℝ v) :
    Countable ι := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  choose f hfD hdist using fun i => hDd.exists_dist_lt (v i) (by norm_num : (0 : ℝ) < 1 / 2)
  haveI : Countable D := hDc.to_subtype
  have hinj : Function.Injective (fun i => (⟨f i, hfD i⟩ : D)) := by
    intro i j hij
    have hfe : f i = f j := congrArg Subtype.val hij
    by_contra hne
    have h0 : inner ℝ (v i) (v j) = (0 : ℝ) := hv.2 hne
    have hsq : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hv.1 i, hv.1 j, h0]
      norm_num
    have h1 : dist (v i) (f i) < 1 / 2 := hdist i
    have h2 : dist (v j) (f j) < 1 / 2 := hdist j
    have htri : dist (v i) (v j) < 1 := by
      have t1 := dist_triangle (v i) (f i) (v j)
      have t2 : dist (f i) (v j) = dist (v j) (f j) := by rw [hfe, dist_comm]
      linarith
    rw [dist_eq_norm] at htri
    nlinarith [norm_nonneg (v i - v j)]
  exact Function.Injective.countable hinj

/-! ## 1. Diagonal extraction -/

/-- **Diagonal extraction (printed: "diagonal extraction of its coordinates").** Given bounded real coordinate
sequences `c j : ℕ → ℝ` (`|c j n| ≤ R`), there is one strictly increasing `φ` along which every coordinate
sequence converges. Proof: nested Bolzano–Weierstrass subsequences `T k` (`T (k+1) = T k ∘ ψ`), diagonal
`n ↦ T n n`. -/
lemma diag_extract (c : ℕ → ℕ → ℝ) (R : ℝ) (hc : ∀ j n, |c j n| ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, ∃ a : ℝ, Tendsto (fun n => c j (φ n)) atTop (𝓝 a) := by
  have step : ∀ (τ : ℕ → ℕ) (j : ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ a : ℝ, Tendsto (fun n => c j (τ (ψ n))) atTop (𝓝 a) := by
    intro τ j
    obtain ⟨a, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (-R) R)
      (x := fun n => c j (τ n)) (fun n => abs_le.mp (hc j (τ n)))
    exact ⟨ψ, hψ, a, hlim⟩
  choose ψ hψmono hψlim using step
  obtain ⟨T, hT0, hTs⟩ : ∃ T : ℕ → ℕ → ℕ, T 0 = id ∧ ∀ k, T (k + 1) = T k ∘ ψ (T k) k :=
    ⟨fun k => Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k τ => τ ∘ ψ τ k) k, rfl, fun k => rfl⟩
  have F1 : ∀ k, StrictMono (T k) := by
    intro k
    induction k with
    | zero => rw [hT0]; exact strictMono_id
    | succ k ih => rw [hTs k]; exact ih.comp (hψmono _ _)
  have F2 : ∀ k j, j < k → ∃ a : ℝ, Tendsto (fun n => c j (T k n)) atTop (𝓝 a) := by
    intro k
    induction k with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · obtain ⟨a, ha⟩ := ih j hlt
        refine ⟨a, ?_⟩
        rw [hTs k]
        exact ha.comp (hψmono (T k) k).tendsto_atTop
      · rw [heq, hTs k]
        exact hψlim (T k) k
  have F3 : ∀ k m, k ≤ m → ∃ θ : ℕ → ℕ, StrictMono θ ∧ T m = T k ∘ θ := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ m hkm ih =>
      obtain ⟨θ, hθ, hEq⟩ := ih
      refine ⟨θ ∘ ψ (T m) m, hθ.comp (hψmono _ _), ?_⟩
      rw [hTs m, ← Function.comp_assoc, ← hEq]
  refine ⟨fun n => T n n, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    show T n n < T (n + 1) (n + 1)
    rw [hTs n]
    exact (F1 n) (lt_of_lt_of_le (Nat.lt_succ_self n) ((hψmono (T n) n).id_le (n + 1)))
  · intro j
    obtain ⟨a, ha⟩ := F2 (j + 1) j (Nat.lt_succ_self j)
    have hsub : ∀ n, j + 1 ≤ n → ∃ s, n ≤ s ∧ T n n = T (j + 1) s := by
      intro n hn
      obtain ⟨θ, hθ, hEq⟩ := F3 (j + 1) n hn
      exact ⟨θ n, hθ.id_le n, by rw [hEq]; rfl⟩
    choose! s hs1 hs2 using hsub
    have hs_tend : Tendsto s atTop atTop :=
      tendsto_atTop_mono' atTop (eventually_atTop.mpr ⟨j + 1, fun n hn => hs1 n hn⟩) tendsto_id
    refine ⟨a, ?_⟩
    have key : Tendsto (fun n => c j (T (j + 1) (s n))) atTop (𝓝 a) := ha.comp hs_tend
    refine Tendsto.congr' ?_ key
    refine eventually_atTop.mpr ⟨j + 1, fun n hn => ?_⟩
    show c j (T (j + 1) (s n)) = c j (T n n)
    rw [hs2 n hn]

/-! ## 2. Finite-head and Cauchy–Schwarz tail estimates -/

/-- Tails of a summable nonnegative family are uniformly small over finite sets disjoint from some finite `F`. -/
lemma tail_small {ι : Type*} [DecidableEq ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hs : Summable f) {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset ι, ∀ G : Finset ι, Disjoint G F → ∑ i ∈ G, f i ≤ η := by
  have hT : Tendsto (fun s : Finset ι => ∑ i ∈ s, f i) atTop (𝓝 (∑' i, f i)) := hs.hasSum
  have hev := hT.eventually (Metric.ball_mem_nhds _ (half_pos hη))
  obtain ⟨F, hF⟩ := eventually_atTop.mp hev
  refine ⟨F, fun G hG => ?_⟩
  have h1 := hF (G ∪ F) (Finset.le_iff_subset.mpr Finset.subset_union_right)
  have h2 := hF F le_rfl
  rw [Finset.sum_union hG] at h1
  rw [Real.dist_eq, abs_lt] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  linarith

/-- Finite Cauchy–Schwarz for `∑ |u_i t_i|`. -/
lemma cs_finset {ι : Type*} (G : Finset ι) (u t : ι → ℝ) {A B Y : ℝ} (hY : 0 ≤ Y)
    (hu : ∑ i ∈ G, u i ^ 2 ≤ A) (ht : ∑ i ∈ G, t i ^ 2 ≤ B) (hAB : A * B ≤ Y ^ 2) :
    ∑ i ∈ G, |u i * t i| ≤ Y := by
  have hu0 : 0 ≤ ∑ i ∈ G, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht0 : 0 ≤ ∑ i ∈ G, t i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq G (fun i => |u i|) (fun i => |t i|)
  simp only [sq_abs] at hCS
  have hX0 : 0 ≤ ∑ i ∈ G, |u i| * |t i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hprod : (∑ i ∈ G, u i ^ 2) * (∑ i ∈ G, t i ^ 2) ≤ A * B :=
    mul_le_mul hu ht ht0 (hu0.trans hu)
  have hsq : (∑ i ∈ G, |u i| * |t i|) ^ 2 ≤ Y ^ 2 := hCS.trans (hprod.trans hAB)
  have hX : ∑ i ∈ G, |u i| * |t i| ≤ Y := by nlinarith
  calc ∑ i ∈ G, |u i * t i| = ∑ i ∈ G, |u i| * |t i| :=
        Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ Y := hX

/-- Head-removed norm bound: with `F` the finite head, the norms of the tail terms have uniformly bounded
finite sums. -/
lemma head_tail_norm {ι : Type*} [DecidableEq ι] (F : Finset ι) (u t : ι → ℝ) {R η : ℝ}
    (hR0 : 0 ≤ R) (hη0 : 0 ≤ η)
    (hu : ∀ G : Finset ι, ∑ i ∈ G, u i ^ 2 ≤ 4 * R ^ 2)
    (ht : ∀ G : Finset ι, Disjoint G F → ∑ i ∈ G, t i ^ 2 ≤ η ^ 2) (G : Finset ι) :
    ∑ i ∈ G, ‖(if i ∈ F then (0 : ℝ) else u i * t i)‖ ≤ 2 * R * η := by
  have hsplit : ∑ i ∈ G, ‖(if i ∈ F then (0 : ℝ) else u i * t i)‖
      = ∑ i ∈ G.filter (fun i => i ∉ F), |u i * t i| := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ F <;> simp [hi, Real.norm_eq_abs]
  rw [hsplit]
  have hdisj : Disjoint (G.filter (fun i => i ∉ F)) F :=
    Finset.disjoint_left.mpr fun i hi hiF => (Finset.mem_filter.mp hi).2 hiF
  exact cs_finset (G.filter (fun i => i ∉ F)) u t (mul_nonneg (mul_nonneg (by norm_num) hR0) hη0)
    (hu _) (ht _ hdisj) (le_of_eq (by ring))

/-- Finite head plus Cauchy–Schwarz tail: if `∑ u_i t_i` has sum `D`, then `|D − ∑_{i∈F} u_i t_i| ≤ 2Rη`
whenever the squared `u` sums are `≤ 4R²` and the squared `t` tails outside `F` are `≤ η²`. -/
lemma tail_bound_hasSum {ι : Type*} [DecidableEq ι] {F : Finset ι} {u t : ι → ℝ} {D R η : ℝ}
    (hR0 : 0 ≤ R) (hη0 : 0 ≤ η) (hS : HasSum (fun i => u i * t i) D)
    (hu : ∀ G : Finset ι, ∑ i ∈ G, u i ^ 2 ≤ 4 * R ^ 2)
    (ht : ∀ G : Finset ι, Disjoint G F → ∑ i ∈ G, t i ^ 2 ≤ η ^ 2) :
    |D - ∑ i ∈ F, u i * t i| ≤ 2 * R * η := by
  have hH : HasSum (fun i => if i ∈ F then u i * t i else 0) (∑ i ∈ F, u i * t i) := by
    have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ι)
      (f := fun i => if i ∈ F then u i * t i else 0) (s := F) (fun i hi => if_neg hi)
    convert this using 1
    exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
  have hK : HasSum (fun i => if i ∈ F then (0 : ℝ) else u i * t i) (D - ∑ i ∈ F, u i * t i) := by
    have := hS.sub hH
    convert this using 1
    funext i
    by_cases hi : i ∈ F <;> simp [hi]
  have hkb := head_tail_norm F u t hR0 hη0 hu ht
  have hkN : Summable (fun i => ‖(if i ∈ F then (0 : ℝ) else u i * t i)‖) :=
    summable_of_sum_le (fun i => norm_nonneg _) hkb
  rw [← hK.tsum_eq, ← Real.norm_eq_abs]
  calc ‖∑' i, (if i ∈ F then (0 : ℝ) else u i * t i)‖
      ≤ ∑' i, ‖(if i ∈ F then (0 : ℝ) else u i * t i)‖ := norm_tsum_le_tsum_norm hkN
    _ ≤ 2 * R * η := tsum_le_of_sum_le' (mul_nonneg (mul_nonneg (by norm_num) hR0) hη0) hkb

/-! ## 3. Printed weak-subsequence lemma (ONB route) -/

section Weak

/-- **Weak subsequence, printed ONB route.** Given a Hilbert basis `b` (countable index), a bounded sequence
`h` has a weakly convergent subsequence. Coordinates `⟪b i, h n⟫` are diagonalized; the limits `a i` are square
summable by Bessel; `w := ∑ a_i b_i`; weak convergence by a finite head plus a Cauchy–Schwarz tail. -/
lemma weak_subseq_of_basis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℝ E) (h : ℕ → E) (R : ℝ) (hR : ∀ n, ‖h n‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : E, ∀ v : E,
      Tendsto (fun n => (inner ℝ (h (φ n)) v : ℝ)) atTop (𝓝 (inner ℝ w v)) := by
  classical
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0)
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- empty Hilbert basis: `E = {0}`
    have hz : ∀ x : E, x = 0 := fun x => (b.hasSum_repr x).unique hasSum_empty
    refine ⟨id, strictMono_id, 0, fun v => ?_⟩
    have hh : ∀ n, h n = 0 := fun n => hz (h n)
    simp only [id, hh, inner_zero_left]
    exact tendsto_const_nhds
  -- Step 1: diagonal extraction of the coordinates `k ↦ ⟪b (e k), h n⟫`
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  have hcoef_bd : ∀ k n, |(inner ℝ (b (e k)) (h n) : ℝ)| ≤ R := by
    intro k n
    have hb1 : ‖b (e k)‖ = 1 := b.orthonormal.1 (e k)
    calc |(inner ℝ (b (e k)) (h n) : ℝ)| ≤ ‖b (e k)‖ * ‖h n‖ := abs_real_inner_le_norm _ _
      _ ≤ R := by rw [hb1, one_mul]; exact hR n
  obtain ⟨φ, hφ, hlim⟩ := diag_extract (fun k n => (inner ℝ (b (e k)) (h n) : ℝ)) R hcoef_bd
  have hcoef : ∀ i, ∃ a : ℝ, Tendsto (fun n => (inner ℝ (b i) (h (φ n)) : ℝ)) atTop (𝓝 a) := by
    intro i
    obtain ⟨k, rfl⟩ := he i
    exact hlim k
  choose a ha using hcoef
  -- Step 2: Bessel bounds, and square summability of the limits
  have hR2 : ∀ n (G : Finset ι), ∑ i ∈ G, (inner ℝ (b i) (h (φ n)) : ℝ) ^ 2 ≤ R ^ 2 := by
    intro n G
    have hB := b.orthonormal.sum_inner_products_le (h (φ n)) (s := G)
    have hn : ‖h (φ n)‖ ^ 2 ≤ R ^ 2 := by
      have := hR (φ n)
      nlinarith [norm_nonneg (h (φ n))]
    calc ∑ i ∈ G, (inner ℝ (b i) (h (φ n)) : ℝ) ^ 2
        = ∑ i ∈ G, ‖(inner ℝ (b i) (h (φ n)) : ℝ)‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ‖h (φ n)‖ ^ 2 := hB
      _ ≤ R ^ 2 := hn
  have hA2 : ∀ G : Finset ι, ∑ i ∈ G, a i ^ 2 ≤ R ^ 2 := by
    intro G
    have hT : Tendsto (fun n => ∑ i ∈ G, (inner ℝ (b i) (h (φ n)) : ℝ) ^ 2) atTop
        (𝓝 (∑ i ∈ G, a i ^ 2)) :=
      tendsto_finsetSum G fun i _ => (ha i).pow 2
    exact le_of_tendsto hT (Eventually.of_forall fun n => hR2 n G)
  have hsum : Summable (fun i => a i ^ 2) :=
    summable_of_sum_le (fun i => sq_nonneg (a i)) hA2
  -- Step 3: the limit vector `w = ∑ a_i b_i` in `E`
  have hmem : Memℓp a 2 := by
    apply memℓp_gen
    simpa [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hsum
  obtain ⟨w, hw⟩ : ∃ w : E, b.repr w = ⟨a, hmem⟩ :=
    ⟨b.repr.symm ⟨a, hmem⟩, b.repr.apply_symm_apply _⟩
  have hw_coef : ∀ i, (inner ℝ (b i) w : ℝ) = a i := by
    intro i
    rw [← b.repr_apply_apply, hw]
  -- Parseval expansions
  have hPw : ∀ v : E, HasSum (fun i => a i * (inner ℝ (b i) v : ℝ)) (inner ℝ w v) := by
    intro v
    have hP := b.hasSum_inner_mul_inner w v
    convert hP using 1
    funext i
    rw [real_inner_comm (b i) w, hw_coef i]
  have hPh : ∀ (n : ℕ) (v : E),
      HasSum (fun i => (inner ℝ (b i) (h (φ n)) : ℝ) * (inner ℝ (b i) v : ℝ)) (inner ℝ (h (φ n)) v) := by
    intro n v
    have hP := b.hasSum_inner_mul_inner (h (φ n)) v
    convert hP using 1
    funext i
    rw [real_inner_comm (b i) (h (φ n))]
  have hPd : ∀ (n : ℕ) (v : E),
      HasSum (fun i => ((inner ℝ (b i) (h (φ n)) : ℝ) - a i) * (inner ℝ (b i) v : ℝ))
        (inner ℝ (h (φ n)) v - inner ℝ w v) := by
    intro n v
    have hd := (hPh n v).sub (hPw v)
    convert hd using 1
    funext i
    ring
  have hconv : ∀ i, Tendsto (fun n => (inner ℝ (b i) (h (φ n)) : ℝ) - a i) atTop (𝓝 0) := by
    intro i
    have := (ha i).sub_const (a i)
    rwa [sub_self] at this
  have hu_all : ∀ (n : ℕ) (G : Finset ι),
      ∑ i ∈ G, ((inner ℝ (b i) (h (φ n)) : ℝ) - a i) ^ 2 ≤ 4 * R ^ 2 := by
    intro n G
    calc ∑ i ∈ G, ((inner ℝ (b i) (h (φ n)) : ℝ) - a i) ^ 2
        ≤ ∑ i ∈ G, (2 * (inner ℝ (b i) (h (φ n)) : ℝ) ^ 2 + 2 * a i ^ 2) :=
          Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg ((inner ℝ (b i) (h (φ n)) : ℝ) + a i)]
      _ = 2 * ∑ i ∈ G, (inner ℝ (b i) (h (φ n)) : ℝ) ^ 2 + 2 * ∑ i ∈ G, a i ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 4 * R ^ 2 := by linarith [hR2 n G, hA2 G]
  -- Step 4: weak convergence to `w`
  refine ⟨φ, hφ, w, fun v => ?_⟩
  have hts : Summable (fun i => (inner ℝ (b i) v : ℝ) ^ 2) := by
    have := b.orthonormal.inner_products_summable v
    simpa [Real.norm_eq_abs, sq_abs] using this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (4 * (R + 1)) := ⟨_, rfl⟩
  have hden : (4 * (R + 1)) ≠ 0 := ne_of_gt (by linarith)
  have hηpos : 0 < η := by rw [hηdef]; exact div_pos hε (by linarith)
  have hη0 : 0 ≤ η := hηpos.le
  have hηkey : η * (4 * (R + 1)) = ε := by rw [hηdef, div_mul_cancel₀ ε hden]
  have h2Rη : 2 * R * η ≤ ε / 2 := by nlinarith
  obtain ⟨F, hF⟩ := tail_small (f := fun i => (inner ℝ (b i) v : ℝ) ^ 2)
    (fun i => sq_nonneg _) hts (pow_pos hηpos 2)
  have hhead : Tendsto (fun n => ∑ i ∈ F, ((inner ℝ (b i) (h (φ n)) : ℝ) - a i) * (inner ℝ (b i) v : ℝ))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum F (fun i _ => (hconv i).mul_const (inner ℝ (b i) v : ℝ))
    simpa using this
  filter_upwards [Metric.tendsto_nhds.mp hhead (ε / 2) (half_pos hε)] with n hn
  simp only [Real.dist_eq, sub_zero] at hn
  have hfin := tail_bound_hasSum (F := F) (u := fun i => (inner ℝ (b i) (h (φ n)) : ℝ) - a i)
    (t := fun i => (inner ℝ (b i) v : ℝ)) hR0 hη0 (hPd n v) (hu_all n) (fun G hG => hF G hG)
  have h3 := abs_add_le (inner ℝ (h (φ n)) v - inner ℝ w v
      - ∑ i ∈ F, ((inner ℝ (b i) (h (φ n)) : ℝ) - a i) * (inner ℝ (b i) v : ℝ))
    (∑ i ∈ F, ((inner ℝ (b i) (h (φ n)) : ℝ) - a i) * (inner ℝ (b i) v : ℝ))
  rw [sub_add_cancel] at h3
  simp only [Real.dist_eq]
  linarith

end Weak

/-- Separable real Hilbert space: a countable Hilbert basis exists and the printed ONB route applies. -/
theorem weak_subseq_onb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (h : ℕ → E) (R : ℝ) (hR : ∀ n, ‖h n‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : E, ∀ v : E,
      Tendsto (fun n => (inner ℝ (h (φ n)) v : ℝ)) atTop (𝓝 (inner ℝ w v)) := by
  obtain ⟨w0, b, -⟩ := exists_hilbertBasis ℝ E
  haveI : Countable w0 := orthonormal_countable_of_separable b.orthonormal
  exact weak_subseq_of_basis b h R hR

/-! ## 4. Compactness of bounded operators into `ℓ¹` (printed compactness step, new weak input) -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Image of a ball is relatively compact; the weak subsequence is `weak_subseq_onb`, the norm convergence of
the image subsequence is the frozen `schur_L1`. -/
theorem compact_image_closedBall_lit (A : E →L[ℝ] L1 𝕜) (R : ℝ) :
    IsCompact (closure (A '' Metric.closedBall 0 R)) := by
  apply IsSeqCompact.isCompact
  intro y hy
  have happrox : ∀ n : ℕ, ∃ u : E, ‖u‖ ≤ R ∧ dist (y n) (A u) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp (hy n) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨u, hu, rfl⟩ := hb
    exact ⟨u, mem_closedBall_zero_iff.mp hu, hd⟩
  choose u hu hd using happrox
  obtain ⟨φ, hφ, w, hw⟩ := weak_subseq_onb u R hu
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

/-- **(1) Compactness** (`IsCompactOperator`), printed route. -/
theorem isCompactOperator_lit (A : E →L[ℝ] L1 𝕜) : IsCompactOperator A :=
  ⟨closure (A '' Metric.closedBall 0 1), compact_image_closedBall_lit A 1,
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E) one_pos)
      (fun x hx => subset_closure ⟨x, hx, rfl⟩)⟩

/-- Operator-norm tails on the image of the unit ball, with the new compactness input. -/
lemma tailComp_uniform_lit (A : E →L[ℝ] L1 𝕜) (S : ℕ → Finset ℤ) (hS : Monotone S)
    (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ‖(tailCLM (S N)).comp A‖ ≤ ε := by
  filter_upwards [tail_uniform_compact (compact_image_closedBall_lit A 1) S hS hexh hε] with N hN
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  rw [ContinuousLinearMap.comp_apply]
  exact hN _ (subset_closure ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩)

/-- **(2) Strong convergence of tails in operator norm**, with the new compactness input. -/
theorem tail_norm_tendsto_lit (A : E →L[ℝ] L1 𝕜) (S : ℕ → Finset ℤ) (hS : Monotone S)
    (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) :
    Tendsto (fun N => ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [tailComp_uniform_lit A S hS hexh (half_pos hε)] with N hN
  have hN' : ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ ≤ ε / 2 := hN
  have hn : 0 ≤ ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  linarith

/-- **(3) Uniformity over a norm-compact family**, with the new compactness input. -/
theorem tail_family_uniform_lit (𝒜 : Set (E →L[ℝ] L1 𝕜)) (hcomp : IsCompact 𝒜) (S : ℕ → Finset ℤ)
    (hS : Monotone S) (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A ∈ 𝒜,
      ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ ≤ ε := by
  intro ε hε
  obtain ⟨t, _htA, htf, hcov⟩ :=
    IsCompact.finite_cover_balls (X := E →L[ℝ] L1 𝕜) hcomp (half_pos hε)
  have hev : ∀ᶠ N in atTop, ∀ C ∈ t, ‖(tailCLM (S N)).comp C‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finite htf]
    intro C _
    exact tailComp_uniform_lit C S hS hexh (half_pos hε)
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

end Compact

/-! ## 5. The headline, source-literal form -/

/-- **R-1D98F7EC, literal printed route (`lem:global-Hilbert-l1-compact`, separable complex `H`).**
Let `H` be a separable complex Hilbert space regarded as a real Hilbert space by restriction of scalars
(`InnerProductSpace.complexToReal`, activated locally). For `𝕜 ∈ {ℝ, ℂ}` and an increasing `S` exhausting `ℤ`,
every bounded real-linear `A : H → ℓ¹(ℤ;𝕜)` is compact, satisfies `‖(1 − P_N) ∘ A‖ → 0`, and this convergence is
uniform over any norm-compact family. The compactness uses the printed ONB weak-subsequence lemma
(`weak_subseq_onb`) and the frozen Schur lemma. -/
theorem hilbert_l1_compact_complex_literal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {𝕜 : Type*} [RCLike 𝕜] (S : ℕ → Finset ℤ) (hS : Monotone S) (hexh : ∀ m : ℤ, ∃ N, m ∈ S N) :
    (∀ A : H →L[ℝ] L1 𝕜, IsCompactOperator A) ∧
    (∀ A : H →L[ℝ] L1 𝕜, Tendsto (fun N => ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖)
      atTop (𝓝 0)) ∧
    (∀ 𝒜 : Set (H →L[ℝ] L1 𝕜), IsCompact 𝒜 → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A ∈ 𝒜,
      ‖(ContinuousLinearMap.id ℝ (L1 𝕜) - restrictCLM (S N)).comp A‖ ≤ ε) := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  exact ⟨fun A => isCompactOperator_lit A,
    fun A => tail_norm_tendsto_lit A S hS hexh,
    fun 𝒜 hcomp ε hε => tail_family_uniform_lit 𝒜 hcomp S hS hexh ε hε⟩

end HilbertL1CompactLiteral

/-! ## 6. Compile-time dependency audit

The headline must not reach the old Riesz-span weak subsequence `HilbertL1Compact.weak_subseq`, nor the old
compactness/tail chain that is built on it. Only constants declared in this module or in the frozen
`HilbertL1Compact` module are traversed (Mathlib cannot depend on either). A failed audit is a compile error. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let root : Name := `HilbertL1CompactLiteral.hilbert_l1_compact_complex_literal
  let forbidden : List Name :=
    [`HilbertL1Compact.weak_subseq, `HilbertL1Compact.compact_image_closedBall,
     `HilbertL1Compact.isCompactOperator_of, `HilbertL1Compact.tail_comp_uniform,
     `HilbertL1Compact.tail_norm_tendsto, `HilbertL1Compact.tail_family_uniform,
     `HilbertL1Compact.hilbert_l1_compact, `HilbertL1Compact.hilbert_l1_compact_complex]
  let isLocal (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | none => true
    | some idx =>
      ((env.header.moduleNames[idx.toNat]!).toString.splitOn "HilbertL1Compact").length > 1
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    if isLocal n then
      if let some ci := env.find? n then
        for d in ci.type.getUsedConstants do
          if !visited.contains d then
            stack := stack.push d
        if let some v := ci.value? (allowOpaque := true) then
          for d in v.getUsedConstants do
            if !visited.contains d then
              stack := stack.push d
  let hits := forbidden.filter visited.contains
  unless hits.isEmpty do
    throwError "dependency audit FAILED: headline reaches {hits}"
  let reused := [`HilbertL1Compact.schur_L1, `HilbertL1Compact.weak_to_functional,
    `HilbertL1CompactLiteral.weak_subseq_onb].filter visited.contains
  logInfo m!"dependency audit passed: headline visits {visited.size} constants; forbidden old chain hits: none; reused frozen/new lemmas reached: {reused}"

#print axioms HilbertL1CompactLiteral.hilbert_l1_compact_complex_literal
#print axioms HilbertL1CompactLiteral.weak_subseq_onb
#print axioms HilbertL1CompactLiteral.weak_subseq_of_basis
#print axioms HilbertL1CompactLiteral.diag_extract
#print axioms HilbertL1CompactLiteral.orthonormal_countable_of_separable
#print axioms HilbertL1CompactLiteral.compact_image_closedBall_lit
#print axioms HilbertL1CompactLiteral.isCompactOperator_lit
#print axioms HilbertL1CompactLiteral.tail_norm_tendsto_lit
#print axioms HilbertL1CompactLiteral.tail_family_uniform_lit
