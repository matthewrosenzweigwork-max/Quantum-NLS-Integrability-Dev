import QuantumNLS.Local013ProductSymbol
import QuantumNLS.TerraMultiRound16LocalPartial
import QuantumNLS.TerraMultiRound20VaryingTail

/-!
# LOCAL-013 `reset:principal-calculus`, stage L2: convergent families are closed under products
(`source-text/chapters/local/quantum_periods.tex:118-140`)

Source (proof of LOCAL-013): "For fixed `p,q`, `c_{N,p,q,0} → 1` and the positive-overlap
probabilities tend to zero. The limiting order-`p+q` kernel is the symmetrized tensor product, whose
diagonal symbol is the product of the two diagonal symbols. For a fixed output degree `j`, only
`p,q ≤ j` can contribute, so there are finitely many degree pairs."

The product family is the LOCAL-011 chosen product expansion
`chosenProductKernelList N (A N) (B N)` (frozen, `PlacementFiberPrefixProductExpansionLOCAL011`),
which represents `A_N B_N` and has the product radius bound.

Proved here (standard axioms only):
* `coeff_prod_eq`: for `j ≤ N`, the degree-`j` coefficient of the chosen product list is the FINITE
  sum over `p, q, s ≤ j` of `c_{N,p,q,s} K_s(A_{p,N}, B_{q,N})` with union degree `j`.
* `tendsto_coeff_prod`: each degree-`j` coefficient converges in operator norm to
  `prodLim Alim Blim j = Σ_{p+q=j} K₀(A_p, B_q)` (zero-overlap terms tend to the symmetrized
  product, positive-overlap terms to zero: TerraMulti round-20/21 varying-input limits).
* `product_converges`: closure of DEF-042 convergence under products on the same radius `R ≥ 1`,
  with the represented operator `A_N B_N` and the product symbol on `‖v‖² ≤ R`.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace BigOperators
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementProduct QuantumNLS.KernelConvergence QuantumNLS.LocalPlacement
  QuantumNLS.PlacementFiberPrefixAlignedTransport QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011 QuantumNLS.Local013ProductSymbol

namespace QuantumNLS.Local013ProductLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Finite reindexing -/

/-- Reindexing an injectively labelled finite sum as a sum over a finset of labels, when all the
omitted terms vanish. -/
theorem sum_comp_inj {ι E : Type*} [Fintype ι] [AddCommMonoid E] (e : ι → ℕ)
    (he : Function.Injective e) (f : ℕ → E) (S : Finset ℕ)
    (h1 : ∀ i, e i ∉ S → f (e i) = 0) (h2 : ∀ n ∈ S, (∀ i, e i ≠ n) → f n = 0) :
    ∑ i, f (e i) = ∑ n ∈ S, f n := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := f) (fun x _ y _ hxy => he hxy)]
  have hA : ∑ n ∈ Finset.univ.image e, f n = ∑ n ∈ Finset.univ.image e ∪ S, f n := by
    apply Finset.sum_subset Finset.subset_union_left
    intro n hn hnot
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hn with h | h
      · exact absurd h hnot
      · exact h
    apply h2 n hnS
    intro i hi
    apply hnot
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hB : ∑ n ∈ S, f n = ∑ n ∈ Finset.univ.image e ∪ S, f n := by
    apply Finset.sum_subset Finset.subset_union_right
    intro n hn hnot
    rcases Finset.mem_union.mp hn with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact h1 i hnot
    · exact absurd h hnot
  rw [hA, hB]

/-! ### The degree-`j` coefficient of the chosen product list -/

theorem coeffAt_self (A : ∀ N : ℕ, KernelList (H := H) N) (N : ℕ) (p : Fin (N + 1)) :
    coeffAt A N p.1 = A N p := by
  unfold coeffAt
  rw [dif_pos (Nat.lt_succ_iff.mp p.2)]

/-- The `(p,q,s)` contribution to the degree-`j` coefficient at total number `N`. -/
def prodTerm (A B : ∀ N : ℕ, KernelList (H := H) N) (j N p q s : ℕ) :
    BoundedSymmetricKernel H j :=
  if h : s ≤ p ∧ s ≤ q ∧ unionSize p q s = j then
    castSymSectorOperator h.2.2
      (((overlapCoefficient N p q s : ℝ) : ℂ) •
        averagedOverlapKernel h.1 h.2.1 (coeffAt A N p) (coeffAt B N q))
  else 0

theorem le_unionSize_left (p q s : ℕ) : p ≤ unionSize p q s := by
  unfold unionSize; omega

theorem le_unionSize_right (p q s : ℕ) (hs : s ≤ p) : q ≤ unionSize p q s := by
  unfold unionSize; omega

theorem prodTerm_eq_zero {A B : ∀ N : ℕ, KernelList (H := H) N} {j N p q s : ℕ}
    (h : ¬ (s ≤ p ∧ s ≤ q ∧ unionSize p q s = j)) : prodTerm A B j N p q s = 0 := by
  unfold prodTerm
  rw [dif_neg h]

theorem overlapProductKernelTerm_apply (A B : ∀ N : ℕ, KernelList (H := H) N) (N j : ℕ)
    (hj : j < N + 1) (p q : Fin (N + 1)) (s : FeasibleOverlapIndex N p.1 q.1) :
    overlapProductKernelTerm (A N) (B N) p q s ⟨j, hj⟩ = prodTerm A B j N p.1 q.1 s.1.1 := by
  have hsp : s.1.1 ≤ p.1 := le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _)
  have hsq : s.1.1 ≤ q.1 := le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)
  unfold overlapProductKernelTerm kernelSpike prodTerm
  by_cases h : j = unionSize p.1 q.1 s.1.1
  · rw [dif_pos h, dif_pos ⟨hsp, hsq, h.symm⟩, coeffAt_self, coeffAt_self]
  · rw [dif_neg h, dif_neg (fun h' => h h'.2.2.symm)]

theorem coeff_prod_eq (A B : ∀ N : ℕ, KernelList (H := H) N) {j N : ℕ} (hjN : j ≤ N) :
    coeffAt (fun N => chosenProductKernelList N (A N) (B N)) N j =
      ∑ p ∈ range (j + 1), ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1),
        prodTerm A B j N p q s := by
  unfold coeffAt
  rw [dif_pos hjN]
  unfold chosenProductKernelList
  simp only [Finset.sum_apply]
  have hs : ∀ p q : Fin (N + 1),
      ∑ s : FeasibleOverlapIndex N p.1 q.1,
          overlapProductKernelTerm (A N) (B N) p q s ⟨j, Nat.lt_succ_of_le hjN⟩ =
        ∑ s ∈ range (j + 1), prodTerm A B j N p.1 q.1 s := by
    intro p q
    simp only [overlapProductKernelTerm_apply]
    apply sum_comp_inj (fun s : FeasibleOverlapIndex N p.1 q.1 => s.1.1)
    · intro a b hab
      exact Subtype.ext (Fin.ext hab)
    · intro s hs
      apply prodTerm_eq_zero
      rintro ⟨h1, _, h3⟩
      have := le_unionSize_left p.1 q.1 s.1.1
      simp only [Finset.mem_range] at hs
      omega
    · intro n hn hnot
      apply prodTerm_eq_zero
      rintro ⟨h1, h2, h3⟩
      exact hnot ⟨⟨n, Nat.lt_succ_of_le (le_min h1 h2)⟩, by show unionSize p.1 q.1 n ≤ N; rw [h3]; exact hjN⟩ rfl
  simp only [hs]
  have hq : ∀ p : Fin (N + 1),
      ∑ q : Fin (N + 1), ∑ s ∈ range (j + 1), prodTerm A B j N p.1 q.1 s =
        ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1), prodTerm A B j N p.1 q s := by
    intro p
    apply sum_comp_inj (fun q : Fin (N + 1) => q.1) Fin.val_injective
      (fun q => ∑ s ∈ range (j + 1), prodTerm A B j N p.1 q s)
    · intro q hq
      apply Finset.sum_eq_zero
      intro s hs
      apply prodTerm_eq_zero
      rintro ⟨h1, _, h3⟩
      have := le_unionSize_right p.1 q.1 s h1
      simp only [Finset.mem_range] at hq
      omega
    · intro n hn hnot
      exact absurd rfl (hnot ⟨n, by simp only [Finset.mem_range] at hn; omega⟩)
  simp only [hq]
  apply sum_comp_inj (fun p : Fin (N + 1) => p.1) Fin.val_injective
    (fun p => ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1), prodTerm A B j N p q s)
  · intro p hp
    apply Finset.sum_eq_zero
    intro q _
    apply Finset.sum_eq_zero
    intro s _
    apply prodTerm_eq_zero
    rintro ⟨_, _, h3⟩
    have := le_unionSize_left p.1 q s
    simp only [Finset.mem_range] at hp
    omega
  · intro n hn hnot
    exact absurd rfl (hnot ⟨n, by simp only [Finset.mem_range] at hn; omega⟩)

/-! ### Fixed-degree limits -/

theorem zero_smul_kernel {n : ℕ} (K : BoundedSymmetricKernel H n) : (0 : ℂ) • K = 0 := by
  ext x
  simp

theorem tendsto_cast {m n : ℕ} (h : m = n) {f : ℕ → BoundedSymmetricKernel H m}
    {L : BoundedSymmetricKernel H m} (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun N => castSymSectorOperator h (f N)) atTop (𝓝 (castSymSectorOperator h L)) := by
  subst h; exact hf

theorem cast_zero {m n : ℕ} (h : m = n) :
    castSymSectorOperator h (0 : BoundedSymmetricKernel H m) = 0 := by
  subst h; rfl

/-- The limit of the `(p,q,s)` contribution: the zero-overlap kernel for `s = 0`, zero otherwise. -/
def prodTermLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j p q s : ℕ) :
    BoundedSymmetricKernel H j :=
  if h : s ≤ p ∧ s ≤ q ∧ unionSize p q s = j then
    castSymSectorOperator h.2.2
      ((if s = 0 then (1 : ℂ) else 0) • averagedOverlapKernel h.1 h.2.1 (Alim p) (Blim q))
  else 0

theorem tendsto_prodTerm (A B : ∀ N : ℕ, KernelList (H := H) N)
    (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p)
    (hA : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0))
    (hB : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt B N p - Blim p‖) atTop (𝓝 0))
    (j p q s : ℕ) :
    Tendsto (fun N => prodTerm A B j N p q s) atTop (𝓝 (prodTermLim Alim Blim j p q s)) := by
  unfold prodTerm prodTermLim
  by_cases h : s ≤ p ∧ s ≤ q ∧ unionSize p q s = j
  · simp only [dif_pos h]
    apply tendsto_cast
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      rw [if_pos rfl, one_smul]
      exact QuantumNLS.TerraMultiRound21VaryingSurvivors.varying_zero_overlap_term_limit p q
        (fun N => coeffAt A N p) (fun N => coeffAt B N q) (Alim p) (Blim q) (hA p) (hB q)
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hs), zero_smul_kernel]
      exact QuantumNLS.TerraMultiRound20VaryingTail.varying_positive_overlap_limit p q s hs h.1
        h.2.1 (fun N => coeffAt A N p) (fun N => coeffAt B N q) (Alim p) (Blim q) (hA p) (hB q)
  · simp only [dif_neg h]
    exact tendsto_const_nhds

theorem sum_prodTermLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j : ℕ) :
    ∑ p ∈ range (j + 1), ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1),
      prodTermLim Alim Blim j p q s = prodLim Alim Blim j := by
  unfold prodLim
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : p ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  rw [Finset.sum_eq_single (j - p)]
  · rw [Finset.sum_eq_single 0]
    · unfold prodTermLim zeroTerm
      rw [dif_pos ⟨Nat.zero_le p, Nat.zero_le _, unionSize_zero_sub j p hpj⟩, dif_pos hpj,
        if_pos rfl, one_smul]
    · intro s _ hs
      unfold prodTermLim
      by_cases h : s ≤ p ∧ s ≤ j - p ∧ unionSize p (j - p) s = j
      · rw [dif_pos h, if_neg hs]
        rw [zero_smul_kernel, cast_zero]
      · rw [dif_neg h]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos j)) h
  · intro q _ hq
    apply Finset.sum_eq_zero
    intro s _
    unfold prodTermLim
    by_cases h : s ≤ p ∧ s ≤ q ∧ unionSize p q s = j
    · rw [dif_pos h]
      rcases eq_or_ne s 0 with hs | hs
      · exfalso
        apply hq
        have h3 := h.2.2
        rw [hs] at h3
        unfold unionSize at h3
        omega
      · rw [if_neg hs]
        rw [zero_smul_kernel, cast_zero]
    · rw [dif_neg h]
  · intro h
    exfalso
    apply h
    simp only [Finset.mem_range]
    omega

/-- **Fixed-degree coefficient limit of products**: `A_{•,N} B_{•,N}` has degree-`j` coefficient
converging in operator norm to `Σ_{p+q=j} K₀(A_p, B_q)`. -/
theorem tendsto_coeff_prod (A B : ∀ N : ℕ, KernelList (H := H) N)
    (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p)
    (hA : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0))
    (hB : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt B N p - Blim p‖) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun N => coeffAt (fun N => chosenProductKernelList N (A N) (B N)) N j) atTop
      (𝓝 (prodLim Alim Blim j)) := by
  rw [← sum_prodTermLim]
  have hlim := tendsto_finset_sum (range (j + 1)) fun p _ =>
    tendsto_finset_sum (range (j + 1)) fun q _ =>
      tendsto_finset_sum (range (j + 1)) fun s _ =>
        tendsto_prodTerm A B Alim Blim hA hB j p q s
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop j] with N hN
  exact (coeff_prod_eq A B hN).symm

set_option maxHeartbeats 1000000 in
/-- **LOCAL-013, product clause.** DEF-042 convergent families on a radius `R ≥ 1` are closed
under products: the LOCAL-011 chosen product expansions represent `A_N B_N`, converge on the same
radius with limiting kernels `prodLim Alim Blim`, and the product has the product symbol on
`‖v‖² ≤ R`. -/
theorem product_converges {R : ℝ} (hR : 1 ≤ R) {A B : ∀ N : ℕ, KernelList (H := H) N}
    {Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius R A Alim) (hB : ConvergesOnRadius R B Blim) :
    ConvergesOnRadius R (fun N => chosenProductKernelList N (A N) (B N)) (prodLim Alim Blim) ∧
      (∀ N, QuantumNLS.RadiusBound.represented (chosenProductKernelList N (A N) (B N)) =
        (QuantumNLS.RadiusBound.represented (A N)).comp
          (QuantumNLS.RadiusBound.represented (B N))) ∧
      ∀ v : H, ‖v‖ ^ 2 ≤ R → symbol (prodLim Alim Blim) v = symbol Alim v * symbol Blim v := by
  have hu := QuantumNLS.TerraMultiRound16LocalPartial.chosen_products_uniformly_bounded hR hA hB
  have hR0 : (0 : ℝ) ≤ R := by linarith
  refine ⟨⟨hu.2, fun j => ?_⟩, hu.1, fun v hv => symbol_prodLim_of_converges hR0 hA hB v hv⟩
  have h := tendsto_coeff_prod A B Alim Blim hA.2 hB.2 j
  exact (tendsto_iff_norm_sub_tendsto_zero (E := BoundedSymmetricKernel H j)).mp h

end QuantumNLS.Local013ProductLimit

#print axioms QuantumNLS.Local013ProductLimit.sum_comp_inj
#print axioms QuantumNLS.Local013ProductLimit.coeff_prod_eq
#print axioms QuantumNLS.Local013ProductLimit.tendsto_prodTerm
#print axioms QuantumNLS.Local013ProductLimit.sum_prodTermLim
#print axioms QuantumNLS.Local013ProductLimit.tendsto_coeff_prod
#print axioms QuantumNLS.Local013ProductLimit.product_converges
