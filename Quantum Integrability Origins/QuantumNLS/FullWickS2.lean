import QuantumNLS.FullWickH4

/-! FullWickS2 (sonnet_fourier, R-140AE34B `thm:full-wick`, Stage 3, ITEM 3 consumer interface).

Printed source: wick_calculus.tex lines 182-186: "Each fixed Wick monomial is an ordered product of
Cartesian generators plus a bounded `O(N^{-1})` error."  Together with the comparison of FullWickS1
(`‖E-word − W(monomial)‖ ≤ C/N`) this module transfers the time-indexed uniform strong symbol of
`FullWickH4.HasUniformStrongT` / `HasUniformPairT`

  (1) from an operator `B` to an operator `A` with `‖A_N − B_N‖ ≤ K/N` (eventually), on preparations
      of uniformly bounded norm (`hasUniformStrongT_of_opClose`, `hasUniformPairT_of_opClose`);
  (2) to a finite linear combination `Σ_k c_k A_k` with symbol `Σ_k c_k a_k`
      (`hasUniformStrongT_sum`, `hasUniformPairT_sum`; companion `Σ_k conj(c_k) A'_k`);
  (3) to both at once (`hasUniformStrongT_of_sum_opClose`, `hasUniformPairT_of_sum_opClose`), which is the
      shape needed for the strong symbol of `W(f) = Σ_p f_p W(z^{α_p} z̄^{β_p})`
      (via `FullWickS1.balanced_ordered_word_comparison`).

Generic in the carrier family `H N`; imports only the frozen `FullWickH4`.  Standard axioms only.
-/

noncomputable section
open Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickS2

open QuantumNLS.FullWickH4

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]

/-- `c · N⁻¹ ≤ ε` eventually, for every real `c` and `ε > 0`. -/
lemma eventually_const_mul_inv_le (c ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ)⁻¹ ≤ ε := by
  have h : Tendsto (fun N : ℕ => c * (N : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul c
  exact (h.eventually (Iio_mem_nhds hε)).mono (fun _ hN => le_of_lt hN)

/-! ### Operator-norm `O(N⁻¹)` perturbation -/

/-- **O(1/N) operator perturbation preserves the uniform strong symbol.**  If `‖A_N − B_N‖ ≤ K/N`
eventually, the preparation has norm at most `M` eventually (uniformly over `S × Tb`), and `B` has
the uniform strong symbol `a`, then so has `A`. -/
theorem hasUniformStrongT_of_opClose {X Θ : Type*} {A B : ∀ N, H N →L[ℂ] H N} {S : Set X}
    {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N} {a : X → Θ → ℂ} {K M : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᶠ N : ℕ in atTop, ‖A N - B N‖ ≤ K * (N : ℝ)⁻¹)
    (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ ≤ M)
    (hB : HasUniformStrongT B S Tb ψ a) : HasUniformStrongT A S Tb ψ a := by
  intro ε hε
  filter_upwards [hAB, hψ, hB (ε / 2) (half_pos hε),
    eventually_const_mul_inv_le (K * M) (ε / 2) (half_pos hε)] with N h1 h2 h3 h4
  intro u hu t ht
  have hsplit : (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)
      = (A N - B N) (ψ u t N) + (B N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  have hKN : 0 ≤ K * (N : ℝ)⁻¹ := mul_nonneg hK (inv_nonneg.2 (Nat.cast_nonneg N))
  have e1 : ‖(A N - B N) (ψ u t N)‖ ≤ ε / 2 := by
    calc ‖(A N - B N) (ψ u t N)‖ ≤ ‖A N - B N‖ * ‖ψ u t N‖ := (A N - B N).le_opNorm _
      _ ≤ (K * (N : ℝ)⁻¹) * M :=
          mul_le_mul h1 (h2 u hu t ht) (norm_nonneg _) hKN
      _ = (K * M) * (N : ℝ)⁻¹ := by ring
      _ ≤ ε / 2 := h4
  rw [hsplit]
  calc ‖(A N - B N) (ψ u t N) + (B N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖
      ≤ ‖(A N - B N) (ψ u t N)‖ + ‖(B N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ :=
        norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add e1 (h3 u hu t ht)
    _ = ε := by ring

/-- The same for the adjoint pair: both the operator and its companion are `O(1/N)`-close to
reference operators `B`, `B'` carrying the pair. -/
theorem hasUniformPairT_of_opClose {X Θ : Type*} {A A' B B' : ∀ N, H N →L[ℂ] H N} {S : Set X}
    {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N} {a : X → Θ → ℂ} {K M : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᶠ N : ℕ in atTop, ‖A N - B N‖ ≤ K * (N : ℝ)⁻¹)
    (hAB' : ∀ᶠ N : ℕ in atTop, ‖A' N - B' N‖ ≤ K * (N : ℝ)⁻¹)
    (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ ≤ M)
    (hB : HasUniformPairT B B' S Tb ψ a) : HasUniformPairT A A' S Tb ψ a :=
  ⟨hasUniformStrongT_of_opClose hK hAB hψ hB.1,
    hasUniformStrongT_of_opClose hK hAB' hψ hB.2⟩

/-! ### Finite linear combinations -/

/-- **Finite linear combination.**  If each `A_i` (`i ∈ s`) has the uniform strong symbol `a_i`, then
`Σ_i c_i A_i` has the uniform strong symbol `Σ_i c_i a_i`. -/
theorem hasUniformStrongT_sum {ι X Θ : Type*} (s : Finset ι) (A : ι → ∀ N, H N →L[ℂ] H N)
    (c : ι → ℂ) (a : ι → X → Θ → ℂ) {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N}
    (hA : ∀ i ∈ s, HasUniformStrongT (A i) S Tb ψ (a i)) :
    HasUniformStrongT (fun N => ∑ i ∈ s, c i • A i N) S Tb ψ
      (fun u t => ∑ i ∈ s, c i * a i u t) := by
  intro ε hε
  set D : ℝ := 1 + ∑ i ∈ s, ‖c i‖ with hD
  have hDpos : 0 < D := by
    have : 0 ≤ ∑ i ∈ s, ‖c i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    rw [hD]; linarith
  set δ : ℝ := ε / D with hδ
  have hδpos : 0 < δ := div_pos hε hDpos
  have hDδ : D * δ = ε := by rw [hδ]; field_simp
  have hall : ∀ᶠ N in atTop, ∀ i ∈ s, ∀ u ∈ S, ∀ t ∈ Tb,
      ‖(A i N - a i u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ ≤ δ :=
    (Filter.eventually_all_finset s).2 (fun i hi => hA i hi δ hδpos)
  filter_upwards [hall] with N hN
  intro u hu t ht
  have e : (∑ i ∈ s, c i • A i N - (∑ i ∈ s, c i * a i u t) • ContinuousLinearMap.id ℂ (H N))
        (ψ u t N)
      = ∑ i ∈ s, c i • ((A i N - a i u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Finset.sum_smul, smul_sub,
      smul_smul, Finset.sum_sub_distrib]
  rw [e]
  calc ‖∑ i ∈ s, c i • ((A i N - a i u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))‖
      ≤ ∑ i ∈ s, ‖c i • ((A i N - a i u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖c i‖ * δ := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hN i hi u hu t ht) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖c i‖) * δ := by rw [Finset.sum_mul]
    _ ≤ D * δ := by
        apply mul_le_mul_of_nonneg_right _ hδpos.le
        rw [hD]; linarith
    _ = ε := hDδ

/-- Finite linear combination for adjoint pairs: the companion of `Σ_i c_i A_i` is
`Σ_i conj(c_i) A'_i`, with the conjugate symbol. -/
theorem hasUniformPairT_sum {ι X Θ : Type*} (s : Finset ι) (A A' : ι → ∀ N, H N →L[ℂ] H N)
    (c : ι → ℂ) (a : ι → X → Θ → ℂ) {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N}
    (hA : ∀ i ∈ s, HasUniformPairT (A i) (A' i) S Tb ψ (a i)) :
    HasUniformPairT (fun N => ∑ i ∈ s, c i • A i N)
      (fun N => ∑ i ∈ s, (starRingEnd ℂ) (c i) • A' i N) S Tb ψ
      (fun u t => ∑ i ∈ s, c i * a i u t) := by
  refine ⟨hasUniformStrongT_sum s A c a (fun i hi => (hA i hi).1), ?_⟩
  have h := hasUniformStrongT_sum s A' (fun i => (starRingEnd ℂ) (c i))
    (fun i u t => (starRingEnd ℂ) (a i u t)) (S := S) (Tb := Tb) (ψ := ψ)
    (fun i hi => (hA i hi).2)
  have hfun : (fun u t => (starRingEnd ℂ) (∑ i ∈ s, c i * a i u t))
      = (fun u t => ∑ i ∈ s, (starRingEnd ℂ) (c i) * (starRingEnd ℂ) (a i u t)) := by
    funext u t
    simp only [map_sum, map_mul]
  rw [hfun]
  exact h

/-! ### Combination of both: `A ≈ Σ_k c_k B_k` -/

/-- If `A_N` is `O(1/N)`-close to `Σ_k c_k B_{k,N}` and each `B_k` has the uniform strong symbol
`b_k`, then `A` has the uniform strong symbol `Σ_k c_k b_k` (on preparations of bounded norm). -/
theorem hasUniformStrongT_of_sum_opClose {ι X Θ : Type*} (s : Finset ι)
    (B : ι → ∀ N, H N →L[ℂ] H N) (c : ι → ℂ) (b : ι → X → Θ → ℂ) {A : ∀ N, H N →L[ℂ] H N}
    {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N} {K M : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᶠ N : ℕ in atTop, ‖A N - ∑ i ∈ s, c i • B i N‖ ≤ K * (N : ℝ)⁻¹)
    (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ ≤ M)
    (hB : ∀ i ∈ s, HasUniformStrongT (B i) S Tb ψ (b i)) :
    HasUniformStrongT A S Tb ψ (fun u t => ∑ i ∈ s, c i * b i u t) :=
  hasUniformStrongT_of_opClose (B := fun N => ∑ i ∈ s, c i • B i N) hK hAB hψ
    (hasUniformStrongT_sum s B c b hB)

/-- Adjoint-pair version of `hasUniformStrongT_of_sum_opClose`. -/
theorem hasUniformPairT_of_sum_opClose {ι X Θ : Type*} (s : Finset ι)
    (B B' : ι → ∀ N, H N →L[ℂ] H N) (c : ι → ℂ) (b : ι → X → Θ → ℂ)
    {A A' : ∀ N, H N →L[ℂ] H N} {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N} {K M : ℝ}
    (hK : 0 ≤ K)
    (hAB : ∀ᶠ N : ℕ in atTop, ‖A N - ∑ i ∈ s, c i • B i N‖ ≤ K * (N : ℝ)⁻¹)
    (hAB' : ∀ᶠ N : ℕ in atTop,
      ‖A' N - ∑ i ∈ s, (starRingEnd ℂ) (c i) • B' i N‖ ≤ K * (N : ℝ)⁻¹)
    (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ ≤ M)
    (hB : ∀ i ∈ s, HasUniformPairT (B i) (B' i) S Tb ψ (b i)) :
    HasUniformPairT A A' S Tb ψ (fun u t => ∑ i ∈ s, c i * b i u t) :=
  hasUniformPairT_of_opClose (B := fun N => ∑ i ∈ s, c i • B i N)
    (B' := fun N => ∑ i ∈ s, (starRingEnd ℂ) (c i) • B' i N) hK hAB hAB' hψ
    (hasUniformPairT_sum s B B' c b hB)

end QuantumNLS.FullWickS2

#print axioms QuantumNLS.FullWickS2.eventually_const_mul_inv_le
#print axioms QuantumNLS.FullWickS2.hasUniformStrongT_of_opClose
#print axioms QuantumNLS.FullWickS2.hasUniformPairT_of_opClose
#print axioms QuantumNLS.FullWickS2.hasUniformStrongT_sum
#print axioms QuantumNLS.FullWickS2.hasUniformPairT_sum
#print axioms QuantumNLS.FullWickS2.hasUniformStrongT_of_sum_opClose
#print axioms QuantumNLS.FullWickS2.hasUniformPairT_of_sum_opClose
