import QuantumNLS.ChargeEnergy
import QuantumNLS.ContactForm
import QuantumNLS.ProductPreparation

/-!
# DEF-031 (energy half) for product states: `h_N[u^{⊗N}]/N`, exact finite-`N` correction

Source (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`): DEF-003 (`definitions.tex:21`,
`κ m/N` microscopic coupling for the normalized profile), DEF-005 (`:31`, contact form), DEF-031
(`:189`: `ψ_N ∈ H¹_sym` and `limsup_N h_N[ψ_N]/N ≤ I_3(u)`), `model.tex` (`h_N` with `2κ/N`,
diagonal measure without `√2`).

Frozen imports (read-only): `ChargeEnergy` (`8b11b1df…`: `energyH1`, `kinetic`, `quartic`,
`hasSum_quartic`), `ContactForm` (`06da9b2b…`: `q`, `Dj`, `Tpair`), through it `CollisionTrace`
(`e249be71…`) and `PhysicalEnergy`, and `ProductPreparation` (`317fa39f…`).

What is proved (no dynamics, no conservation law, nothing assumed about the trace):
* `prod_hasSum(_fintype)`: `Σ_w ∏ g_j(w_j) = ∏ Σ g_j` for nonnegative summable families on `ℤ^N`.
* `productH1`: for unit `u ∈ H¹` the product wave function `u^{⊗N}` is an element of the physical
  `H¹_sym(𝕋_L^N)` (`hasSum_kinWeight_prod`: `Σ a_N|Ψ̂|² = 1 + N K(u)`), `‖Ψ_N‖ = 1`.
* kinetic part `Σ_j ‖∂_jΨ_N‖² = N K(u)` (`sum_norm_sq_Dj_product`).
* contact part, on the constructed Fourier trace: `traceCoeff_product`
  `(T_ijΨ_N)(s,m) = L^{-1/2}(û⋆û)(s) ∏_{l≠i,j} û(m_l)` and `norm_sq_trace_product`
  `‖T_ijΨ_N‖² = Q(u) = ∫|u|⁴` (from `ChargeEnergy.hasSum_quartic`, i.e. the Fourier convolution form,
  not assumed); `card_pair`: `2·#{i<j} = N(N−1)`.
* `hN_product`, `hN_div_product`: `h_N[Ψ_N] = q_{N,κ/N}[Ψ_N] = N K + (2κ/N)(N(N−1)/2) Q` and
  `h_N[Ψ_N]/N = I_3^{(κ)}(u) − κ Q(u)/N` exactly (`I_3 = energyH1 = K + κ Q`).
* `product_energyPrepared`, `product_limsup`: `Ψ_N ∈ H¹_sym`, `‖Ψ_N‖ = 1`, `Ψ_N = u^{⊗N}`,
  `h_N/N → I_3(u)` (so `limsup = I_3`), and `≤ I_3(u)` at every `N ≥ 1` when `κ ≥ 0`.
* `physical_product_energy`: with `ProductPreparation` (`microscopicCoupling N = κ m/N`) the same
  for the normalized profile at effective coupling `κ m`, and `energyH1_profile`:
  `I_3^{(κ)}(u) = m·I_3^{(κ m)}(u/√m)`, so `m·h_N/N → I_3^{(κ)}(u)`.
* `energyH1_smooth_class`: for smooth periodic profiles `E_κ` is the DEF-022 charge `I_3`.

Prerequisite NOT assumed and NOT proved here: the real-space identification of the Fourier-side
trace `T_ij` with the restriction `∫_{x_i=x_j} |F|² dy_{ij}` on the coordinate measure for general
`H¹` (Sol's `CollisionIdentification`, not frozen); `ContactForm.q` is the closed form built from the
constructed Fourier trace.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open MeasureTheory

namespace QuantumNLS.ProductEnergyPreparation

/-- Sums of products over `ℤ^N` factor: for nonnegative summable families,
`Σ_w ∏_j g_j(w_j) = ∏_j Σ_n g_j(n)`. -/
theorem prod_hasSum : ∀ (N : ℕ) (g : Fin N → ℤ → ℝ), (∀ j n, 0 ≤ g j n) → (∀ j, Summable (g j)) →
    HasSum (fun w : Fin N → ℤ => ∏ j, g j (w j)) (∏ j, ∑' n, g j n) := by
  intro N
  induction N with
  | zero =>
    intro g _ _
    have := hasSum_fintype (fun w : Fin 0 → ℤ => (1 : ℝ))
    simp at this ⊢
  | succ N ih =>
    intro g h0 hs
    have h1 := ih (fun j => g j.succ) (fun j n => h0 _ _) (fun j => hs _)
    have hm := Summable.mul_of_nonneg (hs 0) h1.summable (fun n => h0 0 n)
      (fun w => Finset.prod_nonneg fun j _ => h0 _ _)
    have h2 := (hs 0).hasSum.mul h1 hm
    rw [← Fin.prod_univ_succ (f := fun j => ∑' n, g j n)] at h2
    let e : ℤ × (Fin N → ℤ) ≃ (Fin (N+1) → ℤ) := Fin.consEquiv (fun _ : Fin (N+1) => ℤ)
    rw [← e.hasSum_iff]
    convert h2 using 1
    funext p
    simp [e, Function.comp, Fin.prod_univ_succ, Fin.consEquiv]

/-- The same for an arbitrary finite index type. -/
theorem prod_hasSum_fintype {ι : Type} [Fintype ι] (g : ι → ℤ → ℝ) (h0 : ∀ j n, 0 ≤ g j n)
    (hs : ∀ j, Summable (g j)) :
    HasSum (fun w : ι → ℤ => ∏ j, g j (w j)) (∏ j, ∑' n, g j n) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have h := prod_hasSum (Fintype.card ι) (fun k => g (e.symm k)) (fun k n => h0 _ _) (fun k => hs _)
  let E : (ι → ℤ) ≃ (Fin (Fintype.card ι) → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  rw [← E.symm.hasSum_iff]
  have hp : (∏ k, ∑' n, g (e.symm k) n) = ∏ j, ∑' n, g j n :=
    Fintype.prod_equiv e.symm _ _ (fun k => rfl)
  rw [← hp]
  convert h using 1
  funext v
  simp only [Function.comp, E, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, id]
  exact Fintype.prod_equiv e _ _ (fun j => by simp)

/-! ## Part 1: the product state on the physical Fourier carrier -/

section Product

open QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.Energy
  QuantumNLS.CollisionTrace QuantumNLS.Fourier QuantumNLS.ContactForm QuantumNLS.ChargeEnergy
  QuantumNLS.TensorCarrier

variable {L : ℝ} [Fact (0 < L)]

/-- The `H¹` hypothesis on a one-particle `L²` profile: finite F04 weight `(1+(2πn/L)²)`
on its report Fourier coefficients (DEF-002 `s = 1`). -/
def OneH1 (u : L2T L) : Prop := Mem04 L 1 (fun n => fourierL2 L u n)

/-- The literal product wave function `u^{⊗N}` on `L²(𝕋_L^N)`. -/
def prodState (u : L2T L) (N : ℕ) : L2TN L N := prodLp (fun _ : Fin N => u)

theorem norm_prodState (u : L2T L) (N : ℕ) : ‖prodState u N‖ = ‖u‖ ^ N := by
  have h := physEmbed_htpow (L := L) (N := N) u
  unfold prodState
  rw [← h, (physEmbed (L := L) (N := N)).norm_map]
  exact norm_htpow N u

theorem coeff_prodState (u : L2T L) (N : ℕ) (w : Mom N) :
    (momUnitary L N (prodState u N) : Mom N → ℂ) w = ∏ j, fourierL2 L u (w j) :=
  momUnitary_prodLp _ w

theorem norm_sq_a (u : L2T L) (hu : ‖u‖ = 1) :
    HasSum (fun n : ℤ => ‖fourierL2 L u n‖ ^ 2) 1 := by
  have h := QuantumNLS.Energy.summable_sq (fourierL2 L u)
  have e := QuantumNLS.Energy.norm_sq_eq_tsum (fourierL2 L u)
  rw [norm_fourierL2, hu] at e
  have := h.hasSum
  rw [← e] at this
  simpa using this

/-- `kinetic` of the `L²` class of `u` is `Σ (2πn/L)² |û(n)|²`. -/
theorem kinetic_eq (u : L2T L) :
    kinetic (u : AddCircle L → ℂ) = ∑' n : ℤ, freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2 := by
  unfold kinetic
  exact tsum_congr fun n => by rw [fourierL2_apply]

theorem oneH1_h04 {u : L2T L} (hH : OneH1 u) : H04 L 1 (u : AddCircle L → ℂ) := by
  refine ⟨Lp.memLp u, ?_⟩
  have hH' : Mem04 L 1 (fun n => fourierL2 L u n) := hH
  unfold Mem04 at hH' ⊢
  simpa [fourierL2_apply] using hH'

theorem hasSum_kin_a {u : L2T L} (hH : OneH1 u) :
    HasSum (fun n : ℤ => freq L n ^ 2 * ‖fourierL2 L u n‖ ^ 2) (kinetic (u : AddCircle L → ℂ)) := by
  have hs := kin_summable hH
  rw [kin_eq] at hs
  rw [kinetic_eq]
  exact hs.hasSum

/-- **Weighted sums on the product state.**  For `‖u‖ = 1` and `u ∈ H¹`, the `j`-th kinetic sum of
`u^{⊗N}` is `K(u)`. -/
theorem hasSum_kin_prod {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) (j : Fin N) :
    HasSum (fun w : Mom N => freq L (w j) ^ 2 * ‖(momUnitary L N (prodState u N) : Mom N → ℂ) w‖ ^ 2)
      (kinetic (u : AddCircle L → ℂ)) := by
  set g : Fin N → ℤ → ℝ := fun i n => (if i = j then freq L n ^ 2 else 1) * ‖fourierL2 L u n‖ ^ 2
    with hg
  have h0 : ∀ i n, 0 ≤ g i n := fun i n => by simp only [hg]; split_ifs <;> positivity
  have hsum : ∀ i, Summable (g i) := fun i => by
    by_cases hi : i = j
    · simp only [hg, hi, ite_true]; exact (hasSum_kin_a hH).summable
    · simp only [hg, hi, ite_false, one_mul]; exact (norm_sq_a u hu).summable
  have h := prod_hasSum N g h0 hsum
  have hval : ∏ i, ∑' n, g i n = kinetic (u : AddCircle L → ℂ) := by
    have : ∀ i, ∑' n, g i n = if i = j then kinetic (u : AddCircle L → ℂ) else 1 := fun i => by
      by_cases hi : i = j
      · simp only [hg, hi, ite_true]; exact (hasSum_kin_a hH).tsum_eq
      · simp only [hg, hi, ite_false, one_mul]; exact (norm_sq_a u hu).tsum_eq
    simp_rw [this]
    simp
  rw [hval] at h
  convert h using 1
  funext w
  rw [coeff_prodState, norm_prod]
  simp only [hg, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.prod_pow]

/-- Total weighted sum on the product state: `Σ_w a_N(w)|Ψ̂(w)|² = 1 + N K(u)`. -/
theorem hasSum_kinWeight_prod {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    HasSum (fun w : Mom N => kinWeight L N w *
        ‖(momUnitary L N (prodState u N) : Mom N → ℂ) w‖ ^ 2)
      (1 + N * kinetic (u : AddCircle L → ℂ)) := by
  have h1 : HasSum (fun w : Mom N => ‖(momUnitary L N (prodState u N) : Mom N → ℂ) w‖ ^ 2) 1 := by
    have h := QuantumNLS.Energy.summable_sq (momUnitary L N (prodState u N))
    have e := QuantumNLS.Energy.norm_sq_eq_tsum (momUnitary L N (prodState u N))
    have hn : ‖momUnitary L N (prodState u N)‖ ^ 2 = 1 := by
      rw [LinearIsometryEquiv.norm_map, norm_prodState, hu]; simp
    rw [hn] at e
    have := h.hasSum
    rw [← e] at this
    exact this
  have h2 := hasSum_sum (s := Finset.univ) (fun (j : Fin N) _ => hasSum_kin_prod hu hH N j)
  have h3 := h1.add h2
  convert h3 using 1
  · funext w
    unfold kinWeight
    rw [add_mul, Finset.sum_mul, one_mul]
  · simp

/-- **The product state lies in `H¹_sym(𝕋_L^N)`** (as an element of the physical `H¹`). -/
theorem exists_productH1 {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    ∃ x : PhysH1 L N, x.val = prodState u N ∧ x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) := by
  have hmem : prodState u N ∈ {F : L2TN L N | Summable fun w => kinWeight L N w *
      ‖(momUnitary L N F : Mom N → ℂ) w‖ ^ 2} := (hasSum_kinWeight_prod hu hH N).summable
  rw [← PhysH1.range_val] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, hx, ?_⟩
  rw [PhysH1.mem_sym_iff, hx]
  rw [isSymm_iff_coeff]
  intro σ w
  rw [coeff_prodState, coeff_prodState]
  exact Equiv.prod_comp σ (fun i => fourierL2 L u (w i))

/-- The product state as an element of `H¹_sym`. -/
def productH1 {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) : PhysH1 L N :=
  Classical.choose (exists_productH1 hu hH N)

theorem productH1_val {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    (productH1 hu hH N).val = prodState u N :=
  (Classical.choose_spec (exists_productH1 hu hH N)).1

theorem productH1_sym {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    productH1 hu hH N ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) :=
  (Classical.choose_spec (exists_productH1 hu hH N)).2

theorem coeffFun_productH1 {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) (w : Mom N) :
    coeffFun (productH1 hu hH N) w = ∏ j, fourierL2 L u (w j) := by
  unfold coeffFun
  rw [productH1_val, coeff_prodState]

/-- `‖∂_jΨ_N‖² = K(u)` for each coordinate `j` (unit `u ∈ H¹`). -/
theorem norm_sq_Dj_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) (j : Fin N) :
    ‖Dj j (productH1 hu hH N)‖ ^ 2 = kinetic (u : AddCircle L → ℂ) := by
  rw [norm_sq_Dj]
  have h := hasSum_kin_prod hu hH N j
  rw [← h.tsum_eq]
  refine tsum_congr fun w => ?_
  unfold coeffFun
  rw [productH1_val]

/-- **Kinetic part of the product state:** `Σ_j ‖∂_jΨ_N‖² = N K(u)`. -/
theorem sum_norm_sq_Dj_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    ∑ j, ‖Dj j (productH1 hu hH N)‖ ^ 2 = N * kinetic (u : AddCircle L → ℂ) := by
  simp [norm_sq_Dj_product hu hH N]

/-! ## Part 2: the collision trace of the product state -/

section Trace

variable {N : ℕ} (i j : Fin N) (hij : i ≠ j)

omit [Fact (0 < L)] in
theorem fib_rest (t : TIdx N i j) (a : ℤ) (r : Rest N i j) : fib i j hij t a r.1 = t.2 r := by
  obtain ⟨l, h1, h2⟩ := r
  simp [fib, splitEquiv, h1, h2]

omit [Fact (0 < L)] in
/-- The product over `Fin N` along the antidiagonal fibre splits as
`g(a) g(s−a) ∏_{rest} g(m_l)`. -/
theorem prod_fib (g : ℤ → ℂ) (t : TIdx N i j) (a : ℤ) :
    ∏ l, g (fib i j hij t a l) = g a * g (t.1 - a) * ∏ r : Rest N i j, g (t.2 r) := by
  have hji : j ≠ i := hij.symm
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩),
    fib_i, fib_j, ← mul_assoc]
  congr 1
  rw [Finset.prod_subtype ((Finset.univ.erase i).erase j) (p := fun l => l ≠ i ∧ l ≠ j)
    (fun l => by simp [and_comm])]
  exact Finset.prod_congr rfl fun r _ => by rw [fib_rest]

/-- The one-dimensional self-convolution `Σ_k û(k) û(s−k)`. -/
def conv (u : L2T L) (s : ℤ) : ℂ := ∑' k : ℤ, fourierL2 L u k * fourierL2 L u (s - k)

/-- **Fourier trace coefficients of the product state**:
`(T_ij Ψ_N)(s, m) = L^{-1/2} (û ⋆ û)(s) ∏_{l ≠ i,j} û(m_l)`. -/
theorem traceCoeff_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (t : TIdx N i j) :
    traceCoeff L i j hij (coeffFun (productH1 hu hH N)) t =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * conv u t.1 * ∏ r : Rest N i j, fourierL2 L u (t.2 r) := by
  unfold traceCoeff
  simp_rw [coeffFun_productH1, prod_fib i j hij (fun n => fourierL2 L u n)]
  rw [tsum_mul_right]
  unfold conv
  ring

/-- **The collision trace of `u^{⊗N}` evaluated exactly**: for unit `u ∈ H¹` and any pair `i ≠ j`,
`‖T_ij Ψ_N‖² = ∫|u|⁴` — computed on the Fourier side from the constructed trace
(`ChargeEnergy.hasSum_quartic`, the Fourier convolution form of the quartic) and the product
sum over the remaining `N−2` factors (each of norm one). -/
theorem norm_sq_trace_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) :
    ‖traceMap i j hij (productH1 hu hH N)‖ ^ 2 = quartic (u : AddCircle L → ℂ) := by
  have hq := hasSum_quartic (oneH1_h04 hH)
  have hco : ∀ k, coeff L (u : AddCircle L → ℂ) k = fourierL2 L u k := fun k => (fourierL2_apply L u k).symm
  have hq' : HasSum (fun s : ℤ => ‖(((Real.sqrt L)⁻¹ : ℝ) : ℂ) * conv u s‖ ^ 2) (quartic (u : AddCircle L → ℂ)) := by
    simp only [hco] at hq
    exact hq
  have hB : HasSum (fun m : Rest N i j → ℤ => ∏ r, ‖fourierL2 L u (m r)‖ ^ 2) 1 := by
    have := prod_hasSum_fintype (fun (_ : Rest N i j) (n : ℤ) => ‖fourierL2 L u n‖ ^ 2)
      (fun _ n => by positivity) (fun _ => (norm_sq_a u hu).summable)
    simpa [(norm_sq_a u hu).tsum_eq] using this
  have hm := Summable.mul_of_nonneg hq'.summable hB.summable
    (fun s => by positivity) (fun m => Finset.prod_nonneg fun r _ => by positivity)
  have hprod := hq'.mul hB hm
  rw [mul_one] at hprod
  rw [QuantumNLS.Energy.norm_sq_eq_tsum, ← hprod.tsum_eq]
  refine tsum_congr fun t => ?_
  rw [traceMap_apply, traceCoeff_product i j hij hu hH t, norm_mul, norm_prod, mul_pow,
    Finset.prod_pow]

end Trace

/-! ## Part 3: the contact form on the product state, exact finite-`N` correction -/

section Energy

theorem card_pair (N : ℕ) : 2 * Fintype.card (Pair N) = N * (N - 1) := by
  classical
  unfold Pair
  rw [Fintype.card_subtype]
  set A : Finset (Fin N × Fin N) := Finset.univ.filter (fun p => p.1 < p.2) with hA
  set B : Finset (Fin N × Fin N) := Finset.univ.filter (fun p => p.2 < p.1) with hB
  have hAB : A.card = B.card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      simpa using hp
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, by simp⟩
      simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      simpa using hq
  have hoff : (Finset.univ : Finset (Fin N)).offDiag = A ∪ B := by
    ext ⟨a, b⟩
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_union, hA, hB,
      Finset.mem_filter]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact h.ne
      · exact h.ne'
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact absurd (hp.trans hq) (lt_irrefl _)
  have := Finset.offDiag_card (Finset.univ : Finset (Fin N))
  rw [hoff, Finset.card_union_of_disjoint hdisj, ← hAB, Finset.card_univ, Fintype.card_fin] at this
  rw [Nat.mul_sub, mul_one]
  omega

theorem card_pair_real (N : ℕ) : 2 * (Fintype.card (Pair N) : ℝ) = N * ((N : ℝ) - 1) := by
  have h := card_pair N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Fintype.card (Pair 0) = 0 := by omega
    simp
  · have h' : ((2 * Fintype.card (Pair N) : ℕ) : ℝ) = ((N * (N - 1) : ℕ) : ℝ) := by rw [h]
    push_cast [Nat.cast_sub hN] at h'
    simpa using h'

/-- **Contact part of the product state:** `Σ_{i<j} ‖T_ijΨ_N‖² = (N(N−1)/2) ∫|u|⁴`. -/
theorem sum_norm_sq_Tpair_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    ∑ p : Pair N, ‖Tpair p (productH1 hu hH N)‖ ^ 2 =
      (Fintype.card (Pair N) : ℝ) * quartic (u : AddCircle L → ℂ) := by
  have h : ∀ p : Pair N, ‖Tpair p (productH1 hu hH N)‖ ^ 2 = quartic (u : AddCircle L → ℂ) :=
    fun p => by
      unfold Tpair
      rw [traceCLM_apply]
      exact norm_sq_trace_product p.1.1 p.1.2 (ne_of_lt p.2) hu hH
  simp [h]

/-- **The DEF-031 Hamiltonian form** `h_N[ψ] = Σ_j‖∂_jψ‖² + (2κ/N) Σ_{j<l} ‖T_{jl}ψ‖²`, i.e. the
frozen contact form `q_{N,c}` of `ContactForm` at the microscopic coupling `c = κ/N`. -/
def hN (κ : ℝ) (N : ℕ) (x : PhysH1 L N) : ℝ := (q (κ / N) x x).re

/-- **Exact value of `h_N` on `u^{⊗N}`** (unit `u ∈ H¹`):
`h_N[Ψ_N] = N K(u) + (2κ/N)·(N(N−1)/2)·Q(u)`. -/
theorem hN_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (κ : ℝ) (N : ℕ) :
    hN κ N (productH1 hu hH N) =
      N * kinetic (u : AddCircle L → ℂ) +
        2 * (κ / N) * ((Fintype.card (Pair N) : ℝ) * quartic (u : AddCircle L → ℂ)) := by
  unfold hN
  rw [q_self, Complex.ofReal_re, sum_norm_sq_Dj_product hu hH N, sum_norm_sq_Tpair_product hu hH N]

/-- **Exact finite-`N` correction:** for `N ≥ 1`,
`h_N[Ψ_N]/N = K(u) + κ (1 − 1/N) Q(u) = E_κ(u) − κ Q(u)/N`. -/
theorem hN_div_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (κ : ℝ) {N : ℕ} (hN1 : 1 ≤ N) :
    hN κ N (productH1 hu hH N) / N =
      energyH1 κ (u : AddCircle L → ℂ) - κ * quartic (u : AddCircle L → ℂ) / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [hN_product hu hH κ N]
  have hc : 2 * (Fintype.card (Pair N) : ℝ) = N * ((N : ℝ) - 1) := card_pair_real N
  unfold energyH1
  field_simp
  linear_combination (κ * quartic (u : AddCircle L → ℂ)) * hc

end Energy

/-! ## Part 4: the DEF-031 energy preparation inequality for product states -/

section Prepared

/-- **The energy half of DEF-031**: the sequence lies in `H¹_sym` and
`limsup_N h_N[ψ_N]/N ≤ I_3(u)` — written in the equivalent quantified form
`∀ ε > 0, eventually h_N[ψ_N]/N ≤ I_3(u) + ε`, with `I_3 = E_κ(u) = K(u) + κ Q(u)` the
`H¹` extension of `ChargeEnergy` and `h_N` the (frozen) contact form at coupling `κ/N`. -/
def EnergyPrepared (κ : ℝ) (u : L2T L) (ψ : ∀ N : ℕ, PhysH1 L N) : Prop :=
  (∀ N, ψ N ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      hN κ N (ψ N) / N ≤ energyH1 κ (u : AddCircle L → ℂ) + ε

theorem quartic_nonneg (f : AddCircle L → ℂ) : 0 ≤ quartic f :=
  integral_nonneg fun x => by positivity

/-- **Product-state energy preparation** (unit `u ∈ H¹`, any real coupling `κ`):
`Ψ_N = u^{⊗N} ∈ H¹_sym`, `‖Ψ_N‖ = 1`, `Ψ_N = u^{⊗N}` (norm closeness is exact),
`h_N[Ψ_N]/N → I_3(u)`, hence `limsup ≤ I_3(u)`; for `κ ≥ 0` the inequality holds at every `N ≥ 1`
with the exact correction `h_N[Ψ_N]/N = I_3 − κ Q(u)/N`. -/
theorem product_energyPrepared {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (κ : ℝ) :
    (∀ N, (productH1 hu hH N).val = prodState u N) ∧
    (∀ N, ‖(productH1 hu hH N).val‖ = 1) ∧
    (∀ N : ℕ, 1 ≤ N → hN κ N (productH1 hu hH N) / N =
      energyH1 κ (u : AddCircle L → ℂ) - κ * quartic (u : AddCircle L → ℂ) / N) ∧
    Filter.Tendsto (fun N : ℕ => hN κ N (productH1 hu hH N) / N) Filter.atTop
      (nhds (energyH1 κ (u : AddCircle L → ℂ))) ∧
    (0 ≤ κ → ∀ N : ℕ, 1 ≤ N →
      hN κ N (productH1 hu hH N) / N ≤ energyH1 κ (u : AddCircle L → ℂ)) ∧
    EnergyPrepared κ u (productH1 hu hH) := by
  have hexact := fun (N : ℕ) (hN1 : 1 ≤ N) => hN_div_product hu hH κ hN1
  have hlim : Filter.Tendsto (fun N : ℕ => hN κ N (productH1 hu hH N) / N) Filter.atTop
      (nhds (energyH1 κ (u : AddCircle L → ℂ))) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat (κ * quartic (u : AddCircle L → ℂ)))
    have h1 := h0.const_sub (energyH1 κ (u : AddCircle L → ℂ))
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
    exact (hexact N hN1).symm
  refine ⟨fun N => productH1_val hu hH N, fun N => ?_, hexact, hlim, ?_, ?_, ?_⟩
  · rw [productH1_val, norm_prodState, hu]; simp
  · intro hκ N hN1
    rw [hexact N hN1]
    have : 0 ≤ κ * quartic (u : AddCircle L → ℂ) / N :=
      div_nonneg (mul_nonneg hκ (quartic_nonneg _)) (Nat.cast_nonneg N)
    linarith
  · exact fun N => productH1_sym hu hH N
  · intro ε hε
    exact (hlim.eventually (Iio_mem_nhds (by linarith))).mono fun N hN => hN.le

/-- The literal `limsup`: `limsup_N h_N[Ψ_N]/N = I_3(u)` (so `≤ I_3(u)` with equality). -/
theorem product_limsup {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (κ : ℝ) :
    Filter.limsup (fun N : ℕ => hN κ N (productH1 hu hH N) / N) Filter.atTop =
      energyH1 κ (u : AddCircle L → ℂ) :=
  (product_energyPrepared hu hH κ).2.2.2.1.limsup_eq

end Prepared

/-! ## Part 5: physical mass scaling (`ProductPreparation`) and the smooth-profile charge -/

section Physical

open QuantumNLS.ProductPreparation

theorem kinetic_smul (r : ℝ) (u : L2T L) :
    kinetic ((r • u : L2T L) : AddCircle L → ℂ) = r ^ 2 * kinetic (u : AddCircle L → ℂ) := by
  rw [kinetic_eq, kinetic_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have : fourierL2 L (r • u) n = (r : ℂ) * fourierL2 L u n := by
    rw [show r • u = (r : ℂ) • u from (Complex.coe_smul r u).symm, map_smul]; rfl
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem quartic_smul (r : ℝ) (u : L2T L) :
    quartic ((r • u : L2T L) : AddCircle L → ℂ) = r ^ 4 * quartic (u : AddCircle L → ℂ) := by
  unfold quartic
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul r u] with x hx
  rw [hx, Pi.smul_apply, show r • (u : AddCircle L → ℂ) x = (r : ℂ) * (u : AddCircle L → ℂ) x from
    by rw [Complex.real_smul], norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have : |r| ^ 4 = r ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [this]

theorem energyH1_smul (κ r : ℝ) (u : L2T L) :
    energyH1 κ ((r • u : L2T L) : AddCircle L → ℂ) =
      r ^ 2 * kinetic (u : AddCircle L → ℂ) + κ * (r ^ 4 * quartic (u : AddCircle L → ℂ)) := by
  unfold energyH1; rw [kinetic_smul, quartic_smul]

/-- **Mass scaling of `I_3`:** for `P` with mass `m` and coupling `κ`,
`I_3^{(κ)}(u) = m · I_3^{(κ m)}(u/√m)`. -/
theorem energyH1_profile (P : PositiveMassPreparation (L := L)) :
    energyH1 P.coupling (P.profile : AddCircle L → ℂ) =
      physicalMass P.profile * energyH1 P.effectiveCoupling (P.unitProfile : AddCircle L → ℂ) := by
  have hm := P.mass_pos
  have hs : 0 < Real.sqrt (physicalMass P.profile) := Real.sqrt_pos.2 hm
  have hprof : P.profile = Real.sqrt (physicalMass P.profile) • P.unitProfile := by
    unfold PositiveMassPreparation.unitProfile
    rw [smul_inv_smul₀ hs.ne']
  have hsq : Real.sqrt (physicalMass P.profile) ^ 2 = physicalMass P.profile := Real.sq_sqrt hm.le
  conv_lhs => rw [hprof]
  rw [energyH1_smul]
  unfold energyH1 PositiveMassPreparation.effectiveCoupling
  have h4 : Real.sqrt (physicalMass P.profile) ^ 4 = physicalMass P.profile ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  rw [h4, hsq]
  ring

/-- **DEF-003 + DEF-031 for the physical product preparation.**  For a positive-mass preparation `P`
(profile `u`, coupling `κ`, mass `m`) whose normalized profile `û = u/√m` is `H¹`, the product state
`Ψ_N = û^{⊗N}` at microscopic coupling `P.microscopicCoupling N = κ m/N` satisfies: it is in
`H¹_sym`, has norm one, equals `û^{⊗N}` exactly, and
`q_{N,κm/N}[Ψ_N]/N = E_{κm}(û) − κ m Q(û)/N` (exact finite-`N` correction), `→ I_3^{(κ m)}(û)`;
the inequality `≤ I_3^{(κ m)}(û)` holds at every `N ≥ 1` (`κ m > 0`), and
`m · I_3^{(κ m)}(û) = I_3^{(κ)}(u)` for the physical-mass profile. -/
theorem physical_product_energy (P : PositiveMassPreparation (L := L)) (hH : OneH1 P.unitProfile) :
    (∀ N, (productH1 P.norm_unitProfile hH N).val = prodState P.unitProfile N) ∧
    (∀ N, ‖(productH1 P.norm_unitProfile hH N).val‖ = 1) ∧
    (∀ N : ℕ, 1 ≤ N →
      (q (P.microscopicCoupling N) (productH1 P.norm_unitProfile hH N)
          (productH1 P.norm_unitProfile hH N)).re / N =
        energyH1 P.effectiveCoupling (P.unitProfile : AddCircle L → ℂ) -
          P.effectiveCoupling * quartic (P.unitProfile : AddCircle L → ℂ) / N) ∧
    (∀ N : ℕ, 1 ≤ N →
      (q (P.microscopicCoupling N) (productH1 P.norm_unitProfile hH N)
          (productH1 P.norm_unitProfile hH N)).re / N ≤
        energyH1 P.effectiveCoupling (P.unitProfile : AddCircle L → ℂ)) ∧
    EnergyPrepared P.effectiveCoupling P.unitProfile (productH1 P.norm_unitProfile hH) ∧
    Filter.Tendsto (fun N : ℕ => physicalMass P.profile *
        ((q (P.microscopicCoupling N) (productH1 P.norm_unitProfile hH N)
          (productH1 P.norm_unitProfile hH N)).re / N)) Filter.atTop
      (nhds (energyH1 P.coupling (P.profile : AddCircle L → ℂ))) := by
  obtain ⟨hv, hn, hex, hlim, hle, hprep⟩ :=
    product_energyPrepared P.norm_unitProfile hH P.effectiveCoupling
  have e : ∀ N : ℕ, hN P.effectiveCoupling N (productH1 P.norm_unitProfile hH N) =
      (q (P.microscopicCoupling N) (productH1 P.norm_unitProfile hH N)
        (productH1 P.norm_unitProfile hH N)).re := fun N => rfl
  simp only [e] at hex hlim hle hprep
  refine ⟨hv, hn, hex, hle P.effectiveCoupling_pos.le, hprep, ?_⟩
  rw [energyH1_profile]
  exact hlim.const_mul _

/-- **Smooth profiles:** if `u` is (the `L²` class of) a smooth periodic profile, then
`I_3^{(κ)}(u) = E_κ(u)` is the DEF-022 charge `charge L κ ũ 3` of `ClassicalCharges`. -/
theorem energyH1_smooth_class (κ : ℝ) {ũ : ℝ → ℂ} (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ) :
    QuantumNLS.ClassicalCharges.charge L κ ũ 3 =
      ((energyH1 κ ((ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
        (QuantumNLS.WeakDerivatives.liftC hu.smooth.continuous hu.periodic) :
          Lp ℂ 2 (volume : Measure (AddCircle L))) : AddCircle L → ℂ) : ℝ) : ℂ) := by
  rw [QuantumNLS.ChargeEnergy.charge_three_eq_energyH1 κ hu]
  congr 1
  exact (energyH1_congr_ae κ (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
    (volume : Measure (AddCircle L)) _)).symm

end Physical

end Product

/-! Kernel axiom audit. -/
#print axioms prod_hasSum
#print axioms prod_hasSum_fintype
#print axioms exists_productH1
#print axioms hasSum_kinWeight_prod
#print axioms hasSum_kin_prod
#print axioms sum_norm_sq_Dj_product
#print axioms traceCoeff_product
#print axioms norm_sq_trace_product
#print axioms card_pair
#print axioms sum_norm_sq_Tpair_product
#print axioms hN_product
#print axioms hN_div_product
#print axioms product_energyPrepared
#print axioms product_limsup
#print axioms energyH1_profile
#print axioms physical_product_energy
#print axioms energyH1_smooth_class

end QuantumNLS.ProductEnergyPreparation
