import QuantumNLS.Local013ProductLimit

/-!
# LOCAL-013 `reset:principal-calculus`, stage L5a: the commutator family converges
(`source-text/chapters/local/quantum_periods.tex:141-165`)

Source (proof of LOCAL-013): "For commutators, `N c_{N,p,q,1} → pq` and `N Σ_{s≥2} c_{N,p,q,s} → 0`
for fixed `p,q` ... The bound of Lemma reset:placement-algebra on a strictly larger radius controls
all remaining degree tails."

The commutator family is the frozen LOCAL-011 list `positiveOverlapCommutatorList N (A N) (B N)`,
which represents `iN[A_N, B_N]` and obeys the derivation bound `eq:reset:analytic-derivation`
(`local011_full_source_ordered_clauses`).

Proved here (standard axioms only):
* `coeff_comm_eq`: for `j ≤ N` the degree-`j` coefficient is the finite sum over `p, q, s ≤ j` of
  `i N c_{N,p,q,s} K_s^{[·,·]}(A_{p,N}, B_{q,N})` with union degree `j`.
* `tendsto_coeff_comm`: it converges in operator norm to
  `commLim Alim Blim j = Σ_{p,q ≥ 1, p+q-1 = j} i p q K_1^{[·,·]}(A_p, B_q)`.
* `commutator_converges`: if `A, B` converge on `R` and `1 ≤ r < R`, then the commutator family
  converges on `r` to `commLim Alim Blim` and represents `iN[A_N, B_N]`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementProduct QuantumNLS.KernelConvergence QuantumNLS.LocalPlacement
  QuantumNLS.PlacementFiberPrefixCommutator QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011 QuantumNLS.Local013ProductSymbol
  QuantumNLS.Local013ProductLimit

namespace QuantumNLS.Local013CommutatorLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sum_fin_eq_sum_range {E : Type*} [AddCommMonoid E] {N j : ℕ} (hjN : j ≤ N)
    (f : ℕ → E) (hf : ∀ n, j < n → f n = 0) :
    ∑ i : Fin (N + 1), f i.1 = ∑ n ∈ range (j + 1), f n :=
  sum_comp_inj (fun i : Fin (N + 1) => i.1) Fin.val_injective f _
    (fun i hi => hf _ (by simp only [Finset.mem_range] at hi; omega))
    (fun n hn hnot => absurd rfl (hnot ⟨n, by simp only [Finset.mem_range] at hn; omega⟩))

/-- The `(p,q,s)` contribution to the degree-`j` coefficient of the commutator list. -/
def commTerm (A B : ∀ N : ℕ, KernelList (H := H) N) (j N p q s : ℕ) :
    BoundedSymmetricKernel H j :=
  if h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q ∧ unionSize p q s = j then
    castSymSectorOperator h.2.2.2
      ((Complex.I * (N : ℂ) * ((overlapCoefficient N p q s : ℝ) : ℂ)) •
        overlapCommutatorKernel h.2.1 h.2.2.1 (coeffAt A N p) (coeffAt B N q))
  else 0

theorem commTerm_eq_zero {A B : ∀ N : ℕ, KernelList (H := H) N} {j N p q s : ℕ}
    (h : ¬ (p ≤ j ∧ q ≤ j ∧ s ≤ j)) : commTerm A B j N p q s = 0 := by
  unfold commTerm
  rw [dif_neg]
  rintro ⟨h1, h2, h3, h4⟩
  apply h
  have := le_unionSize_left p q s
  have := le_unionSize_right p q s h2
  omega

theorem coeff_comm_eq (A B : ∀ N : ℕ, KernelList (H := H) N) {j N : ℕ} (hjN : j ≤ N) :
    coeffAt (fun N => positiveOverlapCommutatorList N (A N) (B N)) N j =
      ∑ p ∈ range (j + 1), ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1),
        commTerm A B j N p q s := by
  unfold coeffAt
  rw [dif_pos hjN]
  unfold positiveOverlapCommutatorList
  simp only [Finset.sum_apply]
  trans ∑ p : Fin (N + 1), ∑ q : Fin (N + 1), ∑ s : Fin (N + 1), commTerm A B j N p.1 q.1 s.1
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro s _
    by_cases hc : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧ unionSize p.1 q.1 s.1 ≤ N
    · rw [dif_pos hc]
      have hsp : s.1 ≤ p.1 := le_trans hc.2.1 (min_le_left _ _)
      have hsq : s.1 ≤ q.1 := le_trans hc.2.1 (min_le_right _ _)
      unfold kernelSpike commTerm
      by_cases hj' : j = unionSize p.1 q.1 s.1
      · rw [dif_pos hj', dif_pos ⟨hc.1, hsp, hsq, hj'.symm⟩, coeffAt_self, coeffAt_self]
      · rw [dif_neg hj', dif_neg (fun h' => hj' h'.2.2.2.symm)]
    · rw [dif_neg hc]
      unfold commTerm
      rw [dif_neg]
      · rfl
      · rintro ⟨h1, h2, h3, h4⟩
        apply hc
        refine ⟨h1, le_min h2 h3, ?_⟩
        rw [h4]
        omega
  have hs : ∀ p q : ℕ,
      ∑ s : Fin (N + 1), commTerm A B j N p q s.1 =
        ∑ s ∈ range (j + 1), commTerm A B j N p q s := fun p q =>
    sum_fin_eq_sum_range hjN (fun s => commTerm A B j N p q s)
      (fun n hn => commTerm_eq_zero (by rintro ⟨_, _, h3⟩; omega))
  simp only [hs]
  have hq : ∀ p : ℕ,
      ∑ q : Fin (N + 1), ∑ s ∈ range (j + 1), commTerm A B j N p q.1 s =
        ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1), commTerm A B j N p q s := fun p =>
    sum_fin_eq_sum_range hjN (fun q => ∑ s ∈ range (j + 1), commTerm A B j N p q s)
      (fun n hn => by
        show ∑ s ∈ range (j + 1), commTerm A B j N p n s = 0
        refine Finset.sum_eq_zero (fun s _ => commTerm_eq_zero ?_)
        rintro ⟨_, h2, _⟩
        omega)
  simp only [hq]
  refine sum_fin_eq_sum_range hjN
    (fun p => ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1), commTerm A B j N p q s) (fun n hn => ?_)
  show ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1), commTerm A B j N n q s = 0
  refine Finset.sum_eq_zero (fun q _ => Finset.sum_eq_zero (fun s _ => commTerm_eq_zero ?_))
  rintro ⟨h1, _, _⟩
  omega

/-! ### Fixed-degree limits -/

theorem tendsto_eqrec {m n : ℕ} (h : m = n) {f : ℕ → BoundedSymmetricKernel H m}
    {L : BoundedSymmetricKernel H m} (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun N => (h ▸ f N : BoundedSymmetricKernel H n)) atTop
      (𝓝 (h ▸ L : BoundedSymmetricKernel H n)) := by
  subst h; exact hf

theorem tendsto_commK {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : ℕ → BoundedSymmetricKernel H p) (B : ℕ → BoundedSymmetricKernel H q)
    (A₀ : BoundedSymmetricKernel H p) (B₀ : BoundedSymmetricKernel H q)
    (hA : Tendsto (fun N => ‖A N - A₀‖) atTop (𝓝 0))
    (hB : Tendsto (fun N => ‖B N - B₀‖) atTop (𝓝 0)) :
    Tendsto (fun N => overlapCommutatorKernel hsp hsq (A N) (B N)) atTop
      (𝓝 (overlapCommutatorKernel hsp hsq A₀ B₀)) := by
  unfold overlapCommutatorKernel
  exact (QuantumNLS.TerraMultiRound21VaryingAverage.varying_average_limit hsp hsq A B A₀ B₀ hA
    hB).sub (tendsto_eqrec _
      (QuantumNLS.TerraMultiRound21VaryingAverage.varying_average_limit hsq hsp B A B₀ A₀ hB hA))

/-- The limit of the `(p,q,s)` contribution: `i p q K_1^{[·,·]}` for `s = 1`, zero otherwise. -/
def commTermLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j p q s : ℕ) :
    BoundedSymmetricKernel H j :=
  if h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q ∧ unionSize p q s = j then
    castSymSectorOperator h.2.2.2
      ((if s = 1 then Complex.I * (((p : ℝ) * q : ℝ) : ℂ) else 0) •
        overlapCommutatorKernel h.2.1 h.2.2.1 (Alim p) (Blim q))
  else 0

theorem tendsto_commTerm (A B : ∀ N : ℕ, KernelList (H := H) N)
    (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p)
    (hA : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0))
    (hB : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt B N p - Blim p‖) atTop (𝓝 0))
    (j p q s : ℕ) :
    Tendsto (fun N => commTerm A B j N p q s) atTop (𝓝 (commTermLim Alim Blim j p q s)) := by
  unfold commTerm commTermLim
  by_cases h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q ∧ unionSize p q s = j
  · simp only [dif_pos h]
    apply tendsto_cast
    have hk := tendsto_commK h.2.1 h.2.2.1 (fun N => coeffAt A N p) (fun N => coeffAt B N q)
      (Alim p) (Blim q) (hA p) (hB q)
    rcases eq_or_ne s 1 with hs1 | hs1
    · subst hs1
      rw [if_pos rfl]
      have hc0 : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q 1 : ℝ) : ℂ)) atTop
          (𝓝 (((p : ℝ) * q : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (QuantumNLS.OverlapMoments.tendsto_N_c_one p q)
      have hc : Tendsto (fun N : ℕ => Complex.I * (N : ℂ) *
          ((overlapCoefficient N p q 1 : ℝ) : ℂ)) atTop
          (𝓝 (Complex.I * (((p : ℝ) * q : ℝ) : ℂ))) := by
        refine (hc0.const_mul Complex.I).congr (fun N => ?_)
        push_cast
        ring
      exact hc.smul hk
    · rw [if_neg hs1]
      have hs2 : 2 ≤ s := by omega
      have hc0 : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q s : ℝ) : ℂ)) atTop
          (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (QuantumNLS.TerraMultiRound19ScaledTerms.scaled_multiple_overlap_limit p q s hs2 h.2.2.1)
      have hc : Tendsto (fun N : ℕ => Complex.I * (N : ℂ) *
          ((overlapCoefficient N p q s : ℝ) : ℂ)) atTop (𝓝 0) := by
        have := hc0.const_mul Complex.I
        rw [Complex.ofReal_zero, mul_zero] at this
        refine this.congr (fun N => ?_)
        push_cast
        ring
      exact hc.smul hk
  · simp only [dif_neg h]
    exact tendsto_const_nhds

/-- The `(p,q)` single-overlap commutator kernel `i p q K_1^{[·,·]}(A_p,B_q)` at degree `j`. -/
def cTerm (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j p q : ℕ) :
    BoundedSymmetricKernel H j :=
  if h : 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = j then
    castSymSectorOperator h.2.2
      ((Complex.I * (((p : ℝ) * q : ℝ) : ℂ)) • overlapCommutatorKernel h.1 h.2.1 (Alim p) (Blim q))
  else 0

/-- **The limiting degree-`j` kernel of `iN[A_N, B_N]`**. -/
def commLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j : ℕ) :
    BoundedSymmetricKernel H j :=
  ∑ p ∈ range (j + 1), ∑ q ∈ range (j + 1), cTerm Alim Blim j p q

theorem sum_commTermLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j : ℕ) :
    ∑ p ∈ range (j + 1), ∑ q ∈ range (j + 1), ∑ s ∈ range (j + 1),
      commTermLim Alim Blim j p q s = commLim Alim Blim j := by
  unfold commLim
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_eq_single 1]
  · unfold commTermLim cTerm
    by_cases h : 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = j
    · rw [dif_pos ⟨le_refl 1, h.1, h.2.1, h.2.2⟩, dif_pos h, if_pos rfl]
    · rw [dif_neg (fun h' => h ⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩), dif_neg h]
  · intro s _ hs
    unfold commTermLim
    by_cases h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q ∧ unionSize p q s = j
    · rw [dif_pos h, if_neg hs, zero_smul_kernel, cast_zero]
    · rw [dif_neg h]
  · intro h1
    unfold commTermLim
    rw [dif_neg]
    rintro ⟨_, h2, _, h4⟩
    apply h1
    have := le_unionSize_left p q 1
    simp only [Finset.mem_range]
    omega

/-- **Fixed-degree coefficient limit of the commutator family.** -/
theorem tendsto_coeff_comm (A B : ∀ N : ℕ, KernelList (H := H) N)
    (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p)
    (hA : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0))
    (hB : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt B N p - Blim p‖) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun N => coeffAt (fun N => positiveOverlapCommutatorList N (A N) (B N)) N j) atTop
      (𝓝 (commLim Alim Blim j)) := by
  rw [← sum_commTermLim]
  have hlim := tendsto_finset_sum (range (j + 1)) fun p _ =>
    tendsto_finset_sum (range (j + 1)) fun q _ =>
      tendsto_finset_sum (range (j + 1)) fun s _ =>
        tendsto_commTerm A B Alim Blim hA hB j p q s
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop j] with N hN
  exact (coeff_comm_eq A B hN).symm

/-! ### The uniform radius bound on a smaller radius -/

theorem exists_mul_pow_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℕ, (p : ℝ) * r ^ p ≤ K * R ^ p := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hx0 : 0 ≤ r / R := div_nonneg hr hR.le
  have hx1 : r / R < 1 := (div_lt_one hR).mpr hrR
  obtain ⟨K, hK⟩ := (tendsto_self_mul_const_pow_of_lt_one hx0 hx1).bddAbove_range
  refine ⟨max K 0, le_max_right _ _, fun p => ?_⟩
  have hp : (p : ℝ) * (r / R) ^ p ≤ max K 0 := (hK ⟨p, rfl⟩).trans (le_max_left _ _)
  have hRp : 0 < R ^ p := pow_pos hR p
  calc (p : ℝ) * r ^ p = ((p : ℝ) * (r / R) ^ p) * R ^ p := by
        rw [div_pow]; field_simp
    _ ≤ max K 0 * R ^ p := mul_le_mul_of_nonneg_right hp hRp.le

set_option maxHeartbeats 1000000 in
/-- **LOCAL-013, commutator convergence.** If `A, B` converge on `R` and `1 ≤ r < R`, the LOCAL-011
commutator lists of `iN[A_N, B_N]` converge on `r` with limiting kernels `commLim Alim Blim`. -/
theorem commutator_converges {r R : ℝ} (hr : 1 ≤ r) (hrR : r < R)
    {A B : ∀ N : ℕ, KernelList (H := H) N} {Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius R A Alim) (hB : ConvergesOnRadius R B Blim) :
    ConvergesOnRadius r (fun N => positiveOverlapCommutatorList N (A N) (B N))
        (commLim Alim Blim) ∧
      ∀ N, QuantumNLS.RadiusBound.represented (positiveOverlapCommutatorList N (A N) (B N)) =
        ((Complex.I : ℂ) * (N : ℂ)) •
          ((QuantumNLS.RadiusBound.represented (A N)).comp
              (QuantumNLS.RadiusBound.represented (B N)) -
            (QuantumNLS.RadiusBound.represented (B N)).comp
              (QuantumNLS.RadiusBound.represented (A N))) := by
  obtain ⟨⟨CA, hCA⟩, hAl⟩ := hA
  obtain ⟨⟨CB, hCB⟩, hBl⟩ := hB
  have hR1 : 1 ≤ R := le_trans hr hrR.le
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨K, hK0, hK⟩ := exists_mul_pow_le hr0 hrR
  have hCB0 : 0 ≤ CB :=
    (QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (B 0)).trans (hCB 0)
  refine ⟨⟨⟨(2 / (R - r)) * (K * CA) * CB, fun N => ?_⟩, fun j => ?_⟩, fun N => ?_⟩
  · have h := (local011_full_source_ordered_clauses hr hrR (A N) (B N)).2.2.2.2.2
    refine h.trans ?_
    have hsum : ∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A N p‖ ≤ K * CA := by
      calc ∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A N p‖
          ≤ ∑ p : Fin (N + 1), K * (R ^ p.1 * ‖A N p‖) := by
            apply Finset.sum_le_sum
            intro p _
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (hK p.1) (norm_nonneg (A N p))
        _ = K * QuantumNLS.RadiusBound.radiusBound R (A N) := by
            rw [QuantumNLS.RadiusBound.radiusBound, Finset.mul_sum]
        _ ≤ K * CA := mul_le_mul_of_nonneg_left (hCA N) hK0
    have h2 : 0 ≤ 2 / (R - r) := div_nonneg (by norm_num) (by linarith)
    have hs0 : 0 ≤ ∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A N p‖ :=
      Finset.sum_nonneg (fun p _ => by positivity)
    calc 2 / (R - r) * (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A N p‖) *
          QuantumNLS.RadiusBound.radiusBound R (B N)
        ≤ 2 / (R - r) * (K * CA) * QuantumNLS.RadiusBound.radiusBound R (B N) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum h2)
          exact QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (B N)
      _ ≤ 2 / (R - r) * (K * CA) * CB := by
          apply mul_le_mul_of_nonneg_left (hCB N)
          exact mul_nonneg h2 (le_trans (mul_nonneg hK0 (le_trans
            (QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (A 0)) (hCA 0)))
            (le_refl _))
  · have h := tendsto_coeff_comm A B Alim Blim hAl hBl j
    exact (tendsto_iff_norm_sub_tendsto_zero (E := BoundedSymmetricKernel H j)).mp h
  · exact (local011_full_source_ordered_clauses hr hrR (A N) (B N)).2.2.2.2.1

end QuantumNLS.Local013CommutatorLimit

#print axioms QuantumNLS.Local013CommutatorLimit.coeff_comm_eq
#print axioms QuantumNLS.Local013CommutatorLimit.tendsto_commK
#print axioms QuantumNLS.Local013CommutatorLimit.tendsto_commTerm
#print axioms QuantumNLS.Local013CommutatorLimit.sum_commTermLim
#print axioms QuantumNLS.Local013CommutatorLimit.tendsto_coeff_comm
#print axioms QuantumNLS.Local013CommutatorLimit.exists_mul_pow_le
#print axioms QuantumNLS.Local013CommutatorLimit.commutator_converges
