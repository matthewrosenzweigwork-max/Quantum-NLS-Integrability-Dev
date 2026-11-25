import QuantumNLS.Local013CommutatorLimit
import QuantumNLS.Local013PoissonSymbol
import QuantumNLS.RootComplexInterchange
import QuantumNLS.RootSymbolFrechet

/-!
# LOCAL-013 `reset:principal-calculus`, stage L5b: the symbol of the commutator family is `{b, h}`
(`source-text/chapters/local/quantum_periods.tex:141-165`)

Source: "Thus `−iN[Q(A),Q(B)]` has limiting symbol `2pq Im⟨α,β⟩ = {a,b}` ... In particular
`iN[H_N,B_N]` gives `{b,h}`. The bound of Lemma reset:placement-algebra on a strictly larger radius
controls all remaining degree tails. It also permits the fixed-degree coefficient limits of the
commutator to be summed."

Proved here (standard axioms only):
* `pbC_antisymm`: `{F, G} = −{G, F}` for the DEF-015 complex bracket.
* `kps_cTerm`: the symbol of the `(p,q)` limiting kernel `i p q K_1^{[·,·]}(H_p, B_q)` is
  `{b_q, h_p}` (from stage L4 `pbC_eq_commSymbol`).
* `hasSum_reindex`: summing the fixed-degree coefficient symbols over the degree `j` is the
  double series over `(p, q)` (antidiagonal reindexing).
* `symbol_commLim`: if `Σ R^p ‖H_p‖`, `Σ R^p ‖B_p‖` converge, `R > 1` and `‖v‖² < R`, then
  `symbol (commLim Hlim Blim) v = {b, h}(v)` with `b = symbol Blim`, `h = symbol Hlim`
  (termwise bracket of the two series: frozen `RootComplexInterchange.pbC_hasSum_tsum`, derivative
  bounds `RootSymbolFrechet.norm_fderiv_symFun_le`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators
open Filter Topology Finset Metric
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct QuantumNLS.KernelConvergence
  QuantumNLS.PlacementFiberPrefixCommutator QuantumNLS.SymplecticBracket
  QuantumNLS.Local013ProductSymbol QuantumNLS.Local013CommutatorLimit
  QuantumNLS.Local013PoissonSymbol

namespace QuantumNLS.Local013CommutatorSeries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Antisymmetry of the bracket and the symbol of the limiting kernels -/

theorem pbR_antisymm (F G : H → ℝ) (u : H) : pbR F G u = - pbR G F u := by
  rw [pbR_eq_omega, pbR_eq_omega, omega_swap]

theorem pbC_antisymm (F G : H → ℂ) (u : H) : pbC F G u = - pbC G F u := by
  have h1 := pbR_antisymm (fun v => (F v).re) (fun v => (G v).re) u
  have h2 := pbR_antisymm (fun v => (F v).im) (fun v => (G v).im) u
  have h3 := pbR_antisymm (fun v => (F v).im) (fun v => (G v).re) u
  have h4 := pbR_antisymm (fun v => (F v).re) (fun v => (G v).im) u
  unfold pbC
  apply Complex.ext
  · simp only [Complex.neg_re]
    rw [h1, h2]
    ring
  · simp only [Complex.neg_im]
    rw [h3, h4]
    ring

theorem kps_smul {n : ℕ} (c : ℂ) (K : BoundedSymmetricKernel H n) (v : H) :
    kernelProductSymbol (c • K) v = c * kernelProductSymbol K v := by
  unfold kernelProductSymbol
  rw [ContinuousLinearMap.smul_apply, Submodule.coe_smul, inner_smul_right]

theorem kps_cTerm (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j p q : ℕ) (v : H) :
    kernelProductSymbol (cTerm Alim Blim j p q) v =
      if 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = j then
        pbC (kernelProductSymbol (Blim q)) (kernelProductSymbol (Alim p)) v
      else 0 := by
  unfold cTerm
  by_cases h : 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = j
  · rw [dif_pos h, if_pos h, kps_cast, kps_smul, pbC_antisymm,
      pbC_eq_commSymbol h.1 h.2.1 (Alim p) (Blim q) v]
    ring
  · rw [dif_neg h, if_neg h, kps_zero]

theorem kps_commLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j : ℕ) (v : H) :
    kernelProductSymbol (commLim Alim Blim j) v =
      ∑ p ∈ range (j + 1), ∑ q ∈ range (j + 1),
        if 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = j then
          pbC (kernelProductSymbol (Blim q)) (kernelProductSymbol (Alim p)) v
        else 0 := by
  unfold commLim
  rw [kps_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [kps_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact kps_cTerm Alim Blim j p q v

/-! ### Reindexing the degree sum as the double series -/

theorem hasSum_reindex (G : ℕ → ℕ → ℂ)
    (hG : Summable (fun x : ℕ × ℕ => G (x.1 + 1) (x.2 + 1))) :
    HasSum (fun j => ∑ p ∈ range (j + 1), ∑ q ∈ range (j + 1),
        if 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = j then G p q else 0)
      (∑' x : ℕ × ℕ, G (x.1 + 1) (x.2 + 1)) := by
  set f : ℕ × ℕ → ℂ := fun x => G (x.1 + 1) (x.2 + 1) with hf
  have hT0 : (∑ p ∈ range (0 + 1), ∑ q ∈ range (0 + 1),
      if 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = 0 then G p q else 0) = 0 := by
    simp
  have hTs : ∀ n : ℕ, (∑ p ∈ range (n + 1 + 1), ∑ q ∈ range (n + 1 + 1),
      if 1 ≤ p ∧ 1 ≤ q ∧ unionSize p q 1 = n + 1 then G p q else 0) =
        ∑ kl ∈ antidiagonal n, f kl := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    have h0 : (∑ q ∈ range (n + 1 + 1),
        if 1 ≤ 0 ∧ 1 ≤ q ∧ unionSize 0 q 1 = n + 1 then G 0 q else 0) = 0 := by
      simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [Finset.sum_eq_single (n - a + 1)]
    · rw [if_pos ⟨by omega, by omega, by unfold unionSize; omega⟩]
    · intro q _ hq
      rw [if_neg]
      rintro ⟨_, h2, h3⟩
      apply hq
      unfold unionSize at h3
      omega
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  have hsig : HasSum (fun n => ∑ kl ∈ antidiagonal n, f kl) (∑' x, f x) := by
    have h1 : HasSum (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) (∑' x, f x) :=
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff).mpr hG.hasSum
    refine h1.sigma (fun n => ?_)
    rw [← Finset.sum_coe_sort]
    exact hasSum_fintype _
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton]
  rw [hT0, sub_zero]
  convert hsig using 1
  funext n
  exact hTs n

/-! ### Weighted summability -/

theorem summable_shift_weight {R s : ℝ} (hs : 0 ≤ s) (hsR : s < R) {c : ℕ → ℝ}
    (hc0 : ∀ p, 0 ≤ c p) (hc : Summable fun p => R ^ p * c p) :
    Summable fun a : ℕ => ((a : ℝ) + 1) * c (a + 1) * s ^ a := by
  set t : ℝ := (s + R) / 2 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have hst : s ≤ t := by rw [ht]; linarith
  have htR : t < R := by rw [ht]; linarith
  obtain ⟨K, hK0, hK⟩ := exists_mul_pow_le ht0.le htR
  have hshift : Summable fun a : ℕ => R ^ (a + 1) * c (a + 1) :=
    (summable_nat_add_iff 1).mpr hc
  refine Summable.of_nonneg_of_le (fun a => by have := hc0 (a + 1); positivity)
    (fun a => ?_) (hshift.mul_left (K / t))
  have h1 : ((a : ℝ) + 1) * s ^ a ≤ ((a : ℝ) + 1) * t ^ a :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst a) (by positivity)
  have h2 : ((a : ℝ) + 1) * t ^ a = (((a + 1 : ℕ) : ℝ) * t ^ (a + 1)) / t := by
    push_cast
    field_simp
    ring
  have h3 : ((a : ℝ) + 1) * t ^ a ≤ K * R ^ (a + 1) / t := by
    rw [h2]
    exact div_le_div_of_nonneg_right (hK (a + 1)) ht0.le
  have hca := hc0 (a + 1)
  calc ((a : ℝ) + 1) * c (a + 1) * s ^ a = (((a : ℝ) + 1) * s ^ a) * c (a + 1) := by ring
    _ ≤ (K * R ^ (a + 1) / t) * c (a + 1) := mul_le_mul_of_nonneg_right (h1.trans h3) hca
    _ = K / t * (R ^ (a + 1) * c (a + 1)) := by ring

/-! ### Derivative bounds for the symbol terms -/

theorem kps_eq_symFun' {n : ℕ} (K : BoundedSymmetricKernel H n) :
    kernelProductSymbol K = QuantumNLS.RootSymbolFrechet.symFun n (extendSymKernel K) := by
  funext v
  unfold QuantumNLS.RootSymbolFrechet.symFun kernelProductSymbol
  rw [QuantumNLS.RootOverlapLimit.extend_htpow]

theorem hasFDerivAt_kps {n : ℕ} (K : BoundedSymmetricKernel H n) (x : H) :
    HasFDerivAt (kernelProductSymbol K) (fderiv ℝ (kernelProductSymbol K) x) x := by
  rw [kps_eq_symFun']
  exact ((QuantumNLS.RootSymbolFrechet.contDiff_symFun' n _).differentiable
    (by norm_num) x).hasFDerivAt

theorem norm_fderiv_kps_le {n : ℕ} (K : BoundedSymmetricKernel H n) (x : H) {σ : ℝ}
    (hx : ‖x‖ ≤ σ) :
    ‖fderiv ℝ (kernelProductSymbol K) x‖ ≤ 2 * (n : ℝ) * ‖K‖ * σ ^ n * σ ^ (n - 1) := by
  rcases n with _ | j
  · have hc : kernelProductSymbol K = fun _ => kernelProductSymbol K 0 :=
      funext (fun v => QuantumNLS.RootOverlapLimit.kps_const_zero v)
    rw [hc]
    simp
  · rw [kps_eq_symFun']
    refine (QuantumNLS.RootSymbolFrechet.norm_fderiv_symFun_le j _ x).trans ?_
    have hK := norm_extendSymKernel_le (H := H) K
    have hσ : 0 ≤ σ := (norm_nonneg x).trans hx
    rw [Nat.add_sub_cancel]
    push_cast
    gcongr

theorem norm_kps_le_radius {n : ℕ} (K : BoundedSymmetricKernel H n) {y : H} {R : ℝ}
    (hy : ‖y‖ ^ 2 ≤ R) : ‖kernelProductSymbol K y‖ ≤ R ^ n * ‖K‖ := by
  refine (norm_kernelProductSymbol_le K y).trans ?_
  rw [pow_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hy n) (norm_nonneg K)

theorem summable_deriv_bound {R σ : ℝ} (hσ : 0 ≤ σ) (hσR : σ ^ 2 < R)
    (K : ∀ p : ℕ, BoundedSymmetricKernel H p) (hK : Summable fun p => R ^ p * ‖K p‖) :
    Summable fun n : ℕ => 2 * (n : ℝ) * ‖K n‖ * σ ^ n * σ ^ (n - 1) := by
  apply (summable_nat_add_iff 1).mp
  have h := (summable_shift_weight (sq_nonneg σ) hσR (fun p => norm_nonneg (K p)) hK).mul_left
    (2 * σ)
  refine h.congr (fun j => ?_)
  push_cast
  ring

/-! ### The symbol of the commutator family -/

set_option maxHeartbeats 4000000 in
/-- **The commutator family has symbol `{b, h}`.** If `Σ R^p ‖H_p‖` and `Σ R^p ‖B_p‖` converge,
`R > 1`, and `‖v‖² < R`, then `symbol (commLim Hlim Blim) v = {b, h}(v)`. -/
theorem symbol_commLim {R : ℝ} (hR1 : 1 < R) {Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : Summable fun p => R ^ p * ‖Alim p‖) (hB : Summable fun p => R ^ p * ‖Blim p‖)
    (v : H) (hv : ‖v‖ ^ 2 < R) :
    symbol (commLim Alim Blim) v = pbC (symbol Blim) (symbol Alim) v := by
  set G : ℕ → ℕ → ℂ := fun p q =>
    pbC (kernelProductSymbol (Blim q)) (kernelProductSymbol (Alim p)) v with hGdef
  set s : ℝ := ‖v‖ ^ 2 with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hGb : ∀ a b : ℕ, ‖G (a + 1) (b + 1)‖ ≤
      2 * s * ((((a : ℝ) + 1) * ‖Alim (a + 1)‖ * s ^ a) *
        (((b : ℝ) + 1) * ‖Blim (b + 1)‖ * s ^ b)) := by
    intro a b
    have hp : 1 ≤ a + 1 := Nat.le_add_left 1 a
    have hq : 1 ≤ b + 1 := Nat.le_add_left 1 b
    have hk := norm_kernelProductSymbol_le
      (overlapCommutatorKernel hp hq (Alim (a + 1)) (Blim (b + 1))) v
    have hc := norm_overlapCommutatorKernel_le hp hq (Alim (a + 1)) (Blim (b + 1))
    have hdeg : ‖v‖ ^ (2 * unionSize (a + 1) (b + 1) 1) = s * s ^ a * s ^ b := by
      rw [hsdef]
      simp only [unionSize, Nat.add_sub_cancel]
      ring
    rw [hdeg] at hk
    have hnorm : ‖(-Complex.I) * ((((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        kernelProductSymbol (overlapCommutatorKernel hp hq (Alim (a + 1)) (Blim (b + 1))) v‖ =
        (((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) *
          ‖kernelProductSymbol (overlapCommutatorKernel hp hq (Alim (a + 1)) (Blim (b + 1))) v‖ := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    simp only [hGdef]
    rw [pbC_antisymm, norm_neg, pbC_eq_commSymbol hp hq, hnorm]
    have hk2 : ‖kernelProductSymbol (overlapCommutatorKernel hp hq (Alim (a + 1)) (Blim (b + 1)))
        v‖ ≤ 2 * (‖Alim (a + 1)‖ * ‖Blim (b + 1)‖) * (s * s ^ a * s ^ b) :=
      hk.trans (mul_le_mul_of_nonneg_right hc (by positivity))
    calc ((((a + 1 : ℕ) : ℝ)) * ((b + 1 : ℕ) : ℝ)) *
          ‖kernelProductSymbol (overlapCommutatorKernel hp hq (Alim (a + 1)) (Blim (b + 1))) v‖
        ≤ ((((a + 1 : ℕ) : ℝ)) * ((b + 1 : ℕ) : ℝ)) *
          (2 * (‖Alim (a + 1)‖ * ‖Blim (b + 1)‖) * (s * s ^ a * s ^ b)) :=
          mul_le_mul_of_nonneg_left hk2 (by positivity)
      _ = _ := by push_cast; ring
  have hsumA := summable_shift_weight hs0 hv (fun p => norm_nonneg (Alim p)) hA
  have hsumB := summable_shift_weight hs0 hv (fun p => norm_nonneg (Blim p)) hB
  have hprod := (hsumA.mul_of_nonneg hsumB (fun a => by positivity)
    (fun b => by positivity)).mul_left (2 * s)
  have hsumG : Summable (fun x : ℕ × ℕ => G (x.1 + 1) (x.2 + 1)) :=
    Summable.of_norm_bounded hprod (fun x => hGb x.1 x.2)
  -- the left side: reindexing the degree sum
  have hL : symbol (commLim Alim Blim) v = ∑' x : ℕ × ℕ, G (x.1 + 1) (x.2 + 1) := by
    unfold symbol
    simp only [kps_commLim]
    exact (hasSum_reindex G hsumG).tsum_eq
  -- the right side: the termwise bracket of the two series
  have hvR : ‖v‖ < Real.sqrt R := by
    rw [← Real.sqrt_sq (norm_nonneg v)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hv
  set ρ : ℝ := (Real.sqrt R - ‖v‖) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  set σ : ℝ := ‖v‖ + ρ with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  have hσlt : σ < Real.sqrt R := by rw [hσdef, hρdef]; linarith
  have hσR : σ ^ 2 < R := (Real.lt_sqrt hσ0).mp hσlt
  have hball : ∀ x ∈ ball v ρ, ‖x‖ ≤ σ := by
    intro x hx
    have hd : ‖x - v‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.mp hx
    calc ‖x‖ = ‖v + (x - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖x - v‖ := norm_add_le _ _
      _ ≤ σ := by rw [hσdef]; linarith
  have hball2 : ∀ x ∈ ball v ρ, ‖x‖ ^ 2 ≤ R := fun x hx =>
    (pow_le_pow_left₀ (norm_nonneg x) (hball x hx) 2).trans hσR.le
  have h2 := QuantumNLS.RootComplexInterchange.pbC_hasSum_tsum
    (fun n => kernelProductSymbol (Blim n)) (fun m => kernelProductSymbol (Alim m))
    (fun n x => fderiv ℝ (kernelProductSymbol (Blim n)) x)
    (fun m x => fderiv ℝ (kernelProductSymbol (Alim m)) x)
    (fun n => 2 * (n : ℝ) * ‖Blim n‖ * σ ^ n * σ ^ (n - 1))
    (fun n => 2 * (n : ℝ) * ‖Alim n‖ * σ ^ n * σ ^ (n - 1)) v ρ hρ
    (fun n x _ => hasFDerivAt_kps (Blim n) x) (fun m x _ => hasFDerivAt_kps (Alim m) x)
    (fun n x hx => norm_fderiv_kps_le (Blim n) x (hball x hx))
    (fun m x hx => norm_fderiv_kps_le (Alim m) x (hball x hx))
    (summable_deriv_bound hσ0 hσR Blim hB) (summable_deriv_bound hσ0 hσR Alim hA)
    (fun y hy => Summable.of_norm_bounded hB (fun n => norm_kps_le_radius (Blim n) (hball2 y hy)))
    (fun y hy => Summable.of_norm_bounded hA (fun n => norm_kps_le_radius (Alim n) (hball2 y hy)))
  have hR : pbC (symbol Blim) (symbol Alim) v = ∑' q, ∑' p, G p q := h2.tsum_eq.symm
  have hG0q : ∀ q, G 0 q = 0 := fun q =>
    QuantumNLS.RootOverlapLimit.pbC_zero_right _ _
      (fun w => QuantumNLS.RootOverlapLimit.kps_const_zero w) v
  have hGp0 : ∀ p, G p 0 = 0 := fun p =>
    QuantumNLS.RootOverlapLimit.pbC_zero_left _ _
      (fun w => QuantumNLS.RootOverlapLimit.kps_const_zero w) v
  have hcol : ∀ q, ∑' p, G p q = ∑' a, G (a + 1) q := by
    intro q
    rcases q with _ | b
    · simp only [hGp0, tsum_zero]
    · have hsum : Summable (fun a => G (a + 1) (b + 1)) :=
        hsumG.comp_injective (i := fun a => (a, b)) (fun a1 a2 h => by simpa using h)
      have hsum' : Summable (fun p => G p (b + 1)) :=
        (summable_nat_add_iff (f := fun p => G p (b + 1)) 1).mp hsum
      rw [hsum'.tsum_eq_zero_add, hG0q, zero_add]
  have hrows : Summable (fun q => ∑' a, G (a + 1) q) := h2.summable.congr hcol
  have hswap := (Equiv.prodComm ℕ ℕ).tsum_eq (fun x : ℕ × ℕ => G (x.1 + 1) (x.2 + 1))
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at hswap
  have hsw : Summable (fun y : ℕ × ℕ => G (y.2 + 1) (y.1 + 1)) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr hsumG
  rw [hL, hR, tsum_congr hcol, hrows.tsum_eq_zero_add]
  simp only [hGp0, tsum_zero, zero_add]
  rw [← hswap, hsw.tsum_prod' (fun b => hsw.prod_factor b)]

end QuantumNLS.Local013CommutatorSeries

#print axioms QuantumNLS.Local013CommutatorSeries.pbC_antisymm
#print axioms QuantumNLS.Local013CommutatorSeries.kps_cTerm
#print axioms QuantumNLS.Local013CommutatorSeries.hasSum_reindex
#print axioms QuantumNLS.Local013CommutatorSeries.summable_shift_weight
#print axioms QuantumNLS.Local013CommutatorSeries.norm_fderiv_kps_le
#print axioms QuantumNLS.Local013CommutatorSeries.symbol_commLim
