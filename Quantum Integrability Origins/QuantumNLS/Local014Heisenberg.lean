import QuantumNLS.Local014Dyson

/-!
# LOCAL-014 stage E3: the Heisenberg series at fixed `N`

Source: `source-text/chapters/local/quantum_periods.tex:215-218` (proof of LOCAL-014): "The usual
iterated integral identity for the bounded quantum Hamiltonian, or its entire operator exponential
at each fixed `N`, therefore gives a uniformly norm-convergent Heisenberg series for
`|t| < (eK)^{-1}`, because `k^k/k! ≤ e^k`."

Realization. The operator-exponential route (second printed alternative):
* `exp_conj_hasSum`: in any complex Banach algebra, `e^A X e^{-A} = Σ_k (k!)⁻¹ ad_A^k X`
  (`ad_A = L_A − R_A` with commuting left/right multiplications, `exp(L_A − R_A) = exp(L_A)exp(−R_A)`,
  and `exp(±L/R)` evaluated termwise);
* `opExp x = NormedSpace.exp x` for the operator-norm Banach-algebra structure (on `L(Sym^N)` the
  strong-topology instance is not reducibly the norm topology, so the exponential and the series are
  stated through norms);
* `heisenberg_tendsto`: at fixed `N`, for every bounded `X` on `Sym^N` and real `t`,
  `‖Σ_{k<n} (t^k/k!) δ_N^k X − e^{itNH} X e^{−itNH}‖ → 0` with `δ_N = iN[H, ·]` (`deltaOp`);
* `norm_heisenberg_term_le`: with the Dyson bound of stage E1, the `k`-th term of the series for
  `X = Q_{N,q}(B)` is bounded by `(e K |t|)^k 4^q ‖B‖`, uniformly in `N` (`k^k/k! ≤ e^k`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
noncomputable section
open scoped InnerProductSpace BigOperators Nat
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.Local014Dyson

namespace QuantumNLS.Local014Heisenberg

section Banach

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- `ad_A Y = A Y − Y A` as a continuous linear map. -/
def adL (A : 𝔸) : 𝔸 →L[ℂ] 𝔸 :=
  ContinuousLinearMap.mul ℂ 𝔸 A - (ContinuousLinearMap.mul ℂ 𝔸).flip A

theorem adL_apply (A Y : 𝔸) : adL A Y = A * Y - Y * A := by
  simp [adL]

theorem pow_apply_eq_iterate (T : 𝔸 →L[ℂ] 𝔸) (n : ℕ) (Y : 𝔸) : (T ^ n) Y = T^[n] Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, Function.iterate_succ_apply']

theorem exp_apply_hasSum (T : 𝔸 →L[ℂ] 𝔸) (Y : 𝔸) :
    HasSum (fun n : ℕ => ((n !⁻¹ : ℂ)) • T^[n] Y) (NormedSpace.exp T Y) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).mapL
    (ContinuousLinearMap.apply ℂ 𝔸 Y)
  simpa [pow_apply_eq_iterate] using h

theorem exp_left_apply (A Y : 𝔸) :
    NormedSpace.exp (ContinuousLinearMap.mul ℂ 𝔸 A) Y = NormedSpace.exp A * Y := by
  have h1 := exp_apply_hasSum (ContinuousLinearMap.mul ℂ 𝔸 A) Y
  have hit : ∀ n : ℕ, (ContinuousLinearMap.mul ℂ 𝔸 A)^[n] Y = A ^ n * Y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [pow_succ', mul_assoc]
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mul_right Y
  simp only [hit] at h1
  refine h1.unique ?_
  simpa [smul_mul_assoc] using h2

theorem exp_right_apply (A Y : 𝔸) :
    NormedSpace.exp ((ContinuousLinearMap.mul ℂ 𝔸).flip A) Y = Y * NormedSpace.exp A := by
  have h1 := exp_apply_hasSum ((ContinuousLinearMap.mul ℂ 𝔸).flip A) Y
  have hit : ∀ n : ℕ, ((ContinuousLinearMap.mul ℂ 𝔸).flip A)^[n] Y = Y * A ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [pow_succ, mul_assoc]
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mul_left Y
  simp only [hit] at h1
  refine h1.unique ?_
  simpa [mul_smul_comm] using h2

/-- `e^A X e^{-A} = Σ_k (k!)⁻¹ ad_A^k X` in a complex Banach algebra. -/
theorem exp_conj_hasSum (A X : 𝔸) :
    HasSum (fun n : ℕ => ((n !⁻¹ : ℂ)) • (adL A)^[n] X)
      (NormedSpace.exp A * X * NormedSpace.exp (-A)) := by
  have hcomm : Commute (ContinuousLinearMap.mul ℂ 𝔸 A)
      (-(ContinuousLinearMap.mul ℂ 𝔸).flip A) := by
    refine Commute.neg_right ?_
    ext Y
    simp [mul_assoc]
  have hexp : NormedSpace.exp (adL A) =
      NormedSpace.exp (ContinuousLinearMap.mul ℂ 𝔸 A) *
        NormedSpace.exp (-(ContinuousLinearMap.mul ℂ 𝔸).flip A) := by
    rw [adL, sub_eq_add_neg, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
      ((NormedSpace.expSeries_radius_eq_top ℂ (𝔸 →L[ℂ] 𝔸)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℂ (𝔸 →L[ℂ] 𝔸)).symm ▸ edist_lt_top _ _)]
  have hneg : -(ContinuousLinearMap.mul ℂ 𝔸).flip A = (ContinuousLinearMap.mul ℂ 𝔸).flip (-A) := by
    ext Y; simp
  have hval : NormedSpace.exp (adL A) X = NormedSpace.exp A * X * NormedSpace.exp (-A) := by
    rw [hexp, ContinuousLinearMap.mul_apply, hneg, exp_right_apply, exp_left_apply, mul_assoc]
  rw [← hval]
  exact exp_apply_hasSum (adL A) X

theorem adL_smul_iterate (c : ℂ) (A Y : 𝔸) (n : ℕ) :
    (adL (c • A))^[n] Y = c ^ n • (adL A)^[n] Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_smul, adL_apply,
      adL_apply, pow_succ, mul_smul]
    congr 1
    rw [smul_sub, smul_mul_assoc, mul_smul_comm]

/-- The Banach-algebra exponential `e^x` (`NormedSpace.exp`) for the operator-norm structure. -/
def opExp (x : 𝔸) : 𝔸 := NormedSpace.exp x

/-- Norm form of the Heisenberg series in any complex Banach algebra: if `δ Y = c (A Y − Y A)`, then
`‖Σ_{k<n} (t^k/k!) δ^k X − e^{tcA} X e^{−tcA}‖ → 0`. -/
theorem heisenberg_norm_tendsto (c : ℂ) (A X : 𝔸) (t : ℝ) (δ : 𝔸 → 𝔸)
    (hδ : ∀ Y, δ Y = c • (A * Y - Y * A)) :
    Tendsto (fun n : ℕ => ‖(∑ k ∈ range n, ((t : ℂ) ^ k / (k ! : ℂ)) • δ^[k] X) -
        opExp (((t : ℂ) * c) • A) * X * opExp (-(((t : ℂ) * c) • A))‖) atTop (𝓝 0) := by
  have hδ' : δ = adL (c • A) := by
    funext Y; rw [hδ, adL_apply, smul_sub, smul_mul_assoc, mul_smul_comm]
  have h := exp_conj_hasSum (((t : ℂ) * c) • A) X
  have hA : ((t : ℂ) * c) • A = (t : ℂ) • (c • A) := mul_smul _ _ _
  rw [hA] at h
  have h2 : HasSum (fun k : ℕ => ((t : ℂ) ^ k / (k ! : ℂ)) • δ^[k] X)
      (NormedSpace.exp ((t : ℂ) • (c • A)) * X * NormedSpace.exp (-((t : ℂ) • (c • A)))) := by
    refine h.congr_fun ?_
    intro k
    rw [hδ', adL_smul_iterate (t : ℂ) (c • A), smul_smul]
    congr 1
    ring
  rw [opExp, opExp, hA]
  exact (tendsto_iff_norm_sub_tendsto_zero.mp h2.tendsto_sum_nat)

theorem norm_smul_le' (c : ℂ) (x : 𝔸) : ‖c • x‖ ≤ ‖c‖ * ‖x‖ := norm_smul_le c x

end Banach

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Heisenberg series at fixed `N`** (norm form): for every bounded `X` on `Sym^N` and real `t`,
`‖Σ_{k<n} (t^k/k!) δ_N^k X − e^{itNH} X e^{−itNH}‖ → 0`, `δ_N X = iN[H, X]`. -/
theorem heisenberg_tendsto (N : ℕ) (A X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (t : ℝ) :
    Tendsto (fun n : ℕ => ‖(∑ k ∈ range n, ((t : ℂ) ^ k / (k ! : ℂ)) • (deltaOp N A)^[k] X) -
        opExp ((Complex.I * (t : ℂ) * (N : ℂ)) • A) * X *
          opExp (-((Complex.I * (t : ℂ) * (N : ℂ)) • A))‖) atTop (𝓝 0) := by
  have h := heisenberg_norm_tendsto ((Complex.I : ℂ) * (N : ℂ)) A X t (deltaOp N A)
    (fun Y => rfl)
  have hc : (t : ℂ) * ((Complex.I : ℂ) * (N : ℂ)) = Complex.I * (t : ℂ) * (N : ℂ) := by ring
  rw [hc] at h
  exact h

/-- `k^k / k! ≤ e^k`. -/
theorem pow_div_factorial_le (k : ℕ) : (k : ℝ) ^ k / (k ! : ℝ) ≤ Real.exp 1 ^ k := by
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (by positivity) k
  rw [← Real.exp_one_pow] at h
  exact h

/-- The `k`-th Heisenberg term of a test is bounded by `(eK|t|)^k 4^q ‖B‖`, uniformly in `N`. -/
theorem norm_heisenberg_term_le
    {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N} {K : ℝ}
    (hK : ∀ N, QuantumNLS.RadiusBound.radiusBound 8 (Hk N) ≤ K) {q N : ℕ} (hq : q ≤ N)
    (B : BoundedSymmetricKernel H q) (t : ℝ) (k : ℕ) :
    ‖((t : ℂ) ^ k / (k ! : ℂ)) •
        (deltaOp N (QuantumNLS.RadiusBound.represented (Hk N)))^[k]
          (QuantumNLS.RadiusBound.Q N q hq B)‖ ≤
      (Real.exp 1 * K * |t|) ^ k * (4 ^ q * ‖B‖) := by
  have hK0 : 0 ≤ K :=
    (QuantumNLS.RadiusBound.radiusBound_nonneg (by norm_num) (Hk 0)).trans (hK 0)
  refine (norm_smul_le' (𝔸 := SymSector ℂ H N →L[ℂ] SymSector ℂ H N) _ _).trans ?_
  have hd := norm_dyson_test_le hK hq B k
  have hc : ‖(t : ℂ) ^ k / (k ! : ℂ)‖ = |t| ^ k / (k ! : ℝ) := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    exact_mod_cast Complex.norm_natCast _
  rw [hc]
  have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hB0 : 0 ≤ 4 ^ q * ‖B‖ := by positivity
  calc |t| ^ k / (k ! : ℝ) * ‖(deltaOp N (QuantumNLS.RadiusBound.represented (Hk N)))^[k]
          (QuantumNLS.RadiusBound.Q N q hq B)‖
      ≤ |t| ^ k / (k ! : ℝ) * ((K * k) ^ k * (4 ^ q * ‖B‖)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (K * |t|) ^ k * ((k : ℝ) ^ k / (k ! : ℝ)) * (4 ^ q * ‖B‖) := by
        rw [mul_pow, mul_pow]; field_simp
    _ ≤ (K * |t|) ^ k * Real.exp 1 ^ k * (4 ^ q * ‖B‖) := by
        gcongr
        exact pow_div_factorial_le k
    _ = (Real.exp 1 * K * |t|) ^ k * (4 ^ q * ‖B‖) := by
        rw [mul_assoc (Real.exp 1), mul_pow (Real.exp 1)]; ring

end QuantumNLS.Local014Heisenberg

/-! Axiom audit. -/
#print axioms QuantumNLS.Local014Heisenberg.exp_conj_hasSum
#print axioms QuantumNLS.Local014Heisenberg.heisenberg_norm_tendsto
#print axioms QuantumNLS.Local014Heisenberg.heisenberg_tendsto
#print axioms QuantumNLS.Local014Heisenberg.pow_div_factorial_le
#print axioms QuantumNLS.Local014Heisenberg.norm_heisenberg_term_le
