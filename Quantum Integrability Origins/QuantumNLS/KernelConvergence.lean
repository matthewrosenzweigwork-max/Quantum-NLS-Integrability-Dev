import Mathlib
import QuantumNLS.RadiusBound

/-!
# DEF-042: convergence of the chosen kernel expansions (`source/chapters/local/quantum_periods.tex:100-110`)

Source text (DEF-042): "For this proof, convergence on radius `R` means that the chosen expansion bounds are
uniform on `R` and, for every fixed `p`, `A_{p,N}` converges in operator norm to a bounded kernel `A_p` as
`N → ∞`. This is a property of the specified expansions; no uniqueness of expansions is assumed. The
associated symbol is `a(v) = Σ_{p≥0} ⟨v^{⊗p}, A_p v^{⊗p}⟩`, `‖v‖² < R`."

Realized objects used read-only:
* DEF-050 (`RadiusBound`): `KernelList N = (p : Fin (N+1)) → L(Sym^p H)`, `QuantumNLS.RadiusBound.radiusBound R A = Σ_p R^p ‖A_p‖`,
  `radiusBound_nonneg`, `radiusBound_zero`.
* DEF-041/DEF-004 (`KernelDefinition`, `TensorCarrier`): `BoundedSymmetricKernel H p = L(Sym^p H)`,
  the symbol `kernelProductSymbol A u = ⟨u^{⊗p}, A u^{⊗p}⟩` (the term of `a(v)`), `htpow`, `norm_htpow`
  (`‖u^{⊗p}‖ = ‖u‖^p`), `htpow_mem_symSector` (`u^{⊗p} ∈ Sym^p H`).

Definitions.
* `coeffAt A N p`: the coefficient `A_{p,N}`, the `p`-th kernel of the `N`-th list, and `0` for `p > N`.
  Convention: the source states none for `p > N`; it does not affect any statement, since only `N ≥ p`
  enters the limit `N → ∞`.
* `ConvergesOnRadius R A Alim`: `sup_N QuantumNLS.RadiusBound.radiusBound R (A N) < ∞` (stated as `∃ C, ∀ N, … ≤ C`) and, for every
  fixed `p`, `‖A_{p,N} − A_p‖ → 0` as `N → ∞`. No uniqueness of the expansions is assumed.
* `symbol Alim v = Σ'_p ⟨v^{⊗p}, A_p v^{⊗p}⟩` (`kernelProductSymbol`).

Proved (the summability actually established):
1. `Σ_p R^p ‖A_p‖ ≤ C` (summable, nonnegative terms), from the uniform radius bound and norm convergence
   (partial sums are limits of partial sums of the radius bound).
2. `R^p ‖A_p‖ ≤ C` for every `p` (sup control).
3. For `‖v‖² ≤ R` (the source's `‖v‖² < R` is a special case): the terms satisfy
   `|⟨v^{⊗p}, A_p v^{⊗p}⟩| ≤ ‖A_p‖ ‖v‖^{2p} ≤ R^p ‖A_p‖`, so the series is absolutely summable and
   `|a(v)| ≤ Σ_p R^p ‖A_p‖ ≤ C`.

Not proved here (the source sentence "the series and every fixed derivative converge uniformly on smaller
balls" is a separate result): it is not included.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.LocalPlacement
  QuantumNLS.RadiusBound

namespace QuantumNLS.KernelConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The coefficient `A_{p,N}`: the `p`-th kernel of the `N`-th expansion, and `0` for `p > N`. -/
def coeffAt (A : ∀ N : ℕ, KernelList (H := H) N) (N p : ℕ) : BoundedSymmetricKernel H p :=
  if h : p ≤ N then A N ⟨p, Nat.lt_succ_of_le h⟩ else 0

/-- **Convergence on radius `R`** (DEF-042): uniform radius bound `sup_N Σ_p R^p ‖A_{p,N}‖ < ∞`, and for every
fixed `p`, `A_{p,N} → A_p` in operator norm. -/
def ConvergesOnRadius (R : ℝ) (A : ∀ N : ℕ, KernelList (H := H) N)
    (Alim : ∀ p : ℕ, BoundedSymmetricKernel H p) : Prop :=
  (∃ C : ℝ, ∀ N : ℕ, QuantumNLS.RadiusBound.radiusBound R (A N) ≤ C) ∧
    ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0)

/-- The symbol `a(v) = Σ_p ⟨v^{⊗p}, A_p v^{⊗p}⟩` (DEF-042). -/
def symbol (Alim : ∀ p : ℕ, BoundedSymmetricKernel H p) (v : H) : ℂ :=
  ∑' p : ℕ, kernelProductSymbol (Alim p) v

/-- Each symbol term: `|⟨v^{⊗p}, A v^{⊗p}⟩| ≤ ‖A‖ ‖v‖^{2p}`. -/
theorem norm_kernelProductSymbol_le {p : ℕ} (A : BoundedSymmetricKernel H p) (u : H) :
    ‖kernelProductSymbol A u‖ ≤ ‖A‖ * ‖u‖ ^ (2 * p) := by
  unfold kernelProductSymbol
  set x : SymSector ℂ H p := ⟨htpow p u, htpow_mem_symSector p u⟩ with hx
  have hxn : ‖x‖ = ‖u‖ ^ p :=
    (Submodule.coe_norm x).symm.trans (norm_htpow p u)
  calc ‖inner ℂ (htpow p u : HilbertTensorPower ℂ H p)
        ((A x : SymSector ℂ H p) : HilbertTensorPower ℂ H p)‖
      ≤ ‖(htpow p u : HilbertTensorPower ℂ H p)‖ *
          ‖((A x : SymSector ℂ H p) : HilbertTensorPower ℂ H p)‖ := norm_inner_le_norm _ _
    _ = ‖u‖ ^ p * ‖A x‖ := by rw [norm_htpow, Submodule.coe_norm]
    _ ≤ ‖u‖ ^ p * (‖A‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm A x) (pow_nonneg (norm_nonneg _) _)
    _ = ‖A‖ * ‖u‖ ^ (2 * p) := by
        rw [hxn, two_mul, pow_add]
        ring

/-- The radius bound as a sum over `ℕ` (with the convention `A_{p,N} = 0` for `p > N`). -/
theorem radiusBound_eq_sum_range {R : ℝ} (A : ∀ N : ℕ, KernelList (H := H) N) (N : ℕ) :
    QuantumNLS.RadiusBound.radiusBound R (A N) = ∑ p ∈ Finset.range (N + 1), R ^ p * ‖coeffAt A N p‖ := by
  unfold QuantumNLS.RadiusBound.radiusBound
  rw [← Fin.sum_univ_eq_sum_range (fun p => R ^ p * ‖coeffAt A N p‖) (N + 1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [coeffAt, dif_pos (Nat.lt_succ_iff.mp i.2)]

/-- Generic limit step: `‖f_N − a‖ → 0` implies `‖f_N‖ → ‖a‖` (stated for any seminormed group, so
that the kernel-typed instances are not unfolded). -/
theorem norm_tendsto_of {E : Type*} [SeminormedAddCommGroup E] {f : ℕ → E} {a : E}
    (h : Tendsto (fun N : ℕ => ‖f N - a‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ‖f N‖) atTop (𝓝 ‖a‖) :=
  (tendsto_iff_norm_sub_tendsto_zero.2 h).norm

set_option maxHeartbeats 1000000 in
/-- Partial sums of `R^p ‖A_p‖` are bounded by the uniform radius bound (norm convergence). -/
theorem partial_sum_le {R C : ℝ} (hR : 0 ≤ R) {A : ∀ N : ℕ, KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hC : ∀ N : ℕ, QuantumNLS.RadiusBound.radiusBound R (A N) ≤ C)
    (hlim : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0)) (P : ℕ) :
    ∑ p ∈ Finset.range (P + 1), R ^ p * ‖Alim p‖ ≤ C := by
  have hTn : ∀ p : ℕ, Tendsto (fun N : ℕ => R ^ p * ‖coeffAt A N p‖) atTop
      (𝓝 (R ^ p * ‖Alim p‖)) :=
    fun p => (norm_tendsto_of (E := BoundedSymmetricKernel H p) (f := fun N : ℕ => coeffAt A N p)
      (a := Alim p) (hlim p)).const_mul (R ^ p)
  have hsum : Tendsto (fun N : ℕ => ∑ p ∈ Finset.range (P + 1), R ^ p * ‖coeffAt A N p‖) atTop
      (𝓝 (∑ p ∈ Finset.range (P + 1), R ^ p * ‖Alim p‖)) :=
    tendsto_finset_sum _ (fun p _ => hTn p)
  refine le_of_tendsto hsum ?_
  refine Filter.eventually_atTop.2 ⟨P, fun N hN => ?_⟩
  calc ∑ p ∈ Finset.range (P + 1), R ^ p * ‖coeffAt A N p‖
      ≤ ∑ p ∈ Finset.range (N + 1), R ^ p * ‖coeffAt A N p‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hN))
          (fun p _ _ => mul_nonneg (pow_nonneg hR _) (norm_nonneg (coeffAt A N p)))
    _ = QuantumNLS.RadiusBound.radiusBound R (A N) := (radiusBound_eq_sum_range A N).symm
    _ ≤ C := hC N

/-- All partial sums of `Σ_p R^p ‖A_p‖` are bounded by `C`. -/
theorem partial_sums_le {R C : ℝ} (hR : 0 ≤ R) {A : ∀ N : ℕ, KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hC : ∀ N : ℕ, QuantumNLS.RadiusBound.radiusBound R (A N) ≤ C)
    (hlim : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0)) (n : ℕ) :
    ∑ p ∈ Finset.range n, R ^ p * ‖Alim p‖ ≤ C := by
  rcases n with _ | P
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact (radiusBound_nonneg hR (A 0)).trans (hC 0)
  · exact partial_sum_le hR hC hlim P

/-- **Summability of the radius series** `Σ_p R^p ‖A_p‖` (DEF-042 + DEF-050). -/
theorem radius_summable {R C : ℝ} (hR : 0 ≤ R) {A : ∀ N : ℕ, KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hC : ∀ N : ℕ, QuantumNLS.RadiusBound.radiusBound R (A N) ≤ C)
    (hlim : ∀ p : ℕ, Tendsto (fun N : ℕ => ‖coeffAt A N p - Alim p‖) atTop (𝓝 0)) :
    Summable (fun p : ℕ => R ^ p * ‖Alim p‖) :=
  summable_of_sum_range_le (fun p => mul_nonneg (pow_nonneg hR _) (norm_nonneg (Alim _)))
    (partial_sums_le hR hC hlim)

/-- **Main theorem (DEF-042).** Under `ConvergesOnRadius R A Alim` with `0 ≤ R`:
1. `Σ_p R^p ‖A_p‖` is summable with sum `≤ C`, where `C` bounds the uniform radius bound;
2. `R^p ‖A_p‖ ≤ C` for every `p`;
3. for every `v` with `‖v‖² ≤ R` (in particular `‖v‖² < R`), the terms of the symbol series are absolutely
   summable and the symbol satisfies `‖a(v)‖ ≤ C`. -/
theorem kernel_convergence {R : ℝ} (hR : 0 ≤ R) {A : ∀ N : ℕ, KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p} (h : ConvergesOnRadius R A Alim) :
    ∃ C : ℝ, Summable (fun p : ℕ => R ^ p * ‖Alim p‖) ∧
      ∑' p : ℕ, R ^ p * ‖Alim p‖ ≤ C ∧ (∀ p : ℕ, R ^ p * ‖Alim p‖ ≤ C) ∧
      ∀ v : H, ‖v‖ ^ 2 ≤ R →
        Summable (fun p : ℕ => ‖kernelProductSymbol (Alim p) v‖) ∧ ‖symbol Alim v‖ ≤ C := by
  obtain ⟨⟨C, hC⟩, hlim⟩ := h
  have hsum : Summable (fun p : ℕ => R ^ p * ‖Alim p‖) := radius_summable hR hC hlim
  have htsum : ∑' p : ℕ, R ^ p * ‖Alim p‖ ≤ C :=
    Real.tsum_le_of_sum_range_le (fun p => mul_nonneg (pow_nonneg hR _) (norm_nonneg (Alim _)))
      (partial_sums_le hR hC hlim)
  refine ⟨C, hsum, htsum, fun p => (hsum.le_tsum p (fun j _ =>
    mul_nonneg (pow_nonneg hR _) (norm_nonneg (Alim _)))).trans htsum, fun v hv => ?_⟩
  have hbound : ∀ p : ℕ, ‖kernelProductSymbol (Alim p) v‖ ≤ R ^ p * ‖Alim p‖ := by
    intro p
    refine (norm_kernelProductSymbol_le (Alim p) v).trans ?_
    have hpow : ‖v‖ ^ (2 * p) ≤ R ^ p := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) hv p
    calc ‖Alim p‖ * ‖v‖ ^ (2 * p) ≤ ‖Alim p‖ * R ^ p :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg (Alim p))
      _ = R ^ p * ‖Alim p‖ := mul_comm _ _
  have hnorm : Summable (fun p : ℕ => ‖kernelProductSymbol (Alim p) v‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hsum
  refine ⟨hnorm, ?_⟩
  unfold symbol
  calc ‖∑' p : ℕ, kernelProductSymbol (Alim p) v‖
      ≤ ∑' p : ℕ, ‖kernelProductSymbol (Alim p) v‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : ℕ, R ^ p * ‖Alim p‖ := Summable.tsum_le_tsum hbound hnorm hsum
    _ ≤ C := htsum

/-- The zero family converges on every radius `R ≥ 0` (a sanity instance of DEF-042). -/
theorem convergesOnRadius_zero (R : ℝ) (hR : 0 ≤ R) :
    ConvergesOnRadius (H := H) R (fun _ => 0) (fun _ => 0) := by
  refine ⟨⟨0, fun N => ?_⟩, fun p => ?_⟩
  · rw [radiusBound_zero]
  · refine tendsto_const_nhds.congr (fun N => ?_)
    unfold coeffAt
    split_ifs <;> simp [ContinuousLinearMap.opNorm_zero]

end QuantumNLS.KernelConvergence

/-! Axiom audit (DEF-042). -/
#print axioms QuantumNLS.KernelConvergence.norm_kernelProductSymbol_le
#print axioms QuantumNLS.KernelConvergence.radiusBound_eq_sum_range
#print axioms QuantumNLS.KernelConvergence.partial_sum_le
#print axioms QuantumNLS.KernelConvergence.partial_sums_le
#print axioms QuantumNLS.KernelConvergence.radius_summable
#print axioms QuantumNLS.KernelConvergence.kernel_convergence
#print axioms QuantumNLS.KernelConvergence.convergesOnRadius_zero
