import Mathlib
import QuantumNLS.KernelDefinition

/-!
# PROP-008 `lem:B4-high-moments`, stage A: rank-centring and the bias bound
(source/chapters/propagation/spectral_calculus.tex:24-60; `eq:B4-rank-centered`, `eq:B4-finite-rank-bias`)

With `c_r = (N)_r/N^r`, `a_r = ⟨u^{⊗r}, A_r u^{⊗r}⟩`, `X_N = A_0 + Σ_{r=1}^N c_r U_{N,r}(A_r)`,
`x = A_0 + Σ_{r≥1} a_r`, `Y_N = Σ_{r=1}^N c_r (U_{N,r}(A_r) − a_r)`:
* `X_N − x = Y_N + b_N` exactly (`centered_identity`), `b_N = Σ_{r≤N}(c_r−1)a_r − Σ_{r>N} a_r`;
* `1 − r(r−1)/(2N) ≤ c_r ≤ 1` for `r ≤ N` (`fallR_bounds`);
* `|b_N| ≤ (Σ r²‖A_r‖ + Σ r‖A_r‖)/N` (`norm_bN_le`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace
open QuantumNLS.KernelDefinition QuantumNLS.TensorCarrier

namespace QuantumNLS.HighMomentsRank

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The falling ratio `(N)_r / N^r`. -/
def fallR (N r : ℕ) : ℝ := (N.descFactorial r : ℝ) / (N : ℝ) ^ r

/-- The coherent symbol `a_r = ⟨u^{⊗r}, A_r u^{⊗r}⟩`. -/
def aa (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (r : ℕ) : ℂ :=
  kernelProductSymbol (A r) u

/-- `U_{N,r}(A_r)` on `Sym^N H`, and `0` for `r > N`. -/
def placed (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N r : ℕ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  if h : r ≤ N then genericU_N_r N r h (A r) else 0

/-- `X_N = A_0 Id + Σ_{r=1}^N (N)_r/N^r U_{N,r}(A_r)`. -/
def Xop (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  A0 • ContinuousLinearMap.id ℂ (SymSector ℂ H N) +
    ∑ j ∈ Finset.range N, ((fallR N (j + 1) : ℝ) : ℂ) • placed A N (j + 1)

/-- `x = A_0 + Σ_{r≥1} a_r`. -/
def xlim (u : H) (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) : ℂ :=
  A0 + ∑' j : ℕ, aa u A (j + 1)

/-- `Y_N = Σ_{r=1}^N c_r (U_{N,r}(A_r) − a_r Id)`. -/
def Yop (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  ∑ j ∈ Finset.range N, ((fallR N (j + 1) : ℝ) : ℂ) •
    (placed A N (j + 1) - aa u A (j + 1) • ContinuousLinearMap.id ℂ (SymSector ℂ H N))

/-- `b_N = Σ_{r=1}^N (c_r − 1) a_r − Σ_{r>N} a_r`. -/
def bN (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, (((fallR N (j + 1) : ℝ) : ℂ) - 1) * aa u A (j + 1) -
    ∑' k : ℕ, aa u A (k + N + 1)

/-! ### Falling-ratio bounds -/

theorem fallR_succ (N r : ℕ) (hN : 0 < N) (hr : r ≤ N) :
    fallR N (r + 1) = fallR N r * (1 - (r : ℝ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  unfold fallR
  rw [Nat.descFactorial_succ, pow_succ]
  have hsub : ((N - r : ℕ) : ℝ) = (N : ℝ) - r := by rw [Nat.cast_sub hr]
  push_cast [hsub]
  field_simp

theorem fallR_bounds (N : ℕ) (hN : 0 < N) :
    ∀ r : ℕ, r ≤ N → 0 ≤ fallR N r ∧
      1 - (r : ℝ) * ((r : ℝ) - 1) / (2 * N) ≤ fallR N r ∧ fallR N r ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro r
  induction r with
  | zero => intro _; simp [fallR]
  | succ r ih =>
    intro hr
    obtain ⟨h0, hlow, hup⟩ := ih (by omega)
    have hrN : (r : ℝ) ≤ N := by exact_mod_cast (show r ≤ N by omega)
    have hq0 : 0 ≤ 1 - (r : ℝ) / N := by
      rw [sub_nonneg, div_le_one hNr]; exact hrN
    have hq1 : 1 - (r : ℝ) / N ≤ 1 := by
      have : (0 : ℝ) ≤ (r : ℝ) / N := by positivity
      linarith
    rw [fallR_succ N r hN (by omega)]
    refine ⟨mul_nonneg h0 hq0, ?_, ?_⟩
    · have ha : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) / (2 * N) ∨ (r : ℝ) = 0 := by
        rcases Nat.eq_zero_or_pos r with h | h
        · right; simp [h]
        · left
          have : (1 : ℝ) ≤ r := by exact_mod_cast h
          have : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
          positivity
      have hb : 0 ≤ (r : ℝ) / N := by positivity
      have key : 1 - (((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) - 1)) / (2 * N) ≤
          (1 - (r : ℝ) * ((r : ℝ) - 1) / (2 * N)) * (1 - (r : ℝ) / N) := by
        have e : (1 - (r : ℝ) * ((r : ℝ) - 1) / (2 * N)) * (1 - (r : ℝ) / N) =
            1 - (r : ℝ) * ((r : ℝ) - 1) / (2 * N) - (r : ℝ) / N +
              (r : ℝ) * ((r : ℝ) - 1) / (2 * N) * ((r : ℝ) / N) := by ring
        have e2 : 1 - (((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) - 1)) / (2 * N) =
            1 - (r : ℝ) * ((r : ℝ) - 1) / (2 * N) - (r : ℝ) / N := by
          push_cast; field_simp; ring
        rw [e, e2]
        rcases ha with ha | ha
        · have := mul_nonneg ha hb
          linarith
        · rw [ha]; simp
      calc _ ≤ (1 - (r : ℝ) * ((r : ℝ) - 1) / (2 * N)) * (1 - (r : ℝ) / N) := key
        _ ≤ fallR N r * (1 - (r : ℝ) / N) := mul_le_mul_of_nonneg_right hlow hq0
    · calc fallR N r * (1 - (r : ℝ) / N) ≤ fallR N r * 1 :=
          mul_le_mul_of_nonneg_left hq1 h0
        _ ≤ 1 := by rw [mul_one]; exact hup

theorem abs_fallR_sub_one_le (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r ≤ N) :
    |fallR N r - 1| ≤ (r : ℝ) ^ 2 / (2 * N) := by
  obtain ⟨_, hlow, hup⟩ := fallR_bounds N hN r hr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_of_nonpos (by linarith)]
  have : (r : ℝ) * ((r : ℝ) - 1) / (2 * N) ≤ (r : ℝ) ^ 2 / (2 * N) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (r : ℝ), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  linarith

/-! ### Operator identity -/

theorem Yop_eq (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    Yop u A N = (∑ j ∈ Finset.range N, ((fallR N (j + 1) : ℝ) : ℂ) • placed A N (j + 1)) -
      (∑ j ∈ Finset.range N, ((fallR N (j + 1) : ℝ) : ℂ) * aa u A (j + 1)) •
        ContinuousLinearMap.id ℂ (SymSector ℂ H N) := by
  unfold Yop
  simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
  congr 1
  exact (Finset.sum_smul ..).symm

theorem bN_eq (u : H) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    bN u A N = (∑ j ∈ Finset.range N, ((fallR N (j + 1) : ℝ) : ℂ) * aa u A (j + 1)) -
      (∑ j ∈ Finset.range N, aa u A (j + 1)) - ∑' k : ℕ, aa u A (k + N + 1) := by
  unfold bN
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]

/-- **Stage A identity**: `X_N − x Id = Y_N + b_N Id`. -/
theorem centered_identity (u : H) (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ)
    (hsum : Summable (fun j : ℕ => aa u A (j + 1))) :
    Xop A0 A N - xlim u A0 A • ContinuousLinearMap.id ℂ (SymSector ℂ H N) =
      Yop u A N + bN u A N • ContinuousLinearMap.id ℂ (SymSector ℂ H N) := by
  have hsplit := hsum.sum_add_tsum_nat_add N
  have e1 : xlim u A0 A = A0 + (∑ j ∈ Finset.range N, aa u A (j + 1)) +
      ∑' k : ℕ, aa u A (k + N + 1) := by
    unfold xlim
    rw [← hsplit, add_assoc]
  rw [Yop_eq, bN_eq, Xop, e1]
  module

/-! ### Bias bound -/

theorem norm_aa_le (u : H) (hu : ‖u‖ = 1) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (r : ℕ) :
    ‖aa u A r‖ ≤ ‖A r‖ := by
  unfold aa kernelProductSymbol
  set x : SymSector ℂ H r := ⟨htpow r u, htpow_mem_symSector r u⟩ with hx
  have h1 : ⟪(htpow r u : HilbertTensorPower ℂ H r), ((A r x : SymSector ℂ H r) :
      HilbertTensorPower ℂ H r)⟫_ℂ = ⟪x, A r x⟫_ℂ := rfl
  rw [h1]
  have hxn : ‖x‖ = 1 := by
    rw [← Submodule.norm_coe]
    show ‖(htpow r u : HilbertTensorPower ℂ H r)‖ = 1
    rw [norm_htpow, hu, one_pow]
  calc ‖⟪x, A r x⟫_ℂ‖ ≤ ‖x‖ * ‖A r x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A r‖ * ‖x‖) := by
        gcongr
        exact (A r).le_opNorm x
    _ = ‖A r‖ := by rw [hxn]; ring

theorem summable_aa (u : H) (hu : ‖u‖ = 1) (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (h1 : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖A (j + 1)‖)) :
    Summable (fun j : ℕ => aa u A (j + 1)) := by
  refine Summable.of_norm_bounded (g := fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖A (j + 1)‖) h1 ?_
  intro j
  refine (norm_aa_le u hu A (j + 1)).trans ?_
  have : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  nlinarith [norm_nonneg (A (j + 1))]

/-- **Bias bound** `|b_N| ≤ (Σ r²‖A_r‖ + Σ r‖A_r‖)/N` (`eq:B4-finite-rank-bias`). -/
theorem norm_bN_le (u : H) (hu : ‖u‖ = 1) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (S1 S2 : ℝ)
    (h1 : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ‖A (j + 1)‖) S1)
    (h2 : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 2 * ‖A (j + 1)‖) S2)
    (N : ℕ) (hN : 0 < N) : ‖bN u A N‖ ≤ (S2 + S1) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set f1 : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) * ‖A (j + 1)‖ with hf1
  set f2 : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ 2 * ‖A (j + 1)‖ with hf2
  have f1nn : ∀ j, 0 ≤ f1 j := fun j => by positivity
  have f2nn : ∀ j, 0 ≤ f2 j := fun j => by positivity
  -- head
  have hhead : ‖∑ j ∈ Finset.range N, (((fallR N (j + 1) : ℝ) : ℂ) - 1) * aa u A (j + 1)‖ ≤
      S2 / (2 * N) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range N,
        ‖(((fallR N (j + 1) : ℝ) : ℂ) - 1) * aa u A (j + 1)‖ ≤ f2 j / (2 * N) := by
      intro j hj
      have hjN : j + 1 ≤ N := Finset.mem_range.mp hj
      rw [norm_mul]
      have e : ((fallR N (j + 1) : ℝ) : ℂ) - 1 = ((fallR N (j + 1) - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      have hb := abs_fallR_sub_one_le N hN (j + 1) hjN
      calc |fallR N (j + 1) - 1| * ‖aa u A (j + 1)‖
          ≤ (((j + 1 : ℕ) : ℝ) ^ 2 / (2 * N)) * ‖A (j + 1)‖ :=
            mul_le_mul hb (norm_aa_le u hu A (j + 1)) (norm_nonneg _) (by positivity)
        _ = f2 j / (2 * N) := by simp only [hf2]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact sum_le_hasSum _ (fun j _ => f2nn j) h2
  -- tail
  have hshift := (hasSum_nat_add_iff' N).mpr h1
  have hshift' : HasSum (fun k : ℕ => f1 (k + N) / N) ((S1 - ∑ i ∈ Finset.range N, f1 i) / N) :=
    hshift.div_const (N : ℝ)
  have htail : ‖∑' k : ℕ, aa u A (k + N + 1)‖ ≤ S1 / N := by
    have hb : ‖∑' k : ℕ, aa u A (k + N + 1)‖ ≤ (S1 - ∑ i ∈ Finset.range N, f1 i) / N := by
      refine tsum_of_norm_bounded hshift' (fun k => ?_)
      refine (norm_aa_le u hu A (k + N + 1)).trans ?_
      have hk : (N : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ k + N + 1)
      have : f1 (k + N) = ((k + N + 1 : ℕ) : ℝ) * ‖A (k + N + 1)‖ := rfl
      rw [this, le_div_iff₀ hNr]
      nlinarith [norm_nonneg (A (k + N + 1))]
    have hs : 0 ≤ ∑ i ∈ Finset.range N, f1 i := Finset.sum_nonneg (fun i _ => f1nn i)
    refine hb.trans ?_
    apply div_le_div_of_nonneg_right _ hNr.le
    linarith
  unfold bN
  refine (norm_sub_le _ _).trans ?_
  have : S2 / (2 * N) + S1 / N ≤ (S2 + S1) / N := by
    have hS2 : 0 ≤ S2 := h2.nonneg f2nn |>.trans_eq' rfl
    have e : (S2 + S1) / N = S2 / N + S1 / N := add_div _ _ _
    have e2 : S2 / (2 * N) ≤ S2 / N := div_le_div_of_nonneg_left hS2 hNr (by linarith)
    rw [e]
    linarith
  linarith

#print axioms norm_bN_le
#print axioms centered_identity

end QuantumNLS.HighMomentsRank
