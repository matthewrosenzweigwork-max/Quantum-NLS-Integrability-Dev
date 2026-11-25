import Mathlib
import QuantumNLS.MixedTraceNorm
import QuantumNLS.NormalizedTransfer
import QuantumNLS.RootOverlapCommutator

/-!
# PROP-026 remainder 2: the commutator estimate `eq:MP-local-commutator` for the transfer quadratures

Source: `source/chapters/propagation/mixed_propagation.tex`, proof of `lem:MP-linearization` (PROP-026, line 355):
"Two averaged placements commute when their coordinate sets are disjoint.  The chance of an intersection is at most
`jk/N`.  Consequently `eq:MP-transfer`-`eq:MP-kernel` imply `‖[S_N(z),J_N]‖ + ‖[S_N(z)^*,J_N]‖ ≤ Ck‖J‖/N`."
Here `J_N = 𝒰_{N,k}(J)` and `S_N(z) = (1+e(z))1 + Σ_{j=1}^N κ^j (N)_j/N^j 𝒰_{N,j}(K_{j,z})` (`eq:MP-transfer`).

## Proved (imports read-only: `MixedTraceNorm` b05d6b39, `NormalizedTransfer` (DEF-048), `RootOverlapCommutator`)
* `commutator_placementSeries_le` (generic Hilbert space `E`): for every placement series `c·1 + Σ_{j<N} a_j U_{N,j+1}(K_j)`
  and every `J` on `Sym^k`, `N ‖[T, U_{N,k}(J)]‖ ≤ 2k‖J‖ Σ_j (j+1)‖a_j‖‖K_j‖`.  This is the printed placement count: it is
  `RootOverlapCommutator.root_overlap_bound` (`N‖[Q_{N,p}(A),Q_{N,q}(B)]‖ ≤ 2pq‖A‖‖B‖`, disjoint placements commute, the
  intersection probability is `≤ pq/N`) summed with the coefficients.
* `sum_weight_le`: `Σ_{j<N} (j+1) x^{j+1}/√((2(j+1))!) ≤ x e^x` (from `(m!)^2 ∣ (2m)!`), so the series sum is bounded
  independently of `N`.
* `commutator_normalizedTransfer_le`: for the REALIZED DEF-048 operator `normalizedTransfer L κ N z` (not an abstract
  stand-in), given the kernel bound `|κ|^r‖K_{r,z}‖ ≤ B(|κ|L)^r/√((2r)!)` for `1 ≤ r ≤ N` (this is `eq:MP-kernel` with
  `B = 2e^{L|Im z|}`; hypothesis `hker`),
  `N ‖[S_N(z), U_{N,k}(J)]‖ ≤ 2k‖J‖ · B (|κ|L) e^{|κ|L}`.
* `commutator_adjoint_normalizedTransfer_le`: the same for `S_N(z)^*`, via the realized DEF-048 identity
  `S_N(z)^* = e^{-iL\bar z} S_N(\bar z)` (`normalizedTransfer_adjoint`), with the extra factor `|e^{-iL\bar z}| = e^{-L Im z}
  ≤ e^{L|Im z|}` (`norm_adjointPhase_le`).
* `commutator_quadrature_le`: for any quadrature `T = α S_N(z) + β S_N(z)^*`, `‖α‖+‖β‖ ≤ 1` (covers `Re S`, `Im S`):
  `N ‖[T, U_{N,k}(J)]‖ ≤ e^{L|Im z|} · 2k‖J‖ B(|κ|L)e^{|κ|L}`, i.e. `C k ‖J‖ / N` with `C = C(L,κ,Im z)` independent of `N`.
* `genericU_add_eq`: `genericU_N_r (k+q) k = U_N_r (r := k) (q := q)` (the cast along `k+(k+q-k)=k+q` is trivial).
* **`prop026_traceNorm_transfer`**: `MixedTraceNorm.prop026_traceNorm` with `E = L²(𝕋_L)`, `N = k+q`, in which the
  commutator hypothesis `hJ` is DISCHARGED from `hquad` (each `B_{θ,j}` is such a quadrature of the realized
  `S_N(z_θ)`, `|Im z_θ| ≤ h`) and `hker` (`eq:MP-kernel` on the strip) with the explicit constant
  `C_J = e^{Lh} · 2k · 2e^{Lh}(|κ|L)e^{|κ|L}` (contractions `J`).  Everything else (operator-norm Bochner interpretation of
  PROP-014, an explicit labelled interpretation, not an owner ruling) is inherited unchanged.

## Not done (exact remaining statements; hypotheses of the final theorem)
* `hker` (`eq:MP-kernel`: `κ^j‖K_{j,z}‖ ≤ 2e^{L|Im z|}(κL)^j/√(2j)!`) is NOT proved: `NormalizedTransfer` records that the
  sharp kernel bound is not available in the frozen modules (their raw-operator bound is cruder).  It is an explicit
  hypothesis; `κ^j` is read as `|κ|^j` (for `κ > 0`, the source's case, identical).
* `hquad` (that the abstract commuting quadratures `Φ θ (coordC j)` of PROP-014 ARE `Re/Im S_N(z_θ)` along the contour)
  is a hypothesis: this is remainder 3 (the identification of `F_θ`, `b_θ`, `L_N` with `f_z(S_N(z))`, `s(z)`, `eq:MP-L`,
  which needs the unrealized `D, A, s, G`, the contours and the chart extensions `f_z`).  This module proves only that
  IF they are such quadratures, the commutator bound needed by PROP-026 holds with the printed `C k ‖J‖/N` shape.
* The source's contour-sum/integral bookkeeping in `|p_t(z)|·|dz|` is not repeated here (it lives in `MixedLinearization`
  through the weight `w` and `δ`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate Nat ContDiff
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition

noncomputable section

namespace QuantumNLS.MixedCommutator

/-- Operator norm of a scalar multiple (proved on vectors; avoids `NormSMulClass` on `B(Sym^N)`). -/
theorem norm_smul_clm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℂ)
    (f : V →L[ℂ] V) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  calc ‖(c • f) x‖ = ‖c‖ * ‖f x‖ := by rw [ContinuousLinearMap.smul_apply, norm_smul]
    _ ≤ ‖c‖ * (‖f‖ * ‖x‖) := mul_le_mul_of_nonneg_left (f.le_opNorm x) (norm_nonneg _)
    _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `c·1 + Σ_{j<N} a_j U_{N,j+1}(K_j)`: the placement series (the shape of `eq:MP-transfer`). -/
def placementSeries (N : ℕ) (c : ℂ) (a : Fin N → ℂ)
    (K : ∀ j : Fin N, BoundedSymmetricKernel E (j.val + 1)) :
    SymSector ℂ E N →L[ℂ] SymSector ℂ E N :=
  c • ContinuousLinearMap.id ℂ _ + ∑ j : Fin N, a j • genericU_N_r N (j.val + 1) j.2 (K j)

theorem commutator_placementSeries (N : ℕ) (c : ℂ) (a : Fin N → ℂ)
    (K : ∀ j : Fin N, BoundedSymmetricKernel E (j.val + 1))
    (X : SymSector ℂ E N →L[ℂ] SymSector ℂ E N) :
    placementSeries N c a K * X - X * placementSeries N c a K =
      ∑ j : Fin N, a j • (genericU_N_r N (j.val + 1) j.2 (K j) * X -
        X * genericU_N_r N (j.val + 1) j.2 (K j)) := by
  have hc : (c • ContinuousLinearMap.id ℂ (SymSector ℂ E N)) * X =
      X * (c • ContinuousLinearMap.id ℂ (SymSector ℂ E N)) := by
    ext x; simp
  have hsum : ∀ (U : Fin N → (SymSector ℂ E N →L[ℂ] SymSector ℂ E N)),
      (∑ j : Fin N, a j • U j) * X - X * (∑ j : Fin N, a j • U j) =
        ∑ j : Fin N, a j • (U j * X - X * U j) := by
    intro U
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext x
    simp [smul_sub]
  have := hsum (fun j => genericU_N_r N (j.val + 1) j.2 (K j))
  simp only [placementSeries, add_mul, mul_add, hc]
  rw [← this]
  abel

/-- **The placement count (`eq:MP-local-commutator` for a placement series).**
`N ‖[Σ a_j U_{N,j}(K_j) + c, U_{N,k}(J)]‖ ≤ 2k‖J‖ Σ_j j‖a_j‖‖K_j‖`. -/
theorem commutator_placementSeries_le (N k : ℕ) (hk : k ≤ N) (c : ℂ) (a : Fin N → ℂ)
    (K : ∀ j : Fin N, BoundedSymmetricKernel E (j.val + 1)) (J : BoundedSymmetricKernel E k) :
    (N : ℝ) * ‖placementSeries N c a K * genericU_N_r N k hk J -
        genericU_N_r N k hk J * placementSeries N c a K‖ ≤
      2 * k * ‖J‖ * ∑ j : Fin N, ((j : ℝ) + 1) * ‖a j‖ * ‖K j‖ := by
  rw [commutator_placementSeries, Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le (Finset.univ : Finset (Fin N))
    (fun j : Fin N => a j • (genericU_N_r N (j.val + 1) j.2 (K j) * genericU_N_r N k hk J -
      genericU_N_r N k hk J * genericU_N_r N (j.val + 1) j.2 (K j))))
    (Nat.cast_nonneg N)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hs := norm_smul_clm_le (a j) (genericU_N_r N (j.val + 1) j.2 (K j) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * genericU_N_r N (j.val + 1) j.2 (K j))
  have h := QuantumNLS.RootOverlapCommutator.root_overlap_bound N (j.val + 1) k j.2 hk (K j) J
  have h' : (N : ℝ) * ‖genericU_N_r N (j.val + 1) j.2 (K j) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * genericU_N_r N (j.val + 1) j.2 (K j)‖ ≤
      2 * (((j.val + 1 : ℕ) : ℝ) * k) * ‖K j‖ * ‖J‖ := by
    simpa [ContinuousLinearMap.mul_def] using h
  calc (N : ℝ) * ‖a j • (genericU_N_r N (j.val + 1) j.2 (K j) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * genericU_N_r N (j.val + 1) j.2 (K j))‖
      ≤ (N : ℝ) * (‖a j‖ * ‖genericU_N_r N (j.val + 1) j.2 (K j) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * genericU_N_r N (j.val + 1) j.2 (K j)‖) :=
        mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
    _ = ‖a j‖ * ((N : ℝ) * ‖genericU_N_r N (j.val + 1) j.2 (K j) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * genericU_N_r N (j.val + 1) j.2 (K j)‖) := by ring
    _ ≤ ‖a j‖ * (2 * (((j.val + 1 : ℕ) : ℝ) * k) * ‖K j‖ * ‖J‖) :=
        mul_le_mul_of_nonneg_left h' (norm_nonneg _)
    _ = 2 * k * ‖J‖ * (((j : ℝ) + 1) * ‖a j‖ * ‖K j‖) := by push_cast; ring

end Generic

section Numeric

theorem sum_weight_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    ∑ j : Fin N, ((j : ℝ) + 1) *
        (x ^ (j.val + 1) / Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ)) ≤ x * Real.exp x := by
  have hterm : ∀ j : ℕ, ((j : ℝ) + 1) *
      (x ^ (j + 1) / Real.sqrt (((2 * (j + 1))! : ℕ) : ℝ)) ≤ x * (x ^ j / (j ! : ℝ)) := by
    intro j
    have hdvd : (j + 1)! * (j + 1)! ∣ (2 * (j + 1))! := by
      have := Nat.factorial_mul_factorial_dvd_factorial_add (j + 1) (j + 1)
      rwa [← two_mul] at this
    have h2 := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    have hfac : (((j + 1)! : ℕ) : ℝ) ≤ Real.sqrt (((2 * (j + 1))! : ℕ) : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      rw [sq]
      exact_mod_cast h2
    have hpos : (0 : ℝ) < (((j + 1)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hx1 : 0 ≤ x ^ (j + 1) := pow_nonneg hx _
    calc ((j : ℝ) + 1) * (x ^ (j + 1) / Real.sqrt (((2 * (j + 1))! : ℕ) : ℝ))
        ≤ ((j : ℝ) + 1) * (x ^ (j + 1) / (((j + 1)! : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left hx1 hpos hfac
      _ = x * (x ^ j / (j ! : ℝ)) := by
          rw [Nat.factorial_succ]
          push_cast
          have : (j ! : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
          field_simp
          ring
  calc ∑ j : Fin N, ((j : ℝ) + 1) *
        (x ^ (j.val + 1) / Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ))
      = ∑ j ∈ Finset.range N, ((j : ℝ) + 1) *
        (x ^ (j + 1) / Real.sqrt (((2 * (j + 1))! : ℕ) : ℝ)) :=
        Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j : ℝ) + 1) *
          (x ^ (j + 1) / Real.sqrt (((2 * (j + 1))! : ℕ) : ℝ))) N
    _ ≤ ∑ j ∈ Finset.range N, x * (x ^ j / (j ! : ℝ)) := Finset.sum_le_sum fun j _ => hterm j
    _ = x * ∑ j ∈ Finset.range N, x ^ j / (j ! : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x * Real.exp x := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx N) hx

end Numeric

section Transfer

open QuantumNLS.NormalizedTransfer QuantumNLS.HighMomentsRank QuantumNLS.PhysicalTensor

variable (L : ℝ) [Fact (0 < L)]

theorem normalizedTransfer_eq_placementSeries (κ : ℝ) (N : ℕ) (z : ℂ) :
    normalizedTransfer L κ N z =
      placementSeries N (1 + Complex.exp (Complex.I * z * L))
        (fun j : Fin N => (((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ))
        (fun j : Fin N => orderedKernel L (j.val + 1) z) := rfl

/-- **`eq:MP-local-commutator` for the realized transfer `S_N(z)` (DEF-048), part `[S_N(z),J_N]`.**  Given the kernel
bound of `eq:MP-kernel` (hypothesis `hker`, constant `B`, `x = |κ| L`):
`N ‖[S_N(z), U_{N,k}(J)]‖ ≤ 2k‖J‖ B x e^x`. -/
theorem commutator_normalizedTransfer_le (κ : ℝ) (N k : ℕ) (hk : k ≤ N) (z : ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hker : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      |κ| ^ r * ‖orderedKernel L r z‖ ≤
        B * (|κ| * L) ^ r / Real.sqrt (((2 * r)! : ℕ) : ℝ))
    (J : BoundedSymmetricKernel (L2T L) k) :
    (N : ℝ) * ‖normalizedTransfer L κ N z * genericU_N_r N k hk J -
        genericU_N_r N k hk J * normalizedTransfer L κ N z‖ ≤
      2 * k * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L))) := by
  rw [normalizedTransfer_eq_placementSeries]
  refine (commutator_placementSeries_le N k hk _ _ _ J).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hx : 0 ≤ |κ| * L := mul_nonneg (abs_nonneg _) (Fact.out : 0 < L).le
  calc ∑ j : Fin N, ((j : ℝ) + 1) *
        ‖(((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ)‖ *
        ‖orderedKernel L (j.val + 1) z‖
      ≤ ∑ j : Fin N, B * (((j : ℝ) + 1) *
          ((|κ| * L) ^ (j.val + 1) / Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) j.2
        obtain ⟨hf0, -, hf1⟩ := fallR_bounds N hNpos (j.val + 1) j.2
        have hnorm : ‖(((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ)‖ ≤ |κ| ^ (j.val + 1) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hf0]
          calc |κ| ^ (j.val + 1) * fallR N (j.val + 1) ≤ |κ| ^ (j.val + 1) * 1 :=
                mul_le_mul_of_nonneg_left hf1 (by positivity)
            _ = _ := mul_one _
        have hk1 := hker (j.val + 1) (by omega) j.2
        calc ((j : ℝ) + 1) * ‖(((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ)‖ *
              ‖orderedKernel L (j.val + 1) z‖
            ≤ ((j : ℝ) + 1) * (|κ| ^ (j.val + 1) * ‖orderedKernel L (j.val + 1) z‖) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hnorm (ContinuousLinearMap.opNorm_nonneg _)) (by positivity)
          _ ≤ ((j : ℝ) + 1) * (B * (|κ| * L) ^ (j.val + 1) /
                Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hk1 (by positivity)
          _ = B * (((j : ℝ) + 1) *
              ((|κ| * L) ^ (j.val + 1) / Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ))) := by ring
    _ = B * ∑ j : Fin N, ((j : ℝ) + 1) *
          ((|κ| * L) ^ (j.val + 1) / Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ B * ((|κ| * L) * Real.exp (|κ| * L)) :=
        mul_le_mul_of_nonneg_left (sum_weight_le _ hx N) hB

end Transfer

section AbstractComm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem comm_smul_le (c : ℂ) (S X : V →L[ℂ] V) :
    ‖(c • S) * X - X * (c • S)‖ ≤ ‖c‖ * ‖S * X - X * S‖ := by
  have : (c • S) * X - X * (c • S) = c • (S * X - X * S) := by
    ext x; simp [smul_sub]
  rw [this]
  exact norm_smul_clm_le _ _

theorem comm_add_smul_le (α β : ℂ) (S S' X : V →L[ℂ] V) :
    ‖(α • S + β • S') * X - X * (α • S + β • S')‖ ≤
      ‖α‖ * ‖S * X - X * S‖ + ‖β‖ * ‖S' * X - X * S'‖ := by
  have : (α • S + β • S') * X - X * (α • S + β • S') =
      α • (S * X - X * S) + β • (S' * X - X * S') := by
    ext x; simp [smul_sub]; abel
  rw [this]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_smul_clm_le _ _) (norm_smul_clm_le _ _))

end AbstractComm

section Transfer2

open QuantumNLS.NormalizedTransfer QuantumNLS.HighMomentsRank QuantumNLS.PhysicalTensor

variable (L : ℝ) [Fact (0 < L)]

theorem norm_adjointPhase_le (z : ℂ) :
    ‖QuantumNLS.BetheTransferKernelAdjoint.adjointPhase L z‖ ≤ Real.exp (L * |z.im|) := by
  rw [QuantumNLS.BetheTransferKernelAdjoint.adjointPhase, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h : (-Complex.I * (L : ℂ) * conj z).re = -(L * z.im) := by simp
  rw [h]
  have hL : 0 < L := Fact.out
  have := neg_abs_le z.im
  nlinarith [le_abs_self z.im]

/-- The adjoint part `[S_N(z)^*, J_N]`: `S_N(z)^* = e^{-iL\bar z} S_N(\bar z)` (DEF-048), `|e^{-iL\bar z}| = e^{-L Im z}`. -/
theorem commutator_adjoint_normalizedTransfer_le (κ : ℝ) (N k : ℕ) (hk : k ≤ N) (z : ℂ) {B : ℝ}
    (hB : 0 ≤ B)
    (hker : ∀ r : ℕ, 1 ≤ r → r ≤ N →
      |κ| ^ r * ‖orderedKernel L r (conj z)‖ ≤
        B * (|κ| * L) ^ r / Real.sqrt (((2 * r)! : ℕ) : ℝ))
    (J : BoundedSymmetricKernel (L2T L) k) :
    (N : ℝ) * ‖(normalizedTransfer L κ N z).adjoint * genericU_N_r N k hk J -
        genericU_N_r N k hk J * (normalizedTransfer L κ N z).adjoint‖ ≤
      Real.exp (L * |z.im|) * (2 * k * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L)))) := by
  have hc := commutator_normalizedTransfer_le L κ N k hk (conj z) hB hker J
  have h1 := comm_smul_le (QuantumNLS.BetheTransferKernelAdjoint.adjointPhase L z)
    (normalizedTransfer L κ N (conj z)) (genericU_N_r N k hk J)
  rw [← normalizedTransfer_adjoint] at h1
  have hph := norm_adjointPhase_le L z
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * ‖(normalizedTransfer L κ N z).adjoint * genericU_N_r N k hk J -
        genericU_N_r N k hk J * (normalizedTransfer L κ N z).adjoint‖
      ≤ (N : ℝ) * (‖QuantumNLS.BetheTransferKernelAdjoint.adjointPhase L z‖ *
        ‖normalizedTransfer L κ N (conj z) * genericU_N_r N k hk J -
          genericU_N_r N k hk J * normalizedTransfer L κ N (conj z)‖) :=
        mul_le_mul_of_nonneg_left h1 hN0
    _ = ‖QuantumNLS.BetheTransferKernelAdjoint.adjointPhase L z‖ *
        ((N : ℝ) * ‖normalizedTransfer L κ N (conj z) * genericU_N_r N k hk J -
          genericU_N_r N k hk J * normalizedTransfer L κ N (conj z)‖) := by ring
    _ ≤ Real.exp (L * |z.im|) * (2 * k * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L)))) :=
        mul_le_mul hph hc (mul_nonneg hN0 (ContinuousLinearMap.opNorm_nonneg _))
          (Real.exp_pos _).le

/-- The quadratures: any `T = α S_N(z) + β S_N(z)^*` with `‖α‖ + ‖β‖ ≤ 1` (e.g. `Re S`, `Im S`). -/
theorem quad_arith (a b C e : ℝ) (ha : 0 ≤ a) (_hb : 0 ≤ b) (hC : 0 ≤ C) (he : 1 ≤ e) :
    a * C + b * (e * C) ≤ (a + b) * (e * C) := by
  have : C ≤ e * C := le_mul_of_one_le_left hC he
  nlinarith

theorem commutator_quadrature_le (κ : ℝ) (N k : ℕ) (hk : k ≤ N) (z : ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hker : ∀ w : ℂ, w = z ∨ w = conj z → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      |κ| ^ r * ‖orderedKernel L r w‖ ≤
        B * (|κ| * L) ^ r / Real.sqrt (((2 * r)! : ℕ) : ℝ))
    (α β : ℂ) (hαβ : ‖α‖ + ‖β‖ ≤ 1) (J : BoundedSymmetricKernel (L2T L) k) :
    (N : ℝ) * ‖(α • normalizedTransfer L κ N z + β • (normalizedTransfer L κ N z).adjoint) *
          genericU_N_r N k hk J -
        genericU_N_r N k hk J *
          (α • normalizedTransfer L κ N z + β • (normalizedTransfer L κ N z).adjoint)‖ ≤
      Real.exp (L * |z.im|) * (2 * k * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L)))) := by
  have h1 := commutator_normalizedTransfer_le L κ N k hk z hB (hker z (Or.inl rfl)) J
  have h2 := commutator_adjoint_normalizedTransfer_le L κ N k hk z hB
    (hker (conj z) (Or.inr rfl)) J
  have hq := comm_add_smul_le α β (normalizedTransfer L κ N z)
    (normalizedTransfer L κ N z).adjoint (genericU_N_r N k hk J)
  have hC : 0 ≤ 2 * (k : ℝ) * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L))) := by
    have hL : 0 < L := Fact.out
    positivity
  have hE : 1 ≤ Real.exp (L * |z.im|) := Real.one_le_exp (by
    have hL : 0 < L := Fact.out
    positivity)
  have hCe : 2 * (k : ℝ) * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L))) ≤
      Real.exp (L * |z.im|) * (2 * (k : ℝ) * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L)))) :=
    le_mul_of_one_le_left hC hE
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * ‖(α • normalizedTransfer L κ N z + β • (normalizedTransfer L κ N z).adjoint) *
          genericU_N_r N k hk J -
        genericU_N_r N k hk J *
          (α • normalizedTransfer L κ N z + β • (normalizedTransfer L κ N z).adjoint)‖
      ≤ (N : ℝ) * (‖α‖ * ‖normalizedTransfer L κ N z * genericU_N_r N k hk J -
            genericU_N_r N k hk J * normalizedTransfer L κ N z‖ +
          ‖β‖ * ‖(normalizedTransfer L κ N z).adjoint * genericU_N_r N k hk J -
            genericU_N_r N k hk J * (normalizedTransfer L κ N z).adjoint‖) :=
        mul_le_mul_of_nonneg_left hq hN0
    _ = ‖α‖ * ((N : ℝ) * ‖normalizedTransfer L κ N z * genericU_N_r N k hk J -
            genericU_N_r N k hk J * normalizedTransfer L κ N z‖) +
          ‖β‖ * ((N : ℝ) * ‖(normalizedTransfer L κ N z).adjoint * genericU_N_r N k hk J -
            genericU_N_r N k hk J * (normalizedTransfer L κ N z).adjoint‖) := by ring
    _ ≤ ‖α‖ * (2 * (k : ℝ) * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L)))) +
          ‖β‖ * (Real.exp (L * |z.im|) *
            (2 * (k : ℝ) * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L))))) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ ≤ (‖α‖ + ‖β‖) * (Real.exp (L * |z.im|) *
            (2 * (k : ℝ) * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L))))) :=
        quad_arith _ _ _ _ (norm_nonneg α) (norm_nonneg β) hC hE
    _ ≤ 1 * (Real.exp (L * |z.im|) *
            (2 * (k : ℝ) * ‖J‖ * (B * ((|κ| * L) * Real.exp (|κ| * L))))) :=
        mul_le_mul_of_nonneg_right hαβ (by positivity)
    _ = _ := one_mul _

end Transfer2

section Final

open QuantumNLS.FunctionalLinearization QuantumNLS.NormalizedTransfer QuantumNLS.PhysicalTensor
open MeasureTheory

/-- `genericU_N_r (k+q) k` is `U_N_r (r := k) (q := q)` (the cast along `k + (k+q-k) = k+q` is the identity). -/
theorem genericU_add_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (k q : ℕ) (hk : k ≤ k + q) (J : BoundedSymmetricKernel E k) :
    genericU_N_r (k + q) k hk J = U_N_r (r := k) (q := q) J := by
  have key : ∀ (q' : ℕ) (e : q' = q) (h : k + q' = k + q),
      castSymSectorOperator h (U_N_r (r := k) (q := q') J) = U_N_r (r := k) (q := q) J := by
    intro q' e h
    subst e
    rfl
  exact key (k + q - k) (by omega) (Nat.add_sub_of_le hk)

set_option maxHeartbeats 2000000 in
/-- **PROP-026 (trace-norm form) with `hJ` discharged for the realized transfer.**  Same as
`MixedTraceNorm.prop026_traceNorm` with `E = L²(𝕋_L)`, `N = k + q`, except that the commutator hypothesis `hJ` is
replaced by (i) `hquad`: each `B_{θ,j}` is a quadrature `α S_N(z_θ) + β S_N(z_θ)^*`, `‖α‖+‖β‖ ≤ 1`, of the
realized DEF-048 transfer (`NormalizedTransfer.normalizedTransfer`) at a point `z_θ` of the strip `|Im z| ≤ h`; and
(ii) `hker`: the kernel bound `eq:MP-kernel`, `|κ|^r‖K_{r,w}‖ ≤ 2e^{L|Im w|}(|κ|L)^r/√((2r)!)` on the strip.
The resulting `C_J = e^{Lh} · 2k · 2e^{Lh} (|κ|L) e^{|κ|L}` (i.e. `C k` with `C = C(L,κ,h)`, for contractions `J`). -/
theorem prop026_traceNorm_transfer (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        (L : ℝ) [Fact (0 < L)] (κ : ℝ) (k q : ℕ) (hN : 1 ≤ k + q)
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ]
          (SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q)))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hKQ : K ⊆ Q) (hbQ : ∀ θ, b θ ∈ Q)
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (phi : SymSector ℂ (L2T L) (k + q)) (hphi : ‖phi‖ = 1)
        (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
        (hphiδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) •
          (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤ δ θ)
        (z : Θ → ℂ) (h : ℝ) (hz : ∀ θ, |(z θ).im| ≤ h)
        (hquad : ∀ θ j, ∃ α β : ℂ, ‖α‖ + ‖β‖ ≤ 1 ∧
          Φ θ (coordC j) = α • normalizedTransfer L κ (k + q) (z θ) +
            β • (normalizedTransfer L κ (k + q) (z θ)).adjoint)
        (hker : ∀ w : ℂ, |w.im| ≤ h → ∀ r : ℕ, 1 ≤ r →
          |κ| ^ r * ‖orderedKernel L r w‖ ≤
            2 * Real.exp (L * |w.im|) * (|κ| * L) ^ r / Real.sqrt (((2 * r)! : ℕ) : ℝ))
        (w : Θ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hw : Integrable w ν)
        (hwδ : Integrable (fun θ => w θ * δ θ) ν)
        {M0 : ℝ} (hM0 : 0 ≤ M0)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ w θ * M0),
        QuantumNLS.TraceClass.traceNorm
          (reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) • C0N ν Φ F) 1 phi : SymSector ℂ (L2T L) (k + q)) :
                HilbertTensorPower ℂ (L2T L) (k + q)) -
            reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) • LN ν Φ F b) 1 phi : SymSector ℂ (L2T L) (k + q)) :
                HilbertTensorPower ℂ (L2T L) (k + q))) ≤
          ENNReal.ofReal ((C0 * (C1 * M0)) * (∫ θ, w θ * δ θ ∂ν) *
            (Real.exp (L * h) * (2 * k * (2 * Real.exp (L * h) *
              ((|κ| * L) * Real.exp (|κ| * L)))))) := by
  obtain ⟨m, C0, hm, hC0, hmain⟩ := QuantumNLS.MixedTraceNorm.prop026_traceNorm d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hmain hU hQ hQU
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ L _ κ k q hN Φ F hF b hKQ hbQ hcomm hB hFm hdF phi hphi δ hδ hphiδ
    z h hz hquad hker w hw0 hw hwδ {M0} hM0 hFb => ?_⟩
  have hLpos : 0 < L := Fact.out
  have hNpos : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hN
  have hCJ : 0 ≤ Real.exp (L * h) * (2 * k * (2 * Real.exp (L * h) *
      ((|κ| * L) * Real.exp (|κ| * L)))) := by positivity
  refine hC1b ν (E := L2T L) k q Φ F hF b hKQ hbQ hcomm hB hFm hdF ((k + q : ℕ) : ℝ) hNpos phi hphi
    δ hδ hphiδ hCJ ?_ w hw0 hw hwδ hM0 hFb
  intro J hJ θ j
  obtain ⟨α, β, hαβ, hΦ⟩ := hquad θ j
  have hk : k ≤ k + q := Nat.le_add_right k q
  have hB0 : (0 : ℝ) ≤ 2 * Real.exp (L * h) := by positivity
  have hker' : ∀ w' : ℂ, w' = z θ ∨ w' = conj (z θ) → ∀ r : ℕ, 1 ≤ r → r ≤ k + q →
      |κ| ^ r * ‖orderedKernel L r w'‖ ≤
        (2 * Real.exp (L * h)) * (|κ| * L) ^ r / Real.sqrt (((2 * r)! : ℕ) : ℝ) := by
    intro w' hw' r hr _
    have him : |w'.im| ≤ h := by
      rcases hw' with rfl | rfl
      · exact hz θ
      · simpa using hz θ
    refine (hker w' him r hr).trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : Real.exp (L * |w'.im|) ≤ Real.exp (L * h) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him hLpos.le)
    linarith
  have hcomm' := commutator_quadrature_le L κ (k + q) k hk (z θ) hB0 hker' α β hαβ J
  rw [genericU_add_eq k q hk J] at hcomm'
  rw [hΦ]
  rw [le_div_iff₀ hNpos, mul_comm]
  refine hcomm'.trans ?_
  have hzim : Real.exp (L * |(z θ).im|) ≤ Real.exp (L * h) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hz θ) hLpos.le)
  have hJ0 : ‖J‖ ≤ 1 := hJ
  have hX : 0 ≤ (2 * Real.exp (L * h)) * ((|κ| * L) * Real.exp (|κ| * L)) := by positivity
  calc Real.exp (L * |(z θ).im|) * (2 * k * ‖J‖ * ((2 * Real.exp (L * h)) *
        ((|κ| * L) * Real.exp (|κ| * L))))
      ≤ Real.exp (L * h) * (2 * k * 1 * ((2 * Real.exp (L * h)) *
        ((|κ| * L) * Real.exp (|κ| * L)))) := by
        apply mul_le_mul hzim _ (by positivity) (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ hX
        have : (0 : ℝ) ≤ 2 * k := by positivity
        nlinarith
    _ = Real.exp (L * h) * (2 * k * (2 * Real.exp (L * h) *
          ((|κ| * L) * Real.exp (|κ| * L)))) := by ring

end Final

end QuantumNLS.MixedCommutator

#print axioms QuantumNLS.MixedCommutator.commutator_placementSeries_le
#print axioms QuantumNLS.MixedCommutator.sum_weight_le
#print axioms QuantumNLS.MixedCommutator.commutator_normalizedTransfer_le
#print axioms QuantumNLS.MixedCommutator.commutator_adjoint_normalizedTransfer_le
#print axioms QuantumNLS.MixedCommutator.commutator_quadrature_le
#print axioms QuantumNLS.MixedCommutator.genericU_add_eq
#print axioms QuantumNLS.MixedCommutator.prop026_traceNorm_transfer
