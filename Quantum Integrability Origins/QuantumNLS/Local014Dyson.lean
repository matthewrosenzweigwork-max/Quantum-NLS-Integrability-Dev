import QuantumNLS.Local013Main

/-!
# LOCAL-014 stage E1: iterated commutator lists and the Dyson bound

Source: `source-text/chapters/local/quantum_periods.tex:204-213` (proof of LOCAL-014,
`reset:analytic-egorov`): "Let `K` bound the radius-`8` kernel norms. For `2 ≤ r ≤ 4`,
`Σ_p p r^p ‖H_{p,N}‖ ≤ K`, since `p (r/8)^p ≤ 1`. Use equally spaced radii between `4` and `2` in
(reset:analytic-derivation). For the `k`th iterated commutator of a fixed test one obtains
`‖δ_N^k Q_{N,q}(B)‖_2 ≤ (Kk)^k 4^q ‖B‖ (k ≥ 1)`. This is a bound for an explicit expansion and
hence for its operator norm."

Realized objects (frozen, read-only): DEF-050 `RadiusBound.radiusBound`/`represented`/`Q`;
LOCAL-011 commutator lists `positiveOverlapCommutatorList` and the derivation bound (last clause of
`local011_full_source_ordered_clauses`).

* `deltaOp N A X = iN (A X − X A)` (`δ_N X = iN[H_N, X]`);
* `testList q B N`: the list with the single kernel `B` in degree `q` (the expansion of `Q_{N,q}(B)`
  for `q ≤ N`; the zero list for `q > N`);
* `dysonList Hk X k N`: the `k`-fold iterated LOCAL-011 commutator list of `iN[H_N, ·]`;
* `represented_dysonList`: it represents `δ_N^k (represented (X N))`;
* `weight_le`: `Σ_p p r^p ‖H_{p,N}‖ ≤ ‖H_N‖_8` for `0 ≤ r ≤ 4`;
* `dyson_bound`: `‖δ_N^k X_N‖_2 ≤ (K k)^k ‖X_N‖_4` with equally spaced radii `4 − 2j/k`;
* `dyson_bound_test`, `norm_dyson_test_le`: `‖δ_N^k Q_{N,q}(B)‖_2 ≤ (Kk)^k 4^q ‖B‖` and the same
  operator-norm bound (every `k`, including `k = 0` with `0^0 = 1`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.KernelConvergence
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011

namespace QuantumNLS.Local014Dyson

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "RB" => QuantumNLS.RadiusBound.radiusBound
local notation "REP" => QuantumNLS.RadiusBound.represented

/-- `δ_N X = iN[A, X]` on `Sym^N H`. -/
def deltaOp (N : ℕ) (A X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  ((Complex.I : ℂ) * (N : ℂ)) • (A.comp X - X.comp A)

/-- The test list: the single kernel `B` in degree `q`. -/
def testList (q : ℕ) (B : BoundedSymmetricKernel H q) (N : ℕ) :
    LocalPlacement.KernelList (H := H) N :=
  kernelSpike (H := H) B

/-- Iterated LOCAL-011 commutator lists `δ_N^k X_N`. -/
def dysonList (Hk X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) :
    ℕ → ∀ N : ℕ, LocalPlacement.KernelList (H := H) N
  | 0 => X
  | k + 1 => fun N => positiveOverlapCommutatorList N (Hk N) (dysonList Hk X k N)

theorem dysonList_succ (Hk X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) (k N : ℕ) :
    dysonList Hk X (k + 1) N = positiveOverlapCommutatorList N (Hk N) (dysonList Hk X k N) :=
  rfl

theorem represented_dysonList (Hk X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N)
    (k N : ℕ) :
    REP (dysonList Hk X k N) = (deltaOp N (REP (Hk N)))^[k] (REP (X N)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, dysonList_succ]
    exact (local011_full_source_ordered_clauses (le_refl (1 : ℝ)) one_lt_two (Hk N)
      (dysonList Hk X k N)).2.2.2.2.1

theorem represented_testList {q N : ℕ} (hq : q ≤ N) (B : BoundedSymmetricKernel H q) :
    REP (testList q B N) = QuantumNLS.RadiusBound.Q N q hq B := by
  classical
  rw [QuantumNLS.RadiusBound.Q_eq_genericU_N_r]
  let k : Fin (N + 1) := ⟨q, Nat.lt_succ_of_le hq⟩
  unfold QuantumNLS.RadiusBound.represented testList kernelSpike
  rw [Finset.sum_eq_single k]
  · simp [k, QuantumNLS.RadiusBound.Q_eq_genericU_N_r, castSymSectorOperator]
  · intro j _ hjk
    have hjn : j.1 ≠ q := fun h => hjk (Fin.ext h)
    simpa [QuantumNLS.RadiusBound.Q_eq_genericU_N_r, hjn] using
      QuantumNLS.Local013Powers.genericU_zero_kernel (H := H) (N := N) (n := j.1)
        (Nat.lt_succ_iff.mp j.2)
  · simp [k]

theorem radiusBound_testList_le {q : ℕ} (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (B : BoundedSymmetricKernel H q) :
    RB R (testList q B N) ≤ R ^ q * ‖B‖ := by
  classical
  by_cases hq : q ≤ N
  · let k : Fin (N + 1) := ⟨q, Nat.lt_succ_of_le hq⟩
    unfold QuantumNLS.RadiusBound.radiusBound
    rw [Finset.sum_eq_single k]
    · simp [testList, kernelSpike, k, norm_castSymSectorOperator]
    · intro j _ hjk
      have hjn : j.1 ≠ q := fun h => hjk (Fin.ext h)
      rw [testList, kernelSpike, dif_neg hjn]
      have hzero :
          ‖(0 : SymSector ℂ H j.1 →L[ℂ] SymSector ℂ H j.1)‖ = 0 :=
        norm_zero (E := SymSector ℂ H j.1 →L[ℂ] SymSector ℂ H j.1)
      rw [hzero, mul_zero]
    · simp [k]
  · have h0 : testList q B N = 0 := by
      funext j
      have hjn : j.1 ≠ q := fun h => hq (h ▸ Nat.lt_succ_iff.mp j.2)
      rw [testList, kernelSpike, dif_neg hjn]
      rfl
    rw [h0, QuantumNLS.RadiusBound.radiusBound_zero]
    positivity

/-- `p r^p ≤ 8^p` for `0 ≤ r ≤ 4` (the printed `p (r/8)^p ≤ 1`). -/
theorem mul_pow_le_eight {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 4) (p : ℕ) :
    (p : ℝ) * r ^ p ≤ 8 ^ p := by
  have hp : (p : ℝ) ≤ 2 ^ p := by exact_mod_cast (Nat.lt_two_pow_self).le
  calc (p : ℝ) * r ^ p ≤ 2 ^ p * 4 ^ p :=
        mul_le_mul hp (pow_le_pow_left₀ hr0 hr p) (by positivity) (by positivity)
    _ = 8 ^ p := by rw [← mul_pow]; norm_num

/-- `Σ_p p r^p ‖A_p‖ ≤ ‖A‖_8` for `0 ≤ r ≤ 4`. -/
theorem weight_le {N : ℕ} (A : LocalPlacement.KernelList (H := H) N) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 4) :
    ∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖ ≤ RB 8 A := by
  unfold QuantumNLS.RadiusBound.radiusBound
  exact Finset.sum_le_sum fun p _ =>
    mul_le_mul_of_nonneg_right (mul_pow_le_eight hr0 hr p.1)
      (norm_nonneg (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1))

theorem dyson_bound_aux {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N} {K : ℝ}
    (hK : ∀ N, RB 8 (Hk N) ≤ K) (X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N)
    {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∀ j : ℕ, j ≤ k →
      RB (4 - 2 * j / k) (dysonList Hk X j N) ≤ (K * k) ^ j * RB 4 (X N) := by
  have hK0 : 0 ≤ K :=
    (QuantumNLS.RadiusBound.radiusBound_nonneg (by norm_num) (Hk 0)).trans (hK 0)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  intro j
  induction j with
  | zero =>
    intro _
    show RB (4 - 2 * ((0 : ℕ) : ℝ) / k) (X N) ≤ (K * k) ^ 0 * RB 4 (X N)
    simp
  | succ j ih =>
    intro hj
    have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have ih' := ih (Nat.le_of_succ_le hj)
    set r : ℝ := 4 - 2 * ((j + 1 : ℕ) : ℝ) / k with hr
    set R : ℝ := 4 - 2 * (j : ℝ) / k with hRdef
    have hr2 : 2 ≤ r := by
      rw [hr]; push_cast
      have : 2 * ((j : ℝ) + 1) / k ≤ 2 := by
        rw [div_le_iff₀ hkpos]; linarith
      linarith
    have hr4 : r ≤ 4 := by
      rw [hr]; have : 0 ≤ 2 * (((j + 1 : ℕ) : ℝ)) / k := by positivity
      linarith
    have hRr : R - r = 2 / k := by
      rw [hr, hRdef]; push_cast; field_simp; ring
    have hrR : r < R := by
      have : 0 < 2 / (k : ℝ) := by positivity
      linarith
    have hstep := (local011_full_source_ordered_clauses (by linarith : (1 : ℝ) ≤ r) hrR (Hk N)
      (dysonList Hk X j N)).2.2.2.2.2
    rw [dysonList_succ]
    have hw := (weight_le (Hk N) (by linarith : (0 : ℝ) ≤ r) hr4).trans (hK N)
    have hw0 : 0 ≤ ∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖Hk N p‖ :=
      Finset.sum_nonneg fun p _ => by positivity
    have hB0 : 0 ≤ RB R (dysonList Hk X j N) :=
      QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) _
    have h2 : 2 / (R - r) = k := by rw [hRr]; field_simp
    refine hstep.trans ?_
    rw [h2]
    calc (k : ℝ) * (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖Hk N p‖) *
          RB R (dysonList Hk X j N)
        ≤ k * K * ((K * k) ^ j * RB 4 (X N)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hw hkpos.le) ih' hB0
          positivity
      _ = (K * k) ^ (j + 1) * RB 4 (X N) := by ring

/-- **Dyson bound** for an arbitrary list family: `‖δ_N^k X_N‖_2 ≤ (Kk)^k ‖X_N‖_4`. -/
theorem dyson_bound {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N} {K : ℝ}
    (hK : ∀ N, RB 8 (Hk N) ≤ K) (X : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N)
    (k N : ℕ) :
    RB 2 (dysonList Hk X k N) ≤ (K * k) ^ k * RB 4 (X N) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · show RB 2 (X N) ≤ (K * ((0 : ℕ) : ℝ)) ^ 0 * RB 4 (X N)
    rw [pow_zero, one_mul]
    exact QuantumNLS.RadiusBound.radiusBound_mono (by norm_num) (by norm_num) (X N)
  · have h := dyson_bound_aux hK X hk N k le_rfl
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have h42 : (4 : ℝ) - 2 * k / k = 2 := by field_simp; norm_num
    rwa [h42] at h

/-- **eq:reset:dyson-bound**: `‖δ_N^k Q_{N,q}(B)‖_2 ≤ (Kk)^k 4^q ‖B‖`. -/
theorem dyson_bound_test {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N} {K : ℝ}
    (hK : ∀ N, RB 8 (Hk N) ≤ K) {q : ℕ} (B : BoundedSymmetricKernel H q) (k N : ℕ) :
    RB 2 (dysonList Hk (testList q B) k N) ≤ (K * k) ^ k * (4 ^ q * ‖B‖) := by
  have hK0 : 0 ≤ K :=
    (QuantumNLS.RadiusBound.radiusBound_nonneg (by norm_num) (Hk 0)).trans (hK 0)
  refine (dyson_bound hK _ k N).trans ?_
  exact mul_le_mul_of_nonneg_left (radiusBound_testList_le N (by norm_num) B) (by positivity)

/-- The operator-norm consequence: `‖δ_N^k Q_{N,q}(B)‖ ≤ (Kk)^k 4^q ‖B‖`. -/
theorem norm_dyson_test_le {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N} {K : ℝ}
    (hK : ∀ N, RB 8 (Hk N) ≤ K) {q N : ℕ} (hq : q ≤ N) (B : BoundedSymmetricKernel H q)
    (k : ℕ) :
    ‖(deltaOp N (REP (Hk N)))^[k] (QuantumNLS.RadiusBound.Q N q hq B)‖ ≤
      (K * k) ^ k * (4 ^ q * ‖B‖) := by
  rw [← represented_testList hq B, ← represented_dysonList]
  exact (QuantumNLS.RadiusBound.norm_le_radiusBound (by norm_num : (1 : ℝ) ≤ 2) rfl).trans
    (dyson_bound_test hK B k N)

end QuantumNLS.Local014Dyson

/-! Axiom audit. -/
#print axioms QuantumNLS.Local014Dyson.represented_dysonList
#print axioms QuantumNLS.Local014Dyson.represented_testList
#print axioms QuantumNLS.Local014Dyson.radiusBound_testList_le
#print axioms QuantumNLS.Local014Dyson.weight_le
#print axioms QuantumNLS.Local014Dyson.dyson_bound
#print axioms QuantumNLS.Local014Dyson.dyson_bound_test
#print axioms QuantumNLS.Local014Dyson.norm_dyson_test_le
