import Mathlib
import QuantumNLS.Ext006CoreNorm
import QuantumNLS.Ext006VacuumRecurrence
import QuantumNLS.Prop023Scalar

/-! PROP-023 / FIN-CORE-BD-02, stage 2: from the finite-core identity to every weak vacuum.

For a symmetric kernel `K : ℤ → ℤ → ℂ` (no Hilbert-Schmidt or norm hypothesis) and a coefficient
function `ξ : Occ → ℂ` with the weak annihilation property `Ext006VacuumRecurrence.WeakVacuum K ξ`
and `ξ 0 ≠ 0`:

* `core_eq`: on every occupation `m` whose support lies in a finite mode set `S` the literal core
  term `coreTerm S K (total m / 2)` has coefficient `ξ m / ξ 0` (local uniqueness of the weak
  recurrence, proved here for supports inside `S`);
* hence the finite-`S` sector norms `c_S(n) = ‖x_n^S‖²` are the truncated sector probabilities of `ξ`
  (`pS_eq`), which increase to the full probabilities as `S ↑ ℤ`;
* `exists_trace_limits`: the finite traces `tr((K_S^* K_S)^m)` converge (the recurrence determines
  them from the sector norms), nonnegativity and submultiplicativity survive, and the limit
  sequence `t` satisfies the printed recurrence `2 n p_n = ∑_{m=1}^n t_m p_{n-m}` for the sector
  probabilities `p_n` of `ξ` (`weak_vacuum_recurrence`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006CoreLimit
open Occupation Ext006PairCoreCommutator Ext006CoreNorm Ext006VacuumRecurrence
open Filter Topology

/-! ### 1. Coefficients of core operators -/

lemma Ann_coeff (a : ℤ) (v : FS) (m : Occ) :
    (Ann a v) m = (Real.sqrt ((m a : ℝ) + 1) : ℂ) * v (m + e a) := by
  rw [← ip_ket_left m (Ann a v), Ann_adjoint, Cre_ket, ip_smul_left, ip_ket_left,
    Complex.conj_ofReal]

lemma Cre_coeff (a : ℤ) (v : FS) (m : Occ) :
    (Cre a v) m = (Real.sqrt (m a : ℝ) : ℂ) * v (m - e a) := by
  rw [← ip_ket_left m (Cre a v), Cre_adjoint, Ann_ket, ip_smul_left, ip_ket_left,
    Complex.conj_ofReal]

lemma row_coeff (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (a : ℤ) (v : FS) (m : Occ) :
    (rowCreator S K a v) m = ∑ b ∈ S, K a b * ((Real.sqrt (m b : ℝ) : ℂ) * v (m - e b)) := by
  simp only [rowCreator, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Cre_coeff]

lemma pair_coeff (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (v : FS) (m : Occ) :
    (pairCreator S K v) m = ∑ i ∈ S, ∑ j ∈ S, K i j * ((Real.sqrt (m i : ℝ) : ℂ) *
      ((Real.sqrt ((m - e i) j : ℝ) : ℂ) * v (m - e i - e j))) := by
  simp only [pairCreator, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    Cre_coeff]

/-! ### 2. Supports of the core terms -/

def Pred (S : Finset ℤ) (k : ℕ) (m : Occ) : Prop := m.support ⊆ S ∧ total m = k

lemma pair_support (S : Finset ℤ) (K : ℤ → ℤ → ℂ) {k : ℕ} (v : FS)
    (hv : ∀ m, v m ≠ 0 → Pred S k m) : ∀ m, pairCreator S K v m ≠ 0 → Pred S (k + 2) m := by
  intro m hm
  rw [pair_coeff] at hm
  obtain ⟨i, hi, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  obtain ⟨j, hj, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have h1 : (Real.sqrt (m i : ℝ) : ℂ) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hm)
  have h2 : (Real.sqrt ((m - e i) j : ℝ) : ℂ) ≠ 0 :=
    left_ne_zero_of_mul (right_ne_zero_of_mul (right_ne_zero_of_mul hm))
  have h3 : v (m - e i - e j) ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul (right_ne_zero_of_mul hm))
  have hmi : 1 ≤ m i := by
    by_contra hc
    have : m i = 0 := by omega
    simp [this] at h1
  have hmj : 1 ≤ (m - e i) j := by
    by_contra hc
    have : (m - e i) j = 0 := by omega
    simp [this] at h2
  obtain ⟨hs, ht⟩ := hv _ h3
  have t1 := total_sub_e hmi
  have t2 := total_sub_e hmj
  refine ⟨fun c hc => ?_, by omega⟩
  by_cases hci : c = i
  · exact hci ▸ hi
  by_cases hcj : c = j
  · exact hcj ▸ hj
  apply hs
  rw [Finsupp.mem_support_iff] at hc ⊢
  have : (m - e i - e j) c = m c := by
    simp [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hci, Ne.symm hcj]
  rw [this]
  exact hc

lemma coreTerm_support (S : Finset ℤ) (K : ℤ → ℤ → ℂ) (n : ℕ) :
    ∀ m, coreTerm S K n m ≠ 0 → Pred S (2 * n) m := by
  have hw : ∀ n : ℕ, ∀ m, ((pairCreator S K) ^ n) (ket 0) m ≠ 0 → Pred S (2 * n) m := by
    intro n
    induction n with
    | zero =>
      intro m hm
      simp only [pow_zero, Module.End.one_apply] at hm
      have : m = 0 := by
        by_contra hne
        apply hm
        simp [Finsupp.single_apply, Ne.symm hne]
      subst this
      exact ⟨by simp, by simp [total]⟩
    | succ n ih =>
      intro m hm
      rw [pow_succ', Module.End.mul_apply] at hm
      have := pair_support S K _ ih m hm
      simpa [two_mul, mul_add, add_comm, add_left_comm, add_assoc] using
        (show Pred S (2 * n + 2) m from this)
  intro m hm
  apply hw n m
  intro h0
  apply hm
  simp [coreTerm, h0]

/-! ### 3. Local uniqueness of the weak recurrence -/

def LocalVac (S : Finset ℤ) (K : Kernel) (Z : Occ → ℂ) : Prop :=
  ∀ a ∈ S, ∀ m : Occ, m.support ⊆ S →
    (Real.sqrt ((m a : ℝ) + 1) : ℂ) * Z (m + e a) =
      -(∑ b ∈ m.support, K a b * (Real.sqrt (m b : ℝ) : ℂ) * Z (m - e b))

lemma LocalVac.of_weak {S : Finset ℤ} {K : Kernel} {Z : Occ → ℂ} (h : WeakVacuum K Z) :
    LocalVac S K Z := fun a _ m _ => h a m

lemma LocalVac.sub {S : Finset ℤ} {K : Kernel} {Z W : Occ → ℂ} (hZ : LocalVac S K Z)
    (hW : LocalVac S K W) : LocalVac S K (fun m => Z m - W m) := by
  intro a ha m hm
  have h1 := hZ a ha m hm
  have h2 := hW a ha m hm
  simp only [mul_sub, Finset.sum_sub_distrib, h1, h2]
  ring

lemma LocalVac.smul {S : Finset ℤ} {K : Kernel} {Z : Occ → ℂ} (hZ : LocalVac S K Z) (c : ℂ) :
    LocalVac S K (fun m => c * Z m) := by
  intro a ha m hm
  have h1 := hZ a ha m hm
  calc (Real.sqrt ((m a : ℝ) + 1) : ℂ) * (c * Z (m + e a))
      = c * ((Real.sqrt ((m a : ℝ) + 1) : ℂ) * Z (m + e a)) := by ring
    _ = c * (-(∑ b ∈ m.support, K a b * (Real.sqrt (m b : ℝ) : ℂ) * Z (m - e b))) := by rw [h1]
    _ = _ := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

theorem local_zero (S : Finset ℤ) (K : Kernel) {Z : Occ → ℂ} (hZ : LocalVac S K Z)
    (h0 : Z 0 = 0) : ∀ m : Occ, m.support ⊆ S → Z m = 0 := by
  have hz : ∀ k : ℕ, ∀ n : Occ, total n = k → n.support ⊆ S → Z n = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hnk hnS
      by_cases hn : n = 0
      · simpa only [hn] using h0
      obtain ⟨a, ha⟩ : ∃ a, n a ≠ 0 := by
        by_contra! h
        exact hn (Finsupp.ext h)
      have ha' : 1 ≤ n a := Nat.one_le_iff_ne_zero.mpr ha
      have haS : a ∈ S := hnS (Finsupp.mem_support_iff.2 ha)
      have htotal := total_sub_e ha'
      have hsub : (n - e a).support ⊆ S := by
        intro c hc
        apply hnS
        rw [Finsupp.mem_support_iff] at hc ⊢
        intro h0'
        apply hc
        simp [Finsupp.tsub_apply, h0']
      have hs : (∑ b ∈ (n - e a).support,
          K a b * (Real.sqrt ((n - e a) b : ℝ) : ℂ) * Z ((n - e a) - e b)) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hb' : 1 ≤ (n - e a) b :=
          Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
        have ht := total_sub_e hb'
        have hlt : total ((n - e a) - e b) < k := by omega
        have hsub2 : ((n - e a) - e b).support ⊆ S := by
          intro c hc
          apply hsub
          rw [Finsupp.mem_support_iff] at hc ⊢
          intro h0'
          apply hc
          simp [Finsupp.tsub_apply, h0']
        rw [ih _ hlt _ rfl hsub2, mul_zero]
      have he := hZ a haS (n - e a) hsub
      rw [shift_sub_add ha', hs, neg_zero] at he
      have hp : 0 < Real.sqrt (((n - e a) a : ℝ) + 1) :=
        Real.sqrt_pos.mpr (by positivity)
      have hnz : (Real.sqrt (((n - e a) a : ℝ) + 1) : ℂ) ≠ 0 := by
        exact_mod_cast hp.ne'
      exact (mul_eq_zero.mp he).resolve_left hnz
  exact fun n hn => hz (total n) n rfl hn

/-! ### 4. The core terms are the restrictions of every weak vacuum -/

/-- The core terms assembled into one coefficient function (zero in odd sectors). -/
def Y (S : Finset ℤ) (K : Kernel) (m : Occ) : ℂ :=
  if Even (total m) then coreTerm S K (total m / 2) m else 0

lemma Y_of_odd (S : Finset ℤ) (K : Kernel) {m : Occ} (h : ¬ Even (total m)) : Y S K m = 0 := by
  simp [Y, h]

lemma Y_of_even (S : Finset ℤ) (K : Kernel) {m : Occ} {n : ℕ} (h : total m = 2 * n) :
    Y S K m = coreTerm S K n m := by
  have he : Even (total m) := ⟨n, by omega⟩
  simp [Y, he, h]

lemma Y_zero (S : Finset ℤ) (K : Kernel) : Y S K 0 = 1 := by
  rw [Y_of_even S K (n := 0) (by simp [total])]
  simp [coreTerm_zero]

lemma Y_local (S : Finset ℤ) (K : Kernel) (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) :
    LocalVac S K (Y S K) := by
  intro a ha m hm
  rcases Nat.even_or_odd (total m) with he | ho
  · -- even: both sides vanish
    have h1 : ¬ Even (total (m + e a)) := by
      rw [total_add_e]; obtain ⟨r, hr⟩ := he; rw [hr]; intro h; obtain ⟨q, hq⟩ := h; omega
    rw [Y_of_odd S K h1, mul_zero]
    symm
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hb' : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
    have ht := total_sub_e hb'
    have h2 : ¬ Even (total (m - e b)) := by
      obtain ⟨r, hr⟩ := he; intro h; obtain ⟨q, hq⟩ := h; omega
    rw [Y_of_odd S K h2, mul_zero]
  · obtain ⟨n, hn⟩ := ho
    have ht1 : total (m + e a) = 2 * (n + 1) := by rw [total_add_e]; omega
    rw [Y_of_even S K ht1]
    have h := congrArg (fun v : FS => v m) (ann_coreTerm S K hK a ha n)
    simp only [Ann_coeff, Finsupp.coe_neg, Pi.neg_apply, row_coeff] at h
    rw [h]
    congr 1
    have hsub : m.support ⊆ S := hm
    rw [← Finset.sum_subset hsub (fun b _ hb => by
      have : m b = 0 := by simpa using hb
      simp [this])]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
    have ht := total_sub_e hb'
    rw [Y_of_even S K (n := n) (by omega)]
    ring

theorem core_eq (S : Finset ℤ) (K : Kernel) (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) {ξ : Occ → ℂ}
    (hξ : WeakVacuum K ξ) : ∀ m : Occ, m.support ⊆ S → ξ m = ξ 0 * Y S K m := by
  have hZ : LocalVac S K (fun m => ξ m - ξ 0 * Y S K m) :=
    LocalVac.sub (LocalVac.of_weak hξ) (LocalVac.smul (Y_local S K hK) (ξ 0))
  have h0 : (fun m => ξ m - ξ 0 * Y S K m) 0 = 0 := by
    simp [Y_zero]
  intro m hm
  have := local_zero S K hZ h0 m hm
  exact sub_eq_zero.mp this

/-! ### 5. Sector probabilities -/

open Classical in
/-- Truncated sector probability: total mass of `ξ` on `{m : supp m ⊆ S, |m| = 2n}`. -/
def pS (ξ : Occ → ℂ) (S : Finset ℤ) (n : ℕ) : ℝ :=
  ∑' m : Occ, if (m.support ⊆ S ∧ total m = 2 * n) then Complex.normSq (ξ m) else 0

open Classical in
/-- The full sector probability. -/
def pAll (ξ : Occ → ℂ) (n : ℕ) : ℝ :=
  ∑' m : Occ, if total m = 2 * n then Complex.normSq (ξ m) else 0

lemma cc_im (S : Finset ℤ) (K : Kernel) (n : ℕ) : (cc S K n).im = 0 := by
  have h := ip_conj (coreTerm S K n) (coreTerm S K n)
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  unfold cc
  linarith

lemma cc_zero (S : Finset ℤ) (K : Kernel) : cc S K 0 = 1 := by
  unfold cc
  rw [coreTerm_zero, ip_ket_ket]
  simp

lemma cc_re_eq (S : Finset ℤ) (K : Kernel) (n : ℕ) :
    (cc S K n).re = ∑ m ∈ (coreTerm S K n).support, Complex.normSq (coreTerm S K n m) := by
  unfold cc
  exact ip_self_re _

theorem pS_eq (S : Finset ℤ) (K : Kernel) (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) {ξ : Occ → ℂ}
    (hξ : WeakVacuum K ξ) (n : ℕ) :
    pS ξ S n = Complex.normSq (ξ 0) * (cc S K n).re := by
  classical
  rw [cc_re_eq, Finset.mul_sum, pS]
  rw [tsum_eq_sum (s := (coreTerm S K n).support)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hp := coreTerm_support S K n m (Finsupp.mem_support_iff.mp hm)
    have hp' : m.support ⊆ S ∧ total m = 2 * n := hp
    rw [if_pos hp']
    have := core_eq S K hK hξ m hp.1
    rw [Y_of_even S K hp.2] at this
    rw [this, map_mul]
  · intro m hm
    by_cases hp : m.support ⊆ S ∧ total m = 2 * n
    · rw [if_pos hp]
      have h0 : coreTerm S K n m = 0 := by
        by_contra hne
        exact hm (Finsupp.mem_support_iff.mpr hne)
      have := core_eq S K hK hξ m hp.1
      rw [Y_of_even S K hp.2, h0, mul_zero] at this
      rw [this]; simp
    · rw [if_neg hp]

/-- Monotone convergence of the truncated probabilities. -/
theorem pS_tendsto (ξ : Occ → ℂ) (hsum : Summable fun m => Complex.normSq (ξ m)) (n : ℕ) :
    Tendsto (fun N : ℕ => pS ξ (Finset.Icc (-(N : ℤ)) N) n) atTop (nhds (pAll ξ n)) := by
  classical
  unfold pS pAll
  apply tendsto_tsum_of_dominated_convergence (bound := fun m => Complex.normSq (ξ m)) hsum
  · intro m
    have hev : ∀ᶠ N : ℕ in atTop, m.support ⊆ Finset.Icc (-(N : ℤ)) N := by
      obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ c ∈ m.support, |c| ≤ N0 := by
        refine ⟨m.support.sup fun c => c.natAbs, fun c hc => ?_⟩
        have := Finset.le_sup (f := fun c : ℤ => c.natAbs) hc
        have h2 : |c| = (c.natAbs : ℤ) := Int.abs_eq_natAbs c
        rw [h2]; exact_mod_cast this
      filter_upwards [eventually_ge_atTop N0] with N hN c hc
      have := hN0 c hc
      have hab : |c| ≤ (N : ℤ) := this.trans (by exact_mod_cast hN)
      rw [Finset.mem_Icc]
      exact abs_le.mp hab
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    by_cases ht : total m = 2 * n
    · simp [hN, ht]
    · simp [ht]
  · refine Eventually.of_forall fun N m => ?_
    by_cases hp : m.support ⊆ Finset.Icc (-(N : ℤ)) N ∧ total m = 2 * n
    · simp [hp, abs_of_nonneg (Complex.normSq_nonneg _)]
    · simp [hp, Complex.normSq_nonneg]

/-! ### 6. Limits of the traces and the recurrence -/

lemma exists_trace_limits {c t : ℕ → ℕ → ℝ} {cl : ℕ → ℝ} (hc0 : ∀ N, c N 0 = 1)
    (hc : ∀ k, Tendsto (fun N => c N k) atTop (nhds (cl k)))
    (hrec : ∀ (N n : ℕ), 2 * (n : ℝ) * c N n = ∑ m ∈ Finset.range n, c N (n - 1 - m) * t N (m + 1)) :
    ∀ m, ∃ L, Tendsto (fun N => t N (m + 1)) atTop (nhds L) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hex : ∀ j ∈ Finset.range m, ∃ L, Tendsto (fun N => t N (j + 1)) atTop (nhds L) :=
      fun j hj => ih j (Finset.mem_range.1 hj)
    choose! L hL using hex
    refine ⟨2 * ((m : ℝ) + 1) * cl (m + 1) - ∑ j ∈ Finset.range m, cl (m - j) * L j, ?_⟩
    have heq : ∀ N, t N (m + 1) = 2 * ((m : ℝ) + 1) * c N (m + 1) -
        ∑ j ∈ Finset.range m, c N (m - j) * t N (j + 1) := by
      intro N
      have h := hrec N (m + 1)
      rw [Finset.sum_range_succ] at h
      have e : c N (m + 1 - 1 - m) = 1 := by
        rw [show m + 1 - 1 - m = 0 by omega, hc0]
      rw [e] at h
      have e2 : ∑ j ∈ Finset.range m, c N (m + 1 - 1 - j) * t N (j + 1) =
          ∑ j ∈ Finset.range m, c N (m - j) * t N (j + 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show m + 1 - 1 - j = m - j by omega]
      rw [e2] at h
      push_cast at h
      linarith
    simp_rw [heq]
    refine Tendsto.sub (((hc (m + 1)).const_mul _)) ?_
    exact tendsto_finset_sum _ fun j hj => (hc (m - j)).mul (hL j hj)

lemma trace_pow_eq_sum {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (m : ℕ) :
    (A ^ m).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ m := by
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) with hD
  have hUU : star U * U = 1 := by
    rw [hU]; exact (Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2)
  have hUU' : U * star U = 1 := by
    rw [hU]; exact (Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2)
  have hsp : A = U * D * star U := by
    have := hA.spectral_theorem
    simpa [hU, hD, Function.comp_def] using this
  have hpow : ∀ k : ℕ, A ^ k = U * D ^ k * star U := by
    intro k
    induction k with
    | zero => simp [hUU']
    | succ k ih =>
      rw [pow_succ, ih, hsp]
      calc U * D ^ k * star U * (U * D * star U) = U * D ^ k * (star U * U) * D * star U := by
            simp only [mul_assoc]
        _ = U * D ^ (k + 1) * star U := by
            rw [hUU, mul_one, pow_succ]; simp only [mul_assoc]
  rw [hpow m, Matrix.trace_mul_comm, ← mul_assoc, hUU, one_mul, hD,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

open scoped ComplexOrder in
lemma trace_pow_nonneg_submul {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (a b : ℕ) :
    0 ≤ ((A ^ a).trace).re ∧ ((A ^ (a + b)).trace).re ≤ ((A ^ a).trace).re * ((A ^ b).trace).re := by
  have hH := hA.isHermitian
  have hev : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hA.eigenvalues_nonneg i
  have hre : ∀ m : ℕ, ((A ^ m).trace).re = ∑ i, (hH.eigenvalues i) ^ m := by
    intro m
    rw [trace_pow_eq_sum hH m]
    simp [← Complex.ofReal_pow]
  rw [hre, hre, hre]
  refine ⟨Finset.sum_nonneg fun i _ => pow_nonneg (hev i) _, ?_⟩
  rw [Finset.sum_mul_sum]
  calc ∑ i, hH.eigenvalues i ^ (a + b) = ∑ i, hH.eigenvalues i ^ a * hH.eigenvalues i ^ b :=
        Finset.sum_congr rfl fun i _ => pow_add _ _ _
    _ ≤ ∑ i, ∑ j, hH.eigenvalues i ^ a * hH.eigenvalues j ^ b := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.single_le_sum (f := fun j => hH.eigenvalues i ^ a * hH.eigenvalues j ^ b)
          (fun j _ => mul_nonneg (pow_nonneg (hev i) _) (pow_nonneg (hev j) _)) (Finset.mem_univ i)

/-- The finite-level real recurrence. -/
theorem rec_real (S : Finset ℤ) (K : Kernel) (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (n : ℕ) :
    2 * (n : ℝ) * (cc S K n).re =
      ∑ m ∈ Finset.range n, (cc S K (n - 1 - m)).re * (((Tm S K) ^ (m + 1)).trace).re := by
  have h := congrArg Complex.re (trace_recurrence S K hK n)
  rw [Complex.re_sum] at h
  have e1 : (((2 * n : ℕ) : ℂ) * cc S K n).re = 2 * (n : ℝ) * (cc S K n).re := by
    simp [Complex.mul_re]
  rw [e1] at h
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.mul_re, cc_im, zero_mul, sub_zero]

/-- **The recurrence for every weak vacuum.**  For a symmetric kernel `K` (no further hypothesis) and
a summable-square coefficient function `ξ` with the weak annihilation property and `ξ 0 ≠ 0`,
the sector probabilities `p_n = ∑_{|m| = 2n} |ξ_m|²` obey `2 n p_n = ∑_{m=1}^n t_m p_{n-m}` for a
nonnegative submultiplicative sequence `t` (the limit of `tr((K_S^* K_S)^m)`). -/
theorem weak_vacuum_recurrence (K : Kernel) (hK : ∀ i j, K i j = K j i) {ξ : Occ → ℂ}
    (hξ : WeakVacuum K ξ) (hξ0 : ξ 0 ≠ 0) (hsum : Summable fun m => Complex.normSq (ξ m)) :
    ∃ t : ℕ → ℝ, Prop023Scalar.SubMul t ∧
      ∀ n : ℕ, 2 * (n : ℝ) * pAll ξ n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, t x.1 * pAll ξ x.2 := by
  classical
  set SS : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) N with hSS
  have hsym : ∀ N, ∀ i ∈ SS N, ∀ j ∈ SS N, K i j = K j i := fun N i _ j _ => hK i j
  have hn0 : 0 < Complex.normSq (ξ 0) := Complex.normSq_pos.2 hξ0
  set c : ℕ → ℕ → ℝ := fun N k => (cc (SS N) K k).re with hc
  set tt : ℕ → ℕ → ℝ := fun N m => (((Tm (SS N) K) ^ m).trace).re with htt
  set cl : ℕ → ℝ := fun k => pAll ξ k / Complex.normSq (ξ 0) with hcl
  have hc0 : ∀ N, c N 0 = 1 := fun N => by simp [hc, cc_zero]
  have hcN : ∀ N k, c N k = pS ξ (SS N) k / Complex.normSq (ξ 0) := by
    intro N k
    rw [pS_eq (SS N) K (hsym N) hξ k, hc]
    field_simp
  have hclim : ∀ k, Tendsto (fun N => c N k) atTop (nhds (cl k)) := by
    intro k
    simp_rw [hcN]
    exact (pS_tendsto ξ hsum k).div_const _
  have hrec : ∀ (N n : ℕ), 2 * (n : ℝ) * c N n = ∑ m ∈ Finset.range n, c N (n - 1 - m) * tt N (m + 1) :=
    fun N n => rec_real (SS N) K (hsym N) n
  obtain hex := exists_trace_limits hc0 hclim hrec
  choose tl htl using hex
  -- nonnegativity and submultiplicativity pass to the limit
  have hnn : ∀ m, 0 ≤ tl m := by
    intro m
    refine ge_of_tendsto' (htl m) fun N => ?_
    exact (trace_pow_nonneg_submul (Tm_posSemidef (SS N) K) (m + 1) 0).1
  have hsub : ∀ a b, tl (a + b + 1) ≤ tl a * tl b := by
    intro a b
    refine le_of_tendsto_of_tendsto' (htl (a + b + 1)) ((htl a).mul (htl b)) fun N => ?_
    have := (trace_pow_nonneg_submul (Tm_posSemidef (SS N) K) (a + 1) (b + 1)).2
    simpa [htt, show a + 1 + (b + 1) = a + b + 1 + 1 by ring] using this
  refine ⟨fun m => if m = 0 then 0 else tl (m - 1), ⟨by simp, fun k => ?_, fun a b ha hb => ?_⟩, ?_⟩
  · by_cases hk : k = 0
    · simp [hk]
    · simp [hk, hnn]
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have := hsub a' b'
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
    rw [show a' + 1 + (b' + 1) - 1 = a' + b' + 1 by omega]
    exact this
  · intro n
    -- the limit recurrence
    have hlim : Tendsto (fun N => 2 * (n : ℝ) * c N n) atTop (nhds (2 * (n : ℝ) * cl n)) :=
      (hclim n).const_mul _
    have hlim2 : Tendsto (fun N => ∑ m ∈ Finset.range n, c N (n - 1 - m) * tt N (m + 1)) atTop
        (nhds (∑ m ∈ Finset.range n, cl (n - 1 - m) * tl m)) :=
      tendsto_finset_sum _ fun m _ => (hclim _).mul (htl m)
    have heq : 2 * (n : ℝ) * cl n = ∑ m ∈ Finset.range n, cl (n - 1 - m) * tl m := by
      have hfun : (fun N => 2 * (n : ℝ) * c N n) =
          fun N => ∑ m ∈ Finset.range n, c N (n - 1 - m) * tt N (m + 1) :=
        funext fun N => hrec N n
      rw [hfun] at hlim
      exact tendsto_nhds_unique hlim hlim2
    have hp : ∀ k, pAll ξ k = Complex.normSq (ξ 0) * cl k := by
      intro k; simp only [hcl]; field_simp
    have h3 : 2 * (n : ℝ) * pAll ξ n = ∑ m ∈ Finset.range n, pAll ξ (n - 1 - m) * tl m := by
      rw [hp n]
      simp_rw [hp]
      calc 2 * (n : ℝ) * (Complex.normSq (ξ 0) * cl n)
          = Complex.normSq (ξ 0) * (2 * (n : ℝ) * cl n) := by ring
        _ = _ := by
          rw [heq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
    rw [h3, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    simp only [if_true, zero_mul, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show n - (m + 1) = n - 1 - m by omega]
    ring

end QuantumNLS.Ext006CoreLimit
#print axioms QuantumNLS.Ext006CoreLimit.coreTerm_support
#print axioms QuantumNLS.Ext006CoreLimit.local_zero
#print axioms QuantumNLS.Ext006CoreLimit.core_eq
#print axioms QuantumNLS.Ext006CoreLimit.pS_eq
#print axioms QuantumNLS.Ext006CoreLimit.pS_tendsto
#print axioms QuantumNLS.Ext006CoreLimit.weak_vacuum_recurrence
