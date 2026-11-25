import Mathlib
import QuantumNLS.Ext006PairCoreCommutator

/-! PROP-023 / FIN-CORE-BD-02, stage 1: the all-degree norm/trace recurrence on the repository's
literal finite-support CCR core.  For a finite mode set `S` and a symmetric kernel `K` on `S`
(`Ext006PairCoreCommutator.coreTerm`, the literal term `(-a*(K)/2)^n Omega/n!`), put
`c_n = <x_n, x_n>` and `T = K^* K` on `S`.  Then

  `2 n c_n = sum_{m=1}^n tr(T^m) c_{n-m}`.

Proof (no Wick sum, no tensor carrier): the Gram matrix `G^{(n)}_{ij} = <a_i x_n, a_j x_n>` satisfies
`G^{(n+1)} = c_n T + K^* (G^{(n)})^T K` (from `a_i x_{n+1} = -sum_k K_{ik} a_k^* x_n`, the CCR and
adjointness), hence `G^{(n)} = sum_{m=1}^n c_{n-m} T^m`; and `sum_i a_i^* a_i x_n = 2 n x_n`.
All inputs are the frozen `Occupation` / `Ext006PairCoreCommutator` statements. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006CoreNorm
open Occupation Ext006PairCoreCommutator

/-! ### 1. Sesquilinear algebra of `ip` -/

lemma ip_sum_right {ι : Type*} (s : Finset ι) (u : FS) (f : ι → FS) :
    ip u (∑ i ∈ s, f i) = ∑ i ∈ s, ip u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ip_add_right, ih]

lemma ip_ket_ket (n m : Occ) : ip (ket n) (ket m) = if m = n then 1 else 0 := by
  rw [ip_ket_left]
  simp [Finsupp.single_apply]

lemma ip_conj (u v : FS) : ip u v = (starRingEnd ℂ) (ip v u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp [ip_zero_left, ip_zero_right]
  | add u u' hu hu' =>
    rw [ip_add_left, ip_add_right, hu, hu', map_add]
  | single n c =>
    rw [single_eq_smul_ket, ip_smul_left, ip_smul_right, map_mul]
    congr 1
    induction v using Finsupp.induction_linear with
    | zero => simp [ip_zero_left, ip_zero_right]
    | add v v' hv hv' =>
      rw [ip_add_right, ip_add_left, hv, hv', map_add]
    | single m d =>
      rw [single_eq_smul_ket, ip_smul_right, ip_smul_left, ip_ket_ket, ip_ket_ket]
      by_cases h : m = n
      · subst h; simp
      · simp [h, Ne.symm h]

theorem Ann_adjoint (a : ℤ) (u v : FS) : ip u (Ann a v) = ip (Cre a u) v := by
  rw [ip_conj u (Ann a v), ← Cre_adjoint a v u, ip_conj, ip_conj (Cre a u) v]
  simp

/-- `<(sum_k alpha_k u_k), (sum_l beta_l v_l)>` expanded. -/
lemma ip_sum_smul {ι κ : Type*} (s : Finset ι) (t : Finset κ) (α : ι → ℂ) (β : κ → ℂ)
    (u : ι → FS) (v : κ → FS) :
    ip (∑ i ∈ s, α i • u i) (∑ j ∈ t, β j • v j) =
      ∑ i ∈ s, ∑ j ∈ t, (starRingEnd ℂ) (α i) * β j * ip (u i) (v j) := by
  rw [ip_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ip_smul_left, ip_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ip_smul_right]
  ring

/-- The Gram identity of two creations. -/
lemma gram_cre (a b : ℤ) (y : FS) :
    ip (Cre a y) (Cre b y) = (if a = b then ip y y else 0) + ip (Ann b y) (Ann a y) := by
  have h1 : ip (Cre a y) (Cre b y) = ip y (Ann a (Cre b y)) := (Ann_adjoint a y _).symm
  have h2 : Ann a (Cre b y) = Cre b (Ann a y) + (if a = b then y else 0) := by
    have := LinearMap.congr_fun (ann_cre a b) y
    simp only [Module.End.mul_apply, LinearMap.add_apply] at this
    rw [this]
    by_cases h : a = b <;> simp [h]
  rw [h1, h2, ip_add_right, Cre_adjoint]
  by_cases h : a = b <;> simp [h, ip_zero_right, add_comm]

/-! ### 2. The Gram matrix recursion for the core terms -/

variable (S : Finset ℤ) (K : ℤ → ℤ → ℂ)

lemma coreTerm_zero : coreTerm S K 0 = ket 0 := by
  simp [coreTerm]

lemma ann_coreTerm_zero (a : ℤ) : Ann a (coreTerm S K 0) = 0 := by
  rw [coreTerm_zero, Ann_ket]
  simp

/-- `c_n = <x_n, x_n>`. -/
def cc (n : ℕ) : ℂ := ip (coreTerm S K n) (coreTerm S K n)

/-- `G^{(n)}_{ij} = <a_i x_n, a_j x_n>`. -/
def GG (n : ℕ) (i j : ℤ) : ℂ := ip (Ann i (coreTerm S K n)) (Ann j (coreTerm S K n))

lemma ann_coreTerm_sum (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (a : ℤ) (ha : a ∈ S) (n : ℕ) :
    Ann a (coreTerm S K (n + 1)) = ∑ k ∈ S, (-K a k) • Cre k (coreTerm S K n) := by
  rw [ann_coreTerm S K hK a ha n]
  simp only [rowCreator, LinearMap.sum_apply, LinearMap.smul_apply, neg_smul,
    Finset.sum_neg_distrib]

lemma GG_succ (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (n : ℕ) {i j : ℤ} (hi : i ∈ S)
    (hj : j ∈ S) :
    GG S K (n + 1) i j = ∑ k ∈ S, ∑ l ∈ S, (starRingEnd ℂ) (K i k) * K j l *
      ((if k = l then cc S K n else 0) + GG S K n l k) := by
  unfold GG
  rw [ann_coreTerm_sum S K hK i hi, ann_coreTerm_sum S K hK j hj, ip_sum_smul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [gram_cre, map_neg, neg_mul_neg]
  rfl

/-- `sum_i a_i^* a_i x_n = 2 n x_n`. -/
theorem number_coreTerm (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (n : ℕ) :
    ∑ i ∈ S, Cre i (Ann i (coreTerm S K n)) = ((2 * n : ℕ) : ℂ) • coreTerm S K n := by
  cases n with
  | zero => simp [ann_coreTerm_zero]
  | succ n =>
    have h1 : ∑ i ∈ S, Cre i (Ann i (coreTerm S K (n + 1))) =
        -(pairCreator S K (coreTerm S K n)) := by
      simp only [pairCreator, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ann_coreTerm S K hK i hi n]
      simp [rowCreator, map_sum, map_smul]
    have h2 : pairCreator S K (coreTerm S K n) =
        (-2 * ((n + 1 : ℕ) : ℂ)) • coreTerm S K (n + 1) := by
      simp only [coreTerm, map_smul, ← Module.End.mul_apply, ← pow_succ']
      rw [smul_smul]
      congr 1
      have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    rw [h1, h2, ← neg_smul]
    congr 1
    push_cast
    ring

/-! ### 3. The matrix solution of the Gram recursion -/

section MatrixPart
open Matrix
open scoped ComplexOrder
variable (S : Finset ℤ) (K : ℤ → ℤ → ℂ)

/-- The kernel as a matrix on the mode set. -/
def Km : Matrix S S ℂ := Matrix.of fun i j => K i j

/-- `T = K^* K` on the mode set. -/
def Tm : Matrix S S ℂ := (Km S K)ᴴ * Km S K

/-- The Gram matrix of `a_i x_n`. -/
def Gm (n : ℕ) : Matrix S S ℂ := Matrix.of fun i j => GG S K n i j

lemma Km_transpose (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) : (Km S K)ᵀ = Km S K := by
  ext i j
  exact hK j j.2 i i.2

lemma Km_conjTranspose_transpose (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) :
    ((Km S K)ᴴ)ᵀ = (Km S K)ᴴ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, Km, Matrix.of_apply]
  rw [hK i i.2 j j.2]

lemma Tm_transpose (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) :
    (Tm S K)ᵀ = Km S K * (Km S K)ᴴ := by
  unfold Tm
  rw [Matrix.transpose_mul, Km_transpose S K hK, Km_conjTranspose_transpose S K hK]

lemma mul_pow_mul_aux {A : Type*} [Monoid A] (a b : A) (p : ℕ) :
    a * (b * a) ^ p = (a * b) ^ p * a := by
  induction p with
  | zero => simp
  | succ p ih =>
    calc a * (b * a) ^ (p + 1) = (a * (b * a) ^ p) * (b * a) := by rw [pow_succ, ← mul_assoc]
      _ = ((a * b) ^ p * a) * (b * a) := by rw [ih]
      _ = (a * b) ^ (p + 1) * a := by rw [pow_succ]; simp only [mul_assoc]

lemma conj_pow_transpose (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (p : ℕ) :
    (Km S K)ᴴ * ((Tm S K) ^ p)ᵀ * Km S K = (Tm S K) ^ (p + 1) := by
  rw [Matrix.transpose_pow, Tm_transpose S K hK, mul_pow_mul_aux (a := (Km S K)ᴴ)
    (b := Km S K) p]
  unfold Tm
  rw [pow_succ, mul_assoc]

lemma Gm_succ (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (n : ℕ) :
    Gm S K (n + 1) = cc S K n • Tm S K + (Km S K)ᴴ * (Gm S K n)ᵀ * Km S K := by
  ext i j
  have h := GG_succ S K hK n i.2 j.2
  have hsym : ∀ a b : S, K a b = K b a := fun a b => hK a a.2 b b.2
  simp only [Gm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Tm, Km,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [h]
  have e1 : ∑ k ∈ S, ∑ l ∈ S, (starRingEnd ℂ) (K i k) * K j l *
      (if k = l then cc S K n else 0) = cc S K n * ∑ k ∈ S, (starRingEnd ℂ) (K i k) * K j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hk, if_true]
    ring
  have e2 : ∑ k ∈ S, ∑ l ∈ S, (starRingEnd ℂ) (K i k) * K j l * GG S K n l k =
      ∑ l : S, (∑ k : S, (starRingEnd ℂ) (K k i) * GG S K n l k) * K l j := by
    rw [← Finset.sum_coe_sort S]
    simp only [← Finset.sum_coe_sort S, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hsym k i, hsym l j]; ring
  have e3 : ∑ k ∈ S, (starRingEnd ℂ) (K i k) * K j k =
      ∑ k : S, (starRingEnd ℂ) (K k i) * K k j := by
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsym k i, hsym k j]
  simp only [mul_add, Finset.sum_add_distrib, add_mul]
  rw [e1, e2, e3]
  simp only [starRingEnd_apply]

lemma Gm_eq (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (n : ℕ) :
    Gm S K n = ∑ m ∈ Finset.range n, cc S K (n - 1 - m) • (Tm S K) ^ (m + 1) := by
  induction n with
  | zero =>
    ext i j
    simp [Gm, GG, ann_coreTerm_zero, ip_zero_left]
  | succ n ih =>
    rw [Gm_succ S K hK, ih, Matrix.transpose_sum, Finset.mul_sum, Finset.sum_mul,
      Finset.sum_range_succ' (fun m => cc S K (n + 1 - 1 - m) • (Tm S K) ^ (m + 1))]
    simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, conj_pow_transpose S K hK]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      congr 2
      omega
    · simp

lemma sum_diag_GG (n : ℕ) : ∑ i ∈ S, GG S K n i i = (Gm S K n).trace := by
  rw [Matrix.trace, ← Finset.sum_coe_sort S]
  rfl

theorem number_ip (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (n : ℕ) :
    ((2 * n : ℕ) : ℂ) * cc S K n = ∑ i ∈ S, GG S K n i i := by
  have h := congrArg (ip (coreTerm S K n)) (number_coreTerm S K hK n)
  rw [ip_sum_right, ip_smul_right] at h
  unfold cc
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Cre_adjoint]
  rfl

/-- **The all-degree norm/trace recurrence** on the literal finite-support core. -/
theorem trace_recurrence (hK : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i) (n : ℕ) :
    ((2 * n : ℕ) : ℂ) * cc S K n =
      ∑ m ∈ Finset.range n, cc S K (n - 1 - m) * ((Tm S K) ^ (m + 1)).trace := by
  rw [number_ip S K hK n, sum_diag_GG, Gm_eq S K hK n, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul]

theorem Tm_posSemidef : (Tm S K).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

end MatrixPart

end QuantumNLS.Ext006CoreNorm
#print axioms QuantumNLS.Ext006CoreNorm.Ann_adjoint
#print axioms QuantumNLS.Ext006CoreNorm.gram_cre
#print axioms QuantumNLS.Ext006CoreNorm.GG_succ
#print axioms QuantumNLS.Ext006CoreNorm.number_coreTerm
#print axioms QuantumNLS.Ext006CoreNorm.trace_recurrence
#print axioms QuantumNLS.Ext006CoreNorm.Tm_posSemidef
