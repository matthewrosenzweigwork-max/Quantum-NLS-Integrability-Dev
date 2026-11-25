import QuantumNLS.Prop022OPairBridge
import QuantumNLS.Prop022SmoothDomainR126

/-! PROP-022 takeover, stage O4a. The actual physical quadratic Hamiltonian
Q(a,b) = dGamma(a) + (1/2)(a*(b) + a(b)), acting through its second-moment
root (the R125 strong operator), has the following exact ket matrix
elements: for every finite mode set S containing both supports,
  <k| Q |m> = <k| QFS S |m>,
where QFS S is the finite CCR-core polynomial
  sum_{i,j in S} a_ij Cre i Ann j + (c_ij/2) Cre i Cre j + (conj c_ij/2) Ann j Ann i.
The sector-vanishing, moment-domain and smoothness facts used later are
also proved here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022OQuadraticKet
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Occupation Ext006PhysicalCoreR39a Ext006KernelHilbertSchmidt Ext006PhysFockCoord
open Ext005Moments Ext005FormScaleR109 Ext005FormCutoffR109 Ext005MomentEnergyR108
open Ext005PhysicalNumberFormR114 Ext005PhysicalHalfPairR114 Ext005ComplexRieszR113
open Prop022StrongOperatorR125 Prop022OPairBridge Prop022ONumberBridge Prop022TensorCompressionR115
open Ext005PhysicalPairFormR114
variable {L : ℝ} [Fact (0 < L)]

/-- The physical quadratic Hamiltonian through its second-moment root. -/
def Qp (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (x : Fock L) : Fock L :=
  strongCoordinates a b (rootLift 2 x)

lemma embedding_rootLift (x : Fock L) (hx : x ∈ momentDomain (L := L) 1) :
    embedding 1 (rootLift 1 x) = x := by
  rw [rootLift_eq 1 x hx]
  exact embedding_root 1 ⟨x, hx⟩

/-- The sector form of every matrix element of Q. -/
theorem Qp_matrix (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (x y : Fock L)
    (hx : x ∈ momentDomain (L := L) 2) (hy : y ∈ momentDomain (L := L) 1) :
    ⟪y, Qp a b x⟫_ℂ = (∑' n, ⟪y n, Ext005QuadraticEnergyR108.numberBlock a n (x n)⟫_ℂ) +
      (1/2 : ℂ) * ((∑' n, ⟪y n, Ext005PairSector.annihilation b n (x (2+n))⟫_ℂ) +
        ∑' n, ⟪y (2+n), Ext005PairSector.creation b n (x n)⟫_ℂ) := by
  have hx1 : x ∈ momentDomain (L := L) 1 := domain_mono (by omega) hx
  have hq := quadraticAction_form a b ⟨x, hx⟩ (rootLift 1 y)
  rw [embedding_rootLift y hy] at hq
  have hQ : Qp a b x = quadraticAction a b ⟨x, hx⟩ := by
    rw [Qp, quadraticAction, rootLift_eq 2 x hx]
    rfl
  rw [hQ, hq]
  change numberContinuous a (rootLift 1 x) (rootLift 1 y) +
    halfPair b (rootLift 1 x) (rootLift 1 y) = _
  rw [numberContinuous_offDiagonal, halfPair_offDiagonal]
  simp only [sectorTerm, embedding_rootLift x hx1, embedding_rootLift y hy]

/-! ### Single-sector vectors -/

lemma inclusion_apply_self (N : ℕ) (y : HN L N) : inclusion L N y N = y := by
  change (lp.single 2 N y : Fock L) N = y
  rw [lp.single_apply, Pi.single_eq_same]

lemma inclusion_apply_ne (N n : ℕ) (y : HN L N) (h : n ≠ N) : inclusion L N y n = 0 := by
  change (lp.single 2 N y : Fock L) n = 0
  rw [lp.single_apply, Pi.single_eq_of_ne h]

lemma inclusion_mem (j N : ℕ) (y : HN L N) : inclusion L N y ∈ momentDomain (L := L) j := by
  rw [momentDomain_iff]
  apply summable_of_ne_finset_zero (s := {N})
  intro n hn
  rw [inclusion_apply_ne N n y (by simpa using hn), norm_zero]
  ring

lemma physCore_mem (j : ℕ) (v : FS) : physCore (L := L) v ∈ momentDomain (L := L) j := by
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | single m c =>
    rw [show (Finsupp.single m c : FS) = c • ket m by simp, map_smul]
    apply Submodule.smul_mem
    rw [physCore_ket_sector (L := L) (⟨m, rfl⟩ : Arr (total m))]
    exact inclusion_mem j _ _

/-- Number-preserving matrix elements. -/
lemma Qp_number (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (N : ℕ) (z y : HN L N) :
    ⟪inclusion L N z, Qp a b (inclusion L N y)⟫_ℂ =
      ⟪z, Ext005QuadraticEnergyR108.numberBlock a N y⟫_ℂ := by
  rw [Qp_matrix a b _ _ (inclusion_mem 2 N y) (inclusion_mem 1 N z)]
  have h1 : (∑' n, ⟪inclusion L N z n, Ext005QuadraticEnergyR108.numberBlock a n
      (inclusion L N y n)⟫_ℂ) = ⟪z, Ext005QuadraticEnergyR108.numberBlock a N y⟫_ℂ := by
    rw [tsum_eq_single N, inclusion_apply_self, inclusion_apply_self]
    intro n hn
    rw [inclusion_apply_ne N n z hn, inner_zero_left]
  have h2 : (∑' n, ⟪inclusion L N z n, Ext005PairSector.annihilation b n
      (inclusion L N y (2+n))⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : n = N
    · subst hn
      rw [inclusion_apply_ne _ (2+n) y (by omega), map_zero, inner_zero_right]
    · rw [inclusion_apply_ne N n z hn, inner_zero_left]
  have h3 : (∑' n, ⟪inclusion L N z (2+n), Ext005PairSector.creation b n
      (inclusion L N y n)⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : n = N
    · subst hn
      rw [inclusion_apply_ne _ (2+n) z (by omega), inner_zero_left]
    · rw [inclusion_apply_ne N n y hn, map_zero, inner_zero_right]
  rw [h1, h2, h3]
  ring

/-- Pair-creation matrix elements. -/
lemma Qp_creation (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (N : ℕ) (z : HN L (2+N)) (y : HN L N) :
    ⟪inclusion L (2+N) z, Qp a b (inclusion L N y)⟫_ℂ =
      (1/2 : ℂ) * ⟪z, Ext005PairSector.creation b N y⟫_ℂ := by
  rw [Qp_matrix a b _ _ (inclusion_mem 2 N y) (inclusion_mem 1 (2+N) z)]
  have h1 : (∑' n, ⟪inclusion L (2+N) z n, Ext005QuadraticEnergyR108.numberBlock a n
      (inclusion L N y n)⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : n = N
    · subst hn
      rw [inclusion_apply_ne _ n z (by omega), inner_zero_left]
    · rw [inclusion_apply_ne N n y hn, map_zero, inner_zero_right]
  have h2 : (∑' n, ⟪inclusion L (2+N) z n, Ext005PairSector.annihilation b n
      (inclusion L N y (2+n))⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : n = 2+N
    · subst hn
      rw [inclusion_apply_ne N _ y (by omega), map_zero, inner_zero_right]
    · rw [inclusion_apply_ne _ n z hn, inner_zero_left]
  have h3 : (∑' n, ⟪inclusion L (2+N) z (2+n), Ext005PairSector.creation b n
      (inclusion L N y n)⟫_ℂ) = ⟪z, Ext005PairSector.creation b N y⟫_ℂ := by
    rw [tsum_eq_single N, inclusion_apply_self, inclusion_apply_self]
    intro n hn
    rw [inclusion_apply_ne N n y hn, map_zero, inner_zero_right]
  rw [h1, h2, h3]
  ring

/-- Pair-annihilation matrix elements. -/
lemma Qp_annihilation (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (N : ℕ) (z : HN L N)
    (y : HN L (2+N)) :
    ⟪inclusion L N z, Qp a b (inclusion L (2+N) y)⟫_ℂ =
      (1/2 : ℂ) * ⟪z, Ext005PairSector.annihilation b N y⟫_ℂ := by
  rw [Qp_matrix a b _ _ (inclusion_mem 2 (2+N) y) (inclusion_mem 1 N z)]
  have h1 : (∑' n, ⟪inclusion L N z n, Ext005QuadraticEnergyR108.numberBlock a n
      (inclusion L (2+N) y n)⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : n = N
    · subst hn
      rw [inclusion_apply_ne _ n y (by omega), map_zero, inner_zero_right]
    · rw [inclusion_apply_ne N n z hn, inner_zero_left]
  have h2 : (∑' n, ⟪inclusion L N z n, Ext005PairSector.annihilation b n
      (inclusion L (2+N) y (2+n))⟫_ℂ) = ⟪z, Ext005PairSector.annihilation b N y⟫_ℂ := by
    rw [tsum_eq_single N, inclusion_apply_self, inclusion_apply_self]
    intro n hn
    rw [inclusion_apply_ne N n z hn, inner_zero_left]
  have h3 : (∑' n, ⟪inclusion L N z (2+n), Ext005PairSector.creation b n
      (inclusion L (2+N) y n)⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : 2+n = N
    · rw [inclusion_apply_ne _ n y (by omega), map_zero, inner_zero_right]
    · rw [inclusion_apply_ne N (2+n) z hn, inner_zero_left]
  rw [h1, h2, h3]
  ring

/-- All other sector pairs have zero matrix elements. -/
lemma Qp_other (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (K N : ℕ) (z : HN L K) (y : HN L N)
    (h1 : K ≠ N) (h2 : K ≠ 2+N) (h3 : N ≠ 2+K) :
    ⟪inclusion L K z, Qp a b (inclusion L N y)⟫_ℂ = 0 := by
  rw [Qp_matrix a b _ _ (inclusion_mem 2 N y) (inclusion_mem 1 K z)]
  have e1 : (∑' n, ⟪inclusion L K z n, Ext005QuadraticEnergyR108.numberBlock a n
      (inclusion L N y n)⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : n = K
    · subst hn
      rw [inclusion_apply_ne N n y h1, map_zero, inner_zero_right]
    · rw [inclusion_apply_ne K n z hn, inner_zero_left]
  have e2 : (∑' n, ⟪inclusion L K z n, Ext005PairSector.annihilation b n
      (inclusion L N y (2+n))⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : n = K
    · subst hn
      rw [inclusion_apply_ne N (2+n) y (by omega), map_zero, inner_zero_right]
    · rw [inclusion_apply_ne K n z hn, inner_zero_left]
  have e3 : (∑' n, ⟪inclusion L K z (2+n), Ext005PairSector.creation b n
      (inclusion L N y n)⟫_ℂ) = 0 := by
    rw [tsum_congr (fun n => ?_), tsum_zero]
    by_cases hn : 2+n = K
    · rw [inclusion_apply_ne N n y (by omega), map_zero, inner_zero_right]
    · rw [inclusion_apply_ne K (2+n) z hn, inner_zero_left]
  rw [e1, e2, e3]
  ring

/-! ### The finite CCR-core polynomial -/

/-- The literal one-particle entries <e_i, a e_j>. -/
def numberEntry (a : HN L 1 →L[ℂ] HN L 1) (i j : ℤ) : ℂ :=
  ⟪power 1 (physicalBasis L i), a (power 1 (physicalBasis L j))⟫_ℂ

/-- The finite-mode quadratic polynomial on the CCR core. -/
def QFS (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) : Module.End ℂ FS :=
  ∑ i ∈ S, ∑ j ∈ S, (α i j • (Cre i * Ann j) + (c i j / 2) • (Cre i * Cre j) +
    (conj (c i j) / 2) • (Ann j * Ann i))

lemma ip_sum_right {ι : Type*} (u : FS) (s : Finset ι) (f : ι → FS) :
    ip u (∑ x ∈ s, f x) = ∑ x ∈ s, ip u (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip_zero_right]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ip_add_right, ih]

lemma ip_QFS (α c : ℤ → ℤ → ℂ) (S : Finset ℤ) (k m : Occ) :
    ip (ket k) (QFS α c S (ket m)) = ∑ i ∈ S, ∑ j ∈ S,
      (α i j * ip (ket k) (Cre i (Ann j (ket m))) +
        c i j / 2 * ip (ket k) (Cre i (Cre j (ket m))) +
        conj (c i j) / 2 * ip (ket k) (Ann j (Ann i (ket m)))) := by
  simp only [QFS, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.mul_apply, ip_sum_right, ip_add_right, ip_smul_right]

lemma total_sub_e {m : Occ} {a : ℤ} (h : 1 ≤ m a) : total (m - e a) + 1 = total m := by
  rw [← total_add_e, shift_sub_add h]

lemma cre_ann_zero {k m : Occ} (i j : ℤ) (h : total k ≠ total m) :
    ip (ket k) (Cre i (Ann j (ket m))) = 0 := by
  rw [ip_cre_ann]
  by_cases hs : shift j i m = k
  · by_cases hd : DonorOK j m
    · exact absurd (hs ▸ total_shift hd) h
    · have hz : m j = 0 := by
        have : ¬ 1 ≤ m j := hd
        omega
      rw [w_empty hz]
      simp
  · rw [if_neg hs, mul_zero]

lemma cre_cre_zero {k m : Occ} (i j : ℤ) (h : total k ≠ total m + 2) :
    ip (ket k) (Cre i (Cre j (ket m))) = 0 := by
  rw [ip_cre_cre]
  have hs : m + e j + e i ≠ k := by
    intro hs
    apply h
    rw [← hs, total_add_e, total_add_e]
  rw [if_neg hs, mul_zero]

lemma ann_ann_ket (i j : ℤ) (m : Occ) :
    Ann j (Ann i (ket m)) =
      ((Real.sqrt (m i : ℝ) : ℂ) * (Real.sqrt ((m - e i) j : ℝ) : ℂ)) • ket (m - e i - e j) := by
  rw [Ann_ket, map_smul, Ann_ket, smul_smul, mul_comm]

lemma ann_ann_zero {k m : Occ} (i j : ℤ) (h : total m ≠ total k + 2) :
    ip (ket k) (Ann j (Ann i (ket m))) = 0 := by
  rw [ann_ann_ket, ip_ket_left, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases hs : m - e i - e j = k
  · rw [if_pos hs]
    by_cases hi : 1 ≤ m i
    · by_cases hj : 1 ≤ (m - e i) j
      · exfalso
        apply h
        rw [← hs, ← total_sub_e hi, ← total_sub_e hj]
      · have hz : (m - e i) j = 0 := by omega
        simp [hz]
    · have hz : m i = 0 := by omega
      simp [hz]
  · rw [if_neg hs, mul_zero]

lemma ip_conj_ket (k : Occ) (u : FS) : conj (ip u (ket k)) = ip (ket k) u := by
  rw [ip_ket_right, ip_ket_left, Complex.conj_conj]

lemma ann_ann_conj (k m : Occ) (i j : ℤ) :
    conj (ip (ket m) (Cre i (Cre j (ket k)))) = ip (ket k) (Ann j (Ann i (ket m))) := by
  rw [Cre_adjoint, Cre_adjoint, ip_conj_ket]

/-- **Quadratic ket bridge.** -/
theorem Qp_ket (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (k m : Occ) (S : Finset ℤ)
    (hk : k.support ⊆ S) (hm : m.support ⊆ S) :
    ⟪physCore (L := L) (ket k), Qp a b (physCore (ket m))⟫_ℂ =
      ip (ket k) (QFS (numberEntry a) (pairCoeff b) S (ket m)) := by
  rw [ip_QFS]
  by_cases hKN : total k = total m
  · rw [physCore_ket_sector (L := L) (⟨k, hKN⟩ : Arr (total m)),
      physCore_ket_sector (L := L) (⟨m, rfl⟩ : Arr (total m)), Qp_number,
      numberBlock_ket _ a _ _ S hk hm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [cre_cre_zero i j (by omega), ann_ann_zero i j (by omega)]
    simp [numberEntry]
  by_cases hC : total k = 2 + total m
  · rw [physCore_ket_sector (L := L) (⟨k, hC⟩ : Arr (2 + total m)),
      physCore_ket_sector (L := L) (⟨m, rfl⟩ : Arr (total m)), Qp_creation,
      creation_ket _ b _ _ S hk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [cre_ann_zero i j hKN, ann_ann_zero i j (by omega)]
    ring
  by_cases hA : total m = 2 + total k
  · rw [physCore_ket_sector (L := L) (⟨k, rfl⟩ : Arr (total k)),
      physCore_ket_sector (L := L) (⟨m, hA⟩ : Arr (2 + total k)), Qp_annihilation,
      ← ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm]
    have hcr : ⟪sectorKet (L := L) (⟨m, hA⟩ : Arr (2 + total k)),
        (Ext005PairSector.annihilation b (total k)).adjoint
          (sectorKet (L := L) (⟨k, rfl⟩ : Arr (total k)))⟫_ℂ =
        ∑ i ∈ S, ∑ j ∈ S, pairCoeff b i j * ip (ket m) (Cre i (Cre j (ket k))) :=
      creation_ket (total k) b (⟨m, hA⟩ : Arr (2 + total k)) (⟨k, rfl⟩ : Arr (total k)) S hm
    rw [hcr, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [cre_ann_zero (k := k) (m := m) i j hKN, cre_cre_zero (k := k) (m := m) i j (by omega),
      map_mul, ann_ann_conj]
    ring
  · rw [physCore_ket_sector (L := L) (⟨k, rfl⟩ : Arr (total k)),
      physCore_ket_sector (L := L) (⟨m, rfl⟩ : Arr (total m)),
      Qp_other a b _ _ _ _ hKN hC (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [cre_ann_zero i j hKN, cre_cre_zero i j (by omega), ann_ann_zero i j (by omega)]
    ring

end QuantumNLS.Prop022OQuadraticKet

#print axioms QuantumNLS.Prop022OQuadraticKet.Qp_ket
