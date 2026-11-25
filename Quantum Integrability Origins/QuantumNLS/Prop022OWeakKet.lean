import QuantumNLS.Prop022OCommutator
import QuantumNLS.Prop022BlockEquationR124
import QuantumNLS.Prop022OWeylField

/-! PROP-022 takeover, stage O4c. Field matrix elements between occupation
kets, the bilinear core bridge of the physical quadratic Hamiltonian, and
the weak ket commutator identity for finitely supported smearings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop022OWeakKet
open Occupation Prop022OQuadraticKet Prop022OCommutator
open Ext006BogoliubovAlg Ext006SmoothOperatorsR34a Ext006StrongFieldR41a
open Ext006IdentityCyclicR35a Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006QuasifreeWeak

/-! ### Field matrix elements between kets -/

lemma field_coeff (h : H) (w : D) (k : Occ) :
    (field h w).1 k = (∑' a, conj (h a) * ((Real.sqrt ((k a : ℝ)+1) : ℂ) * w.1 (k + e a))) +
      ∑ a ∈ k.support, h a * ((Real.sqrt (k a : ℝ) : ℂ) * w.1 (k - e a)) := by
  change smearedAnnCoeff h w.1 k + smearedCreCoeff h w.1 k = _
  rw [smearedAnnCoeff, lp.inner_eq_tsum]
  refine congrArg₂ (· + ·) (tsum_congr (fun a => ?_)) rfl
  rw [RCLike.inner_apply, mul_comm]
  rfl

lemma ket_val (n m : Occ) : (ketD n).1 m = if m = n then 1 else 0 := by
  change (lp.single 2 n (1 : ℂ) : Ext006VacuumRecurrence.Fock) m = _
  rw [lp.single_apply, Pi.single_apply]

lemma ip_cre_ket (k n : Occ) (a : ℤ) :
    ip (ket k) (Cre a (ket n)) =
      (Real.sqrt ((n a : ℝ)+1) : ℂ) * (if n + e a = k then 1 else 0) := by
  rw [Cre_ket, ip_ket_left, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]

lemma ip_ann_ket (k n : Occ) (a : ℤ) :
    ip (ket k) (Ann a (ket n)) =
      (Real.sqrt (n a : ℝ) : ℂ) * (if n - e a = k then 1 else 0) := by
  rw [Ann_ket, ip_ket_left, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]

lemma add_e_apply (k : Occ) (a : ℤ) : (k + e a) a = k a + 1 := by
  simp [e]

lemma ann_term (k n : Occ) (a : ℤ) :
    (Real.sqrt ((k a : ℝ)+1) : ℂ) * (if k + e a = n then 1 else 0) =
      (Real.sqrt (n a : ℝ) : ℂ) * (if n - e a = k then 1 else 0) := by
  by_cases h : k + e a = n
  · have h2 : n - e a = k := by rw [← h]; exact add_tsub_cancel_right k (e a)
    rw [if_pos h, if_pos h2, ← h, add_e_apply]
    push_cast
    ring
  · rw [if_neg h, mul_zero]
    by_cases h2 : n - e a = k
    · have hz : n a = 0 := by
        by_contra hne
        apply h
        rw [← h2]
        exact shift_sub_add (show 1 ≤ n a by omega)
      simp [hz]
    · rw [if_neg h2, mul_zero]

lemma cre_term (k n : Occ) (a : ℤ) :
    (Real.sqrt (k a : ℝ) : ℂ) * (if k - e a = n then 1 else 0) =
      (Real.sqrt ((n a : ℝ)+1) : ℂ) * (if n + e a = k then 1 else 0) := by
  have := ann_term n k a
  rw [this]

lemma field_ket (h : H) (k n : Occ) (S : Finset ℤ) (hk : k.support ⊆ S) (hn : n.support ⊆ S) :
    ⟪(ketD k).1, (field h (ketD n)).1⟫_ℂ = ip (ket k) (phiFS S (fun l => h l) (ket n)) := by
  have hl : ⟪(ketD k).1, (field h (ketD n)).1⟫_ℂ = (field h (ketD n)).1 k := by
    change ⟪(lp.single 2 k (1 : ℂ) : Ext006VacuumRecurrence.Fock), (field h (ketD n)).1⟫_ℂ = _
    rw [lp.inner_single_left]
    simp
  rw [hl, field_coeff]
  simp only [ket_val]
  have hA : (∑' a, conj (h a) * ((Real.sqrt ((k a : ℝ)+1) : ℂ) *
      (if k + e a = n then (1 : ℂ) else 0))) =
      ∑ a ∈ S, conj (h a) * ((Real.sqrt (n a : ℝ) : ℂ) * (if n - e a = k then 1 else 0)) := by
    rw [tsum_eq_sum (s := S)]
    · exact Finset.sum_congr rfl (fun a _ => by rw [ann_term])
    · intro a ha
      have hna : n a = 0 := Finsupp.notMem_support_iff.mp (fun h' => ha (hn h'))
      have hne : k + e a ≠ n := by
        intro he
        have := congrArg (fun f : Occ => f a) he
        simp only [add_e_apply] at this
        omega
      rw [if_neg hne, mul_zero, mul_zero]
  have hC : (∑ a ∈ k.support, h a * ((Real.sqrt (k a : ℝ) : ℂ) *
      (if k - e a = n then (1 : ℂ) else 0))) =
      ∑ a ∈ S, h a * ((Real.sqrt ((n a : ℝ)+1) : ℂ) * (if n + e a = k then 1 else 0)) := by
    rw [Finset.sum_subset hk]
    · exact Finset.sum_congr rfl (fun a _ => by rw [cre_term])
    · intro a _ ha
      have hka : k a = 0 := Finsupp.notMem_support_iff.mp ha
      simp [hka]
  rw [hA, hC, phiFS, LinearMap.sum_apply, ip_sum_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, ip_add_right,
    ip_smul_right, ip_smul_right, ip_cre_ket, ip_ann_ket]
  ring

/-! ### The core inner product -/

lemma ip_eq_inner (u v : FS) :
    ip u v = ⟪Ext006PhysicalVacuum.coreEmbedding u, Ext006PhysicalVacuum.coreEmbedding v⟫_ℂ := by
  induction u using Finsupp.induction_linear with
  | zero => rw [ip_zero_left, map_zero, inner_zero_left]
  | add u w hu hw => rw [ip_add_left, hu, hw, map_add, inner_add_left]
  | single m c =>
    rw [show (Finsupp.single m c : FS) = c • ket m by simp, ip_smul_left, map_smul,
      inner_smul_left, ip_ket_left, Ext006PhysicalVacuum.coreEmbedding_ket, lp.inner_single_left,
      Prop022OPairBridge.coreEmbedding_apply]
    simp

lemma ip_conj (u v : FS) : conj (ip u v) = ip v u := by
  rw [ip_eq_inner, ip_eq_inner, inner_conj_symm]

lemma Ann_adjoint (a : ℤ) (u v : FS) : ip u (Ann a v) = ip (Cre a u) v := by
  rw [← ip_conj, ← Cre_adjoint, ip_conj]

lemma phiFS_adjoint (S : Finset ℤ) (h : ℤ → ℂ) (u v : FS) :
    ip (phiFS S h u) v = ip u (phiFS S h v) := by
  simp only [phiFS, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [ip_sum_right]
  induction S using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ip_add_left, ih, ip_add_left, ip_smul_left,
      ip_smul_left, ip_add_right, ip_smul_right, ip_smul_right, Cre_adjoint, Ann_adjoint,
      Complex.conj_conj]
    ring

lemma phiFS_extend (S T : Finset ℤ) (hST : S ⊆ T) (g : ℤ → ℂ) (hg : ∀ a ∈ T, a ∉ S → g a = 0) :
    phiFS T g = phiFS S g := by
  unfold phiFS
  symm
  apply Finset.sum_subset hST
  intro a ha hna
  rw [hg a ha hna, map_zero, zero_smul, zero_smul, add_zero]

/-- Field action on a ket for a finitely supported smearing, as a core vector. -/
lemma field_core (g : H) (S : Finset ℤ) (hg : ∀ a ∉ S, g a = 0) (n : Occ) (hn : n.support ⊆ S) :
    (field g (ketD n)).1 = Ext006PhysicalVacuum.coreEmbedding (phiFS S (fun l => g l) (ket n)) := by
  apply Ext006ClosedFieldGraphsR36a.ket_total
  intro m
  have hT : S ⊆ S ∪ m.support := Finset.subset_union_left
  rw [field_ket g m n (S ∪ m.support) Finset.subset_union_right (hn.trans hT),
    phiFS_extend S (S ∪ m.support) hT _ (fun a _ ha => hg a ha)]
  change _ = ⟪(lp.single 2 m (1 : ℂ) : Ext006VacuumRecurrence.Fock), _⟫_ℂ
  rw [lp.inner_single_left, Prop022OPairBridge.coreEmbedding_apply, ip_ket_left]
  simp

end QuantumNLS.Prop022OWeakKet
