import QuantumNLS.Prop022OWeakKet

/-! PROP-022 takeover, stage O4d. The weak ket commutator identity for the
actual physical quadratic Hamiltonian and the actual occupation field:
  <Q k, phi(g) n> - <phi(g) k, Q n> = i <k, phi(Lambda g) n>
for every square-summable smearing g, where Lambda is the coordinate form of
the real-linear generator v |-> -i (a v - b conj v) of the printed
linearized equation, with the original basis conjugation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022OWeakIdentity
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Occupation Prop022OQuadraticKet Prop022OCommutator Prop022OWeakKet Prop022OPairBridge
open Ext006BogoliubovAlg Ext006SmoothOperatorsR34a Ext006StrongFieldR41a Ext006FieldBoundsR42a
open Ext006IdentityCyclicR35a Ext006PhysFockCoord Ext006KernelHilbertSchmidt
open Ext005Moments Ext005MomentEnergyR108 Ext005FormCutoffR109 Ext005FormScaleR109 Ext005PhysicalNumberFormR114
open Prop022StrongOperatorR125 Prop022PrintedCoefficientsR124 Prop022PairHSR122
open Prop022TensorCompressionR115 Ext006PhysicalNormBridge.PairTensor
variable {L : ℝ} [Fact (0 < L)]

/-! ### Linearity and symmetry of the physical quadratic Hamiltonian -/

lemma Qp_add (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (x y : Fock L)
    (hx : x ∈ momentDomain (L := L) 2) (hy : y ∈ momentDomain (L := L) 2) :
    Qp a b (x + y) = Qp a b x + Qp a b y := by
  simp only [Qp]
  rw [rootLift_eq 2 _ (Submodule.add_mem _ hx hy), rootLift_eq 2 x hx, rootLift_eq 2 y hy,
    ← map_add]
  congr 1
  exact (momentRoot (L := L) 2).map_add ⟨x, hx⟩ ⟨y, hy⟩

lemma Qp_smul (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (c : ℂ) (x : Fock L)
    (hx : x ∈ momentDomain (L := L) 2) :
    Qp a b (c • x) = c • Qp a b x := by
  simp only [Qp]
  rw [rootLift_eq 2 _ (Submodule.smul_mem _ c hx), rootLift_eq 2 x hx, ← map_smul]
  congr 1
  exact (momentRoot (L := L) 2).map_smul c ⟨x, hx⟩

lemma Qp_form (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (x y : Fock L)
    (hx : x ∈ momentDomain (L := L) 2) (hy : y ∈ momentDomain (L := L) 1) :
    ⟪y, Qp a b x⟫_ℂ = quadraticContinuous a b (rootLift 1 x) (rootLift 1 y) := by
  have hq := quadraticAction_form a b ⟨x, hx⟩ (rootLift 1 y)
  rw [embedding_rootLift y hy] at hq
  have hQ : Qp a b x = quadraticAction a b ⟨x, hx⟩ := by
    rw [Qp, quadraticAction, rootLift_eq 2 x hx]
    rfl
  rw [hQ, hq]

/-- Symmetry of Q on its second-moment domain. -/
lemma Qp_symm (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a) (b : HN L 2) (x y : Fock L)
    (hx : x ∈ momentDomain (L := L) 2) (hy : y ∈ momentDomain (L := L) 2) :
    ⟪Qp a b x, y⟫_ℂ = ⟪x, Qp a b y⟫_ℂ := by
  rw [← inner_conj_symm, Qp_form a b x y hx (domain_mono (by omega) hy),
    Qp_form a b y x hy (domain_mono (by omega) hx),
    Ext005PhysicalSymmetryR114.quadraticContinuous_symmetric a ha]

/-- Q composed with the core embedding, as a linear map. -/
def QpL (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) : FS →ₗ[ℂ] Fock L where
  toFun v := Qp a b (physCore v)
  map_add' u v := by rw [map_add]; exact Qp_add a b _ _ (physCore_mem 2 u) (physCore_mem 2 v)
  map_smul' c v := by rw [map_smul]; exact Qp_smul a b c _ (physCore_mem 2 v)

/-! ### Supports inside a finite mode set -/

/-- Every occupation in the support of v is supported in S. -/
def Good (S : Finset ℤ) (v : FS) : Prop := ∀ m ∈ v.support, m.support ⊆ S

lemma good_add {S : Finset ℤ} {u v : FS} (hu : Good S u) (hv : Good S v) : Good S (u + v) := by
  intro m hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
  · exact hu m h
  · exact hv m h

lemma good_smul {S : Finset ℤ} (c : ℂ) {u : FS} (hu : Good S u) : Good S (c • u) :=
  fun m hm => hu m (Finsupp.support_smul hm)

lemma good_ket {S : Finset ℤ} {m : Occ} (hm : m.support ⊆ S) : Good S (ket m) := by
  intro m' h'
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h'
  rw [h']
  exact hm

lemma good_sum {ι : Type*} {S : Finset ℤ} (T : Finset ι) (f : ι → FS)
    (hf : ∀ x ∈ T, Good S (f x)) : Good S (∑ x ∈ T, f x) := by
  classical
  induction T using Finset.induction_on with
  | empty => intro m hm; simp at hm
  | insert x T hx ih =>
    rw [Finset.sum_insert hx]
    exact good_add (hf x (Finset.mem_insert_self x T))
      (ih (fun y hy => hf y (Finset.mem_insert_of_mem hy)))

lemma good_phiFS {S : Finset ℤ} (h : ℤ → ℂ) {n : Occ} (hn : n.support ⊆ S) :
    Good S (phiFS S h (ket n)) := by
  rw [phiFS_apply, phiV]
  apply good_sum
  intro l hl
  apply good_add
  · rw [Cre_ket, smul_smul]
    apply good_smul
    apply good_ket
    intro x hx
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with h' | h'
    · exact hn h'
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h'
      rw [h']
      exact hl
  · rw [Ann_ket, smul_smul]
    apply good_smul
    apply good_ket
    intro x hx
    apply hn
    rw [Finsupp.mem_support_iff] at hx ⊢
    intro h0
    apply hx
    rw [Finsupp.tsub_apply, h0, Nat.zero_sub]

/-! ### The bilinear core bridge -/

lemma support_single_add {k : Occ} {c : ℂ} {f : FS} (hk : k ∉ f.support) (hc : c ≠ 0) :
    k ∈ (Finsupp.single k c + f).support ∧ ∀ x ∈ f.support, x ∈ (Finsupp.single k c + f).support := by
  constructor
  · rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.notMem_support_iff.mp hk, add_zero]
    exact hc
  · intro x hx
    have hxk : x ≠ k := fun h => hk (h ▸ hx)
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hxk),
      zero_add]
    exact Finsupp.mem_support_iff.mp hx

lemma bridge_left (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (S : Finset ℤ) (m : Occ)
    (hm : m.support ⊆ S) (u : FS) (hu : Good S u) :
    ⟪physCore (L := L) u, QpL a b (ket m)⟫_ℂ = ip u (QFS (numberEntry a) (pairCoeff b) S (ket m)) := by
  induction u using Finsupp.induction with
  | zero => rw [map_zero, inner_zero_left, ip_zero_left]
  | single_add k c f hk hc ih =>
    obtain ⟨h1, h2⟩ := support_single_add hk hc
    rw [map_add, inner_add_left, ip_add_left, ih (fun x hx => hu x (h2 x hx)),
      show (Finsupp.single k c : FS) = c • ket k by simp, map_smul, inner_smul_left, ip_smul_left]
    congr 1
    change conj c * ⟪physCore (L := L) (ket k), Qp a b (physCore (ket m))⟫_ℂ = _
    rw [Qp_ket a b k m S (hu k h1) hm]

/-- Bilinear bridge between the physical Q and the finite core polynomial. -/
theorem bridge (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (S : Finset ℤ) (u v : FS)
    (hu : Good S u) (hv : Good S v) :
    ⟪physCore (L := L) u, QpL a b v⟫_ℂ = ip u (QFS (numberEntry a) (pairCoeff b) S v) := by
  induction v using Finsupp.induction with
  | zero => rw [map_zero, inner_zero_right, map_zero, ip_zero_right]
  | single_add k c f hk hc ih =>
    obtain ⟨h1, h2⟩ := support_single_add hk hc
    rw [map_add, inner_add_right, map_add, ip_add_right, ih (fun x hx => hv x (h2 x hx)),
      show (Finsupp.single k c : FS) = c • ket k by simp, map_smul, inner_smul_right, map_smul,
      ip_smul_right, bridge_left a b S k (hv k h1) u hu]

/-! ### The coordinate generator of the printed linearized equation -/

/-- The literal number coefficient as an operator on the one-particle space. -/
def aOp (a : HN L 1 →L[ℂ] HN L 1) : L2T L →L[ℂ] L2T L :=
  oneEmbedding.adjoint ∘L a ∘L oneEmbedding

/-- The complex-linear representative of the pair kernel, original conjugation. -/
def bOp (b : HN L 2) : L2T L →L[ℂ] L2T L :=
  tensorOperator (physicalBasis L) (twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2))

/-- The real-linear generator v ↦ -i (a v - b conj v). -/
def gen (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (v : L2T L) : L2T L :=
  (-Complex.I) • (aOp a v - bOp b (conjugation (physicalBasis L) v))

/-- Its coordinate form. -/
def LamH (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (h : H) : H :=
  (physicalBasis L).repr (gen a b ((physicalBasis L).repr.symm h))

lemma gen_add (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (v w : L2T L) :
    gen a b (v + w) = gen a b v + gen a b w := by
  simp only [gen, map_add]
  module

lemma LamH_add (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (h h' : H) :
    LamH a b (h + h') = LamH a b h + LamH a b h' := by
  simp only [LamH, map_add, gen_add]

lemma gen_norm (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (v : L2T L) :
    ‖gen a b v‖ ≤ (‖aOp a‖ + ‖bOp b‖) * ‖v‖ := by
  rw [gen, norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc ‖aOp a v - bOp b (conjugation (physicalBasis L) v)‖
      ≤ ‖aOp a v‖ + ‖bOp b (conjugation (physicalBasis L) v)‖ := norm_sub_le _ _
    _ ≤ ‖aOp a‖ * ‖v‖ + ‖bOp b‖ * ‖conjugation (physicalBasis L) v‖ :=
      add_le_add (le_opNorm _ _) (le_opNorm _ _)
    _ = _ := by rw [conjugation_norm]; ring

lemma LamH_norm (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (h : H) :
    ‖LamH a b h‖ ≤ (‖aOp a‖ + ‖bOp b‖) * ‖h‖ := by
  rw [LamH, LinearIsometryEquiv.norm_map]
  have := gen_norm a b ((physicalBasis L).repr.symm h)
  rwa [LinearIsometryEquiv.norm_map] at this

lemma numberEntry_herm (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a) (i j : ℤ) :
    numberEntry a i j = conj (numberEntry a j i) := by
  rw [numberEntry, numberEntry, ← adjoint_inner_left, ha, inner_conj_symm]

lemma pairCoeff_symm (b : HN L 2) (i j : ℤ) : pairCoeff b i j = pairCoeff b j i := by
  have hfix : permHilbertIsometry (Equiv.swap (0 : Fin 2) 1)
      (b : HilbertTensorPower ℂ (L2T L) 2) = b := (mem_fixedSubmodule.mp b.property) _
  have hf : htcommIsometry ℂ (L2T L) (L2T L) (twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2)) =
      twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2) :=
    (twoIso_swap _).symm.trans (congrArg twoIso hfix)
  have he := (htcommIsometry ℂ (L2T L) (L2T L)).inner_map_map
    (htmul (physicalBasis L i) (physicalBasis L j))
    (twoIso (E := L2T L) (b : HilbertTensorPower ℂ (L2T L) 2))
  rw [htcommIsometry_htmul, hf] at he
  rw [pairCoeff, pairCoeff, ← he]

lemma repr_symm_finite (g : H) (G : Finset ℤ) (hg : ∀ x ∉ G, g x = 0) :
    (physicalBasis L).repr.symm g = ∑ j ∈ G, g j • physicalBasis L j := by
  apply (physicalBasis L).repr.injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_sum]
  simp only [map_smul, HilbertBasis.repr_self]
  apply lp.ext
  funext i
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact hg i h

lemma LamH_finite (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (g : H) (G : Finset ℤ)
    (hg : ∀ x ∉ G, g x = 0) (l : ℤ) :
    LamH a b g l = Lam (numberEntry a) (pairCoeff b) G (fun x => g x) l := by
  rw [LamH, HilbertBasis.repr_apply_apply, repr_symm_finite g G hg]
  have hc : conjugation (physicalBasis L) (∑ j ∈ G, g j • physicalBasis L j) =
      ∑ j ∈ G, conj (g j) • physicalBasis L j := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [Prop022BlockEquationR124.conjugation_smul, Ext006KernelHilbertSchmidt.conjugation_basis])
  rw [gen, hc, map_sum, map_sum, inner_smul_right, inner_sub_right, inner_sum, inner_sum]
  simp only [map_smul, inner_smul_right]
  rw [Lam, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have h1 : ⟪physicalBasis L l, aOp a (physicalBasis L j)⟫_ℂ = numberEntry a l j := by
    rw [aOp, comp_apply, comp_apply, adjoint_inner_right, oneEmbedding_apply, oneEmbedding_apply]
    rfl
  have h2 : ⟪physicalBasis L l, bOp b (physicalBasis L j)⟫_ℂ = pairCoeff b l j := by
    rw [bOp, tensorOperator_matrix, pairCoeff_symm]
    rfl
  rw [h1, h2]
  ring

/-! ### The weak ket identity -/

/-- The physical quadratic Hamiltonian in occupation coordinates. -/
def Qo (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (w : Ext006VacuumRecurrence.Fock) :
    Ext006VacuumRecurrence.Fock :=
  Phi (Qp a b ((Phi (L := L)).symm w))

lemma ip_sub (u v w : FS) : ip u (v - w) = ip u v - ip u w := by
  rw [ip_eq_inner, ip_eq_inner, ip_eq_inner, map_sub, inner_sub_right]

lemma inner_Phi_left (X : Fock L) (Y : Ext006VacuumRecurrence.Fock) :
    ⟪Phi X, Y⟫_ℂ = ⟪X, (Phi (L := L)).symm Y⟫_ℂ := by
  rw [← (Phi (L := L)).inner_map_map X ((Phi (L := L)).symm Y),
    LinearIsometryEquiv.apply_symm_apply]

lemma inner_Phi_right (Y : Ext006VacuumRecurrence.Fock) (X : Fock L) :
    ⟪Y, Phi X⟫_ℂ = ⟪(Phi (L := L)).symm Y, X⟫_ℂ := by
  rw [← (Phi (L := L)).inner_map_map ((Phi (L := L)).symm Y) X,
    LinearIsometryEquiv.apply_symm_apply]

lemma Phi_symm_ket (k : Occ) : (Phi (L := L)).symm (ketD k).1 = physCore (ket k) :=
  (physCore_ket k).symm

lemma Phi_symm_core (v : FS) :
    (Phi (L := L)).symm (Ext006PhysicalVacuum.coreEmbedding v) = physCore v := rfl

/-- **Weak ket identity**, finitely supported smearings. -/
theorem wk_finite (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a) (b : HN L 2) (g : H)
    (G : Finset ℤ) (hg : ∀ x ∉ G, g x = 0) (k n : Occ) :
    ⟪Qo (L := L) a b (ketD k).1, (field g (ketD n)).1⟫_ℂ -
      ⟪(field g (ketD k)).1, Qo (L := L) a b (ketD n).1⟫_ℂ =
      Complex.I * ⟪(ketD k).1, (field (LamH (L := L) a b g) (ketD n)).1⟫_ℂ := by
  set S := G ∪ k.support ∪ n.support
  have hGS : G ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hkS : k.support ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hnS : n.support ⊆ S := Finset.subset_union_right
  have hgS : ∀ x ∉ S, g x = 0 := fun x hx => hg x (fun h => hx (hGS h))
  rw [field_core g S hgS n hnS, field_core g S hgS k hkS, Qo, Qo, inner_Phi_left,
    inner_Phi_right, Phi_symm_ket, Phi_symm_ket, Phi_symm_core, Phi_symm_core,
    Qp_symm a ha b _ _ (physCore_mem 2 _) (physCore_mem 2 _)]
  change ⟪physCore (L := L) (ket k), QpL a b (phiFS S (fun l => g l) (ket n))⟫_ℂ -
    ⟪physCore (L := L) (phiFS S (fun l => g l) (ket k)), QpL a b (ket n)⟫_ℂ = _
  rw [bridge a b S _ _ (good_ket hkS) (good_phiFS _ hnS),
    bridge a b S _ _ (good_phiFS _ hkS) (good_ket hnS), phiFS_adjoint, ← ip_sub,
    QFS_apply, phiFS_apply, QFS_apply, phiFS_apply,
    QV_comm _ _ S _ (numberEntry_herm a ha) (pairCoeff_symm b), ip_smul_right,
    field_ket _ k n S hkS hnS, phiFS_apply]
  congr 3
  funext l
  exact (LamH_finite a b g S hgS l).symm

lemma field_norm_ket (h : H) (n : Occ) :
    ‖(field h (ketD n)).1‖ ≤ 2 * ‖h‖ * Real.sqrt ((total n : ℝ) + 1) := by
  have hb := field_norm_sq_le h (ketD n) (Ext006AnalyticFieldR42a.ket_particleBound n)
  have hk : ‖(ketD n).1‖ = 1 := by
    change ‖(lp.single 2 n (1 : ℂ) : Ext006VacuumRecurrence.Fock)‖ = 1
    rw [lp.norm_single (by norm_num), norm_one]
  rw [hk] at hb
  have hs : (2 * ‖h‖ * Real.sqrt ((total n : ℝ) + 1))^2 = 4 * ‖h‖^2 * ((total n : ℝ) + 1) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
  rw [hs]
  nlinarith

lemma field_sub_smear (h h' : H) (w : D) :
    (field (h - h') w).1 = (field h w).1 - (field h' w).1 := by
  have he : h = (h - h') + h' := by abel
  have := congrArg (fun F : Module.End ℂ D => (F w).1) (field_add_smear (h - h') h')
  simp only [LinearMap.add_apply, Submodule.coe_add, ← he] at this
  rw [this]
  abel

/-- **Weak ket identity** for every square-summable smearing. -/
theorem wk (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a) (b : HN L 2) (g : H) (k n : Occ) :
    ⟪Qo (L := L) a b (ketD k).1, (field g (ketD n)).1⟫_ℂ -
      ⟪(field g (ketD k)).1, Qo (L := L) a b (ketD n).1⟫_ℂ =
      Complex.I * ⟪(ketD k).1, (field (LamH (L := L) a b g) (ketD n)).1⟫_ℂ := by
  let F : H → ℂ := fun h => ⟪Qo (L := L) a b (ketD k).1, (field h (ketD n)).1⟫_ℂ -
      ⟪(field h (ketD k)).1, Qo (L := L) a b (ketD n).1⟫_ℂ -
      Complex.I * ⟪(ketD k).1, (field (LamH (L := L) a b h) (ketD n)).1⟫_ℂ
  have hsub : ∀ h h', F h - F h' = F (h - h') := by
    intro h h'
    have hl : LamH (L := L) a b (h - h') = LamH a b h - LamH a b h' := by
      have := LamH_add (L := L) a b (h - h') h'
      rw [sub_add_cancel] at this
      rw [this]; abel
    simp only [F, field_sub_smear, hl, inner_sub_left, inner_sub_right]
    ring
  set C := ‖Qo (L := L) a b (ketD k).1‖ * (2 * Real.sqrt ((total n : ℝ) + 1)) +
    2 * Real.sqrt ((total k : ℝ) + 1) * ‖Qo (L := L) a b (ketD n).1‖ +
    2 * (‖aOp a‖ + ‖bOp b‖) * Real.sqrt ((total n : ℝ) + 1)
  have hbound : ∀ h, ‖F h‖ ≤ C * ‖h‖ := by
    intro h
    have e1 : ‖⟪Qo (L := L) a b (ketD k).1, (field h (ketD n)).1⟫_ℂ‖ ≤
        ‖Qo (L := L) a b (ketD k).1‖ * (2 * ‖h‖ * Real.sqrt ((total n : ℝ) + 1)) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (field_norm_ket h n) (norm_nonneg _))
    have e2 : ‖⟪(field h (ketD k)).1, Qo (L := L) a b (ketD n).1⟫_ℂ‖ ≤
        (2 * ‖h‖ * Real.sqrt ((total k : ℝ) + 1)) * ‖Qo (L := L) a b (ketD n).1‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (field_norm_ket h k) (norm_nonneg _))
    have hk1 : ‖(ketD k).1‖ = 1 := by
      change ‖(lp.single 2 k (1 : ℂ) : Ext006VacuumRecurrence.Fock)‖ = 1
      rw [lp.norm_single (by norm_num), norm_one]
    have e3 : ‖Complex.I * ⟪(ketD k).1, (field (LamH (L := L) a b h) (ketD n)).1⟫_ℂ‖ ≤
        2 * ((‖aOp a‖ + ‖bOp b‖) * ‖h‖) * Real.sqrt ((total n : ℝ) + 1) := by
      rw [norm_mul, Complex.norm_I, one_mul]
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hk1, one_mul]
      refine (field_norm_ket _ n).trans ?_
      gcongr
      exact LamH_norm a b h
    calc ‖F h‖ ≤ ‖⟪Qo (L := L) a b (ketD k).1, (field h (ketD n)).1⟫_ℂ‖ +
          ‖⟪(field h (ketD k)).1, Qo (L := L) a b (ketD n).1⟫_ℂ‖ +
          ‖Complex.I * ⟪(ketD k).1, (field (LamH (L := L) a b h) (ketD n)).1⟫_ℂ‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by
        have := add_le_add (add_le_add e1 e2) e3
        refine this.trans (le_of_eq ?_)
        simp only [C]
        ring
  have hzero : ∀ G : Finset ℤ, F (∑ i ∈ G, lp.single 2 i (g i)) = 0 := by
    intro G
    simp only [F]
    rw [sub_eq_zero]
    apply wk_finite a ha b _ G
    intro x hx
    rw [lp.coeFn_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [lp.single_apply, Pi.single_apply, if_neg]
    rintro rfl
    exact hx hi
  have hlim := (lp.hasSum_single (p := 2) (by norm_num) g)
  suffices hF : F g = 0 by
    simp only [F] at hF
    exact sub_eq_zero.mp hF
  apply norm_le_zero_iff.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  have hC : 0 ≤ C := by positivity
  obtain ⟨G, hG⟩ := (Metric.tendsto_atTop.mp hlim) (ε / (C + 1)) (by positivity)
  have hd := hG G le_rfl
  rw [dist_eq_norm] at hd
  have he : F g = F (g - ∑ i ∈ G, lp.single 2 i (g i)) := by
    rw [← hsub, hzero, sub_zero]
  rw [he, zero_add]
  calc ‖F (g - ∑ i ∈ G, lp.single 2 i (g i))‖
      ≤ C * ‖g - ∑ i ∈ G, lp.single 2 i (g i)‖ := hbound _
    _ ≤ C * (ε / (C + 1)) := by
        gcongr
        rw [norm_sub_rev]
        exact hd.le
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end QuantumNLS.Prop022OWeakIdentity

#print axioms QuantumNLS.Prop022OWeakIdentity.wk
