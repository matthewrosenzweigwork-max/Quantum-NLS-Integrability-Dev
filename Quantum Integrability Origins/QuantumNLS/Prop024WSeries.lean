import QuantumNLS.Prop024AssemblyR58
import QuantumNLS.Prop024DomainEstimateR57
import QuantumNLS.Prop024WNorms

/-! PROP-024 operator-level Wick expansion, module 6 (Prop024WSeries): the Hilbert-norm convergent cell expansion.

The cell vectors `cellVec N m a b = N^{1-(a+b)/2} C(m,a) C(m,b) 𝒲_{a,b}(contractedKernel m a b) y` are grouped by total degree `j = a+b` (`cellDeg`, `cellSum_eq_deg`).  Under the factorial kernel bound, the printed polynomial moment bounds and `N ≥ 256 e A Q`: the degree-0,1,2 series converge absolutely in `m` (polynomial-geometric envelope, `summable_norm_cellDeg`), the degree-`j ≥ 3` cells are bounded by `N · contractedSliceCell` and summable by the frozen R54 series (`summable_norm_remCell`), and `hasSum_cellSum`: `∑_m ∑_{a,b ≤ m} cell = constScalar • y + linVec + quadVec + remVec` in Hilbert norm.  The constant term is a scalar multiple of `y` (`cellDeg_zero`, `wickFock_zero_scalar`). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
open Filter
namespace QuantumNLS.Prop024WSeries
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022TensorCompressionR115 Ext006NumberPhase
open Prop024WBlock Prop024WSector Prop024WWords Prop024WOrder Prop024WNorms
open Prop024ContractionsR54 Prop024PhysicalHamiltonianR54 Prop024WickCellsR54
open Prop022FactorialCoefficientsR115
variable {L : ℝ} [Fact (0 < L)]

/-- The degree-`j` slice of the `m`-th order cells. -/
def cellDeg (N m j : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) (x : Fock L) : Fock L :=
  ∑ a ∈ Finset.range (j+1), cellVec N m a (j - a) Bm u x

lemma cellVec_out (N m a b : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) (x : Fock L)
    (h : ¬ (a ≤ m ∧ b ≤ m)) : cellVec N m a b Bm u x = 0 := by
  unfold cellVec; rw [dif_neg h]

lemma sum_range_sq_eq_triangle {G : Type*} [AddCommMonoid G] (m : ℕ) (F : ℕ → ℕ → G)
    (hFz : ∀ a b, (a > m ∨ b > m) → F a b = 0) :
    ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1), F a b =
      ∑ j ∈ Finset.range (2*m+1), ∑ a ∈ Finset.range (j+1), F a (j - a) := by
  have h1 : ∀ j, ∑ a ∈ Finset.range (j+1), F a (j - a) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, F p.1 p.2 := by
    intro j
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [h1]
  rw [← Finset.sum_biUnion (s := Finset.range (2*m+1)) (t := Finset.HasAntidiagonal.antidiagonal)
    (f := fun p : ℕ × ℕ => F p.1 p.2)
    (fun i _ j _ hij => Finset.disjoint_left.2 (fun p hi hj => hij (by
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hi hj; omega)))]
  rw [← Finset.sum_product' (s := Finset.range (m+1)) (t := Finset.range (m+1)) (f := F)]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨p.1 + p.2, by omega, rfl⟩
  · intro p hp hnp
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.mem_product] at hp hnp
    obtain ⟨j, hj, hjp⟩ := hp
    exact hFz _ _ (by omega)

/-- The `m`-th order cell sum regrouped by total degree. -/
lemma cellSum_eq_deg (N m : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) (x : Fock L) :
    cellSum N m Bm u x = ∑ j ∈ Finset.range (2*m+1), cellDeg N m j Bm u x := by
  unfold cellSum cellDeg
  exact sum_range_sq_eq_triangle m (fun a b => cellVec N m a b Bm u x)
    (fun a b h => cellVec_out N m a b Bm u x (by omega))

lemma summable_poly_geom (A : ℝ) (hA : 0 < A) (p : ℕ) :
    Summable (fun m : ℕ => (m : ℝ) ^ p * (A ^ m / Real.sqrt ((2*m).factorial : ℝ))) := by
  have hs : Summable (fun m : ℕ => ((p.factorial : ℝ) * (Real.exp 1 * A) ^ m) / (m.factorial : ℝ)) := by
    have := Real.summable_pow_div_factorial (Real.exp 1 * A)
    exact (this.mul_left (p.factorial : ℝ)).congr (fun m => by ring)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
  have h1 : (m : ℝ) ^ p ≤ (p.factorial : ℝ) * (Real.exp 1) ^ m := by
    have h := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) p
    rw [div_le_iff₀ (by positivity)] at h
    have e : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [e] at h
    linarith
  have hfac := Prop024DomainEstimateR57.factorial_le_sqrt_two_mul m
  have hmpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h2 : A ^ m / Real.sqrt ((2*m).factorial : ℝ) ≤ A ^ m / (m.factorial : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hmpos hfac
  calc (m : ℝ) ^ p * (A ^ m / Real.sqrt ((2*m).factorial : ℝ))
      ≤ ((p.factorial : ℝ) * (Real.exp 1) ^ m) * (A ^ m / (m.factorial : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = ((p.factorial : ℝ) * (Real.exp 1 * A) ^ m) / (m.factorial : ℝ) := by
        rw [mul_pow]; ring


/-- The pointwise bound on the cells with the geometric/factorial kernel envelope. -/
lemma norm_cellVec_le_geom (N m a b : ℕ) (hab : a ≤ m ∧ b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (M A : ℝ) (hB : FactorialBound B M A) (hm : 1 ≤ m)
    (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L)
    (hxj : x.1 ∈ (polynomialRoot (L := L) (a+b)).domain) :
    ‖cellVec N m a b (B m) u x.1‖ ≤
      ((N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b)) * ‖polynomialRoot (a+b) ⟨x.1, hxj⟩‖ * M *
        ((m : ℝ) ^ (a + b) * (A ^ m / Real.sqrt ((2 * m).factorial : ℝ))) := by
  have h1 := norm_cellVec_le N m a b hab (B m) u x hxj
  have hck : ‖ck m a b hab.1 hab.2 (B m) u‖ ≤ M * A ^ m / Real.sqrt ((2 * m).factorial : ℝ) := by
    rw [← contractedKernel_eq_ck]
    exact contractedKernel_factorial_bound m a b hab.1 hab.2 B u hu M A hB hm
  have hca : (m.choose a : ℝ) ≤ (m : ℝ) ^ a := by exact_mod_cast Nat.choose_le_pow m a
  have hcb : (m.choose b : ℝ) ≤ (m : ℝ) ^ b := by exact_mod_cast Nat.choose_le_pow m b
  have hν := norm_nonneg (polynomialRoot (a+b) ⟨x.1, hxj⟩)
  have hNr : (0 : ℝ) ≤ (N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b) := by positivity
  refine h1.trans ?_
  unfold cellCoeff
  have hC : (m.choose a : ℝ) * (m.choose b : ℝ) ≤ (m : ℝ) ^ (a + b) := by
    rw [pow_add]; exact mul_le_mul hca hcb (Nat.cast_nonneg _) (by positivity)
  have hk0 := norm_nonneg (ck m a b hab.1 hab.2 (B m) u)
  calc (N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b) * (m.choose a : ℝ) * (m.choose b : ℝ) *
        ‖ck m a b hab.1 hab.2 (B m) u‖ * ‖polynomialRoot (a + b) ⟨x.1, hxj⟩‖
      = ((N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b)) * ‖polynomialRoot (a + b) ⟨x.1, hxj⟩‖ *
        (((m.choose a : ℝ) * (m.choose b : ℝ)) * ‖ck m a b hab.1 hab.2 (B m) u‖) := by ring
    _ ≤ ((N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b)) * ‖polynomialRoot (a + b) ⟨x.1, hxj⟩‖ *
        ((m : ℝ) ^ (a + b) * (M * A ^ m / Real.sqrt ((2 * m).factorial : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hC hck hk0 (by positivity)
    _ = ((N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b)) * ‖polynomialRoot (a + b) ⟨x.1, hxj⟩‖ * M *
        ((m : ℝ) ^ (a + b) * (A ^ m / Real.sqrt ((2 * m).factorial : ℝ))) := by ring


lemma norm_cellVec_le_geom' (N m a b j : ℕ) (hj : a + b = j) (hab : a ≤ m ∧ b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (M A : ℝ) (hB : FactorialBound B M A) (hm : 1 ≤ m)
    (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L)
    (hxj : x.1 ∈ (polynomialRoot (L := L) j).domain) :
    ‖cellVec N m a b (B m) u x.1‖ ≤
      ((N : ℝ) / Real.sqrt (N : ℝ) ^ j) * ‖polynomialRoot j ⟨x.1, hxj⟩‖ * M *
        ((m : ℝ) ^ j * (A ^ m / Real.sqrt ((2 * m).factorial : ℝ))) := by
  subst hj
  exact norm_cellVec_le_geom N m a b hab B M A hB hm u hu x hxj

/-- The slice norm is bounded by the polynomial-geometric envelope. -/
lemma norm_cellDeg_le_geom (N m j : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 < A)
    (hB : FactorialBound B M A) (hm : 1 ≤ m) (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L) :
    ‖cellDeg N m j (B m) u x.1‖ ≤
      ((j : ℝ) + 1) * (((N : ℝ) / Real.sqrt (N : ℝ) ^ j) *
        ‖polynomialRoot j ⟨x.1, mem_polyRoot_of_momentFinite j (momentFinite_of_mem x)⟩‖ * M) *
        ((m : ℝ) ^ j * (A ^ m / Real.sqrt ((2 * m).factorial : ℝ))) := by
  have hxj := mem_polyRoot_of_momentFinite (L := L) j (momentFinite_of_mem x)
  set R : ℝ := ((N : ℝ) / Real.sqrt (N : ℝ) ^ j) * ‖polynomialRoot j ⟨x.1, hxj⟩‖ * M *
        ((m : ℝ) ^ j * (A ^ m / Real.sqrt ((2 * m).factorial : ℝ))) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  unfold cellDeg
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a ∈ Finset.range (j + 1), ‖cellVec N m a (j - a) (B m) u x.1‖
      ≤ ∑ a ∈ Finset.range (j + 1), R := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        by_cases hab : a ≤ m ∧ j - a ≤ m
        · exact norm_cellVec_le_geom' N m a (j - a) j (Nat.add_sub_of_le haj) hab B M A hB hm u hu x hxj
        · rw [cellVec_out N m a (j - a) (B m) u x.1 hab, norm_zero]; exact hR0
    _ = ((j : ℝ) + 1) * R := by simp [Finset.sum_const]
    _ = _ := by rw [hR]; ring

lemma summable_norm_cellDeg (N j : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 < A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L) :
    Summable (fun m : ℕ => ‖cellDeg N (m + 1) j (B (m + 1)) u x.1‖) := by
  have hs := (summable_nat_add_iff 1).mpr (summable_poly_geom A hA j)
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    (hs.mul_left (((j : ℝ) + 1) * (((N : ℝ) / Real.sqrt (N : ℝ) ^ j) *
        ‖polynomialRoot j ⟨x.1, mem_polyRoot_of_momentFinite j (momentFinite_of_mem x)⟩‖ * M)))
  exact norm_cellDeg_le_geom N (m + 1) j B M A hM hA hB (by omega) u hu x


/-! ### The constant term -/

lemma wickBlock_zero_scalar (k : ℕ) (C : HN L 0 →L[ℂ] HN L 0) (z : HN L (0 + k)) :
    wickBlock 0 0 k C z = (PhysicalPlacements.zeroKernelScalar L C) • z := by
  rw [wickBlock_balanced, wickCoeff_balanced, KernelDefinition.U_N_r_eq_Q_N_p,
    PhysicalPlacements.Q_N_0_eq_scalar_id_on_split]
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have : (((0 + k).factorial : ℝ) / (k.factorial : ℝ)) = 1 := by
    rw [Nat.zero_add]; exact div_self hk.ne'
  rw [this]
  simp

lemma wickFock_zero_scalar (C : HN L 0 →L[ℂ] HN L 0) {y : Fock L} (hy : MomentFinite y) :
    wickFock 0 0 C y = (PhysicalPlacements.zeroKernelScalar L C) • y := by
  apply fock_ext_sectors 0
  · intro j hj; omega
  · intro k
    rw [wickFock_sector 0 0 C hy k, wickBlock_zero_scalar]
    rfl

lemma cellDeg_zero (N m : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) {x : Fock L} (hx : MomentFinite x) :
    cellDeg N m 0 Bm u x =
      ((N : ℂ) * PhysicalPlacements.zeroKernelScalar L (ck m 0 0 (Nat.zero_le _) (Nat.zero_le _) Bm u)) • x := by
  unfold cellDeg
  simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
  unfold cellVec
  rw [dif_pos ⟨Nat.zero_le _, Nat.zero_le _⟩, wickFock_zero_scalar _ hx, smul_smul]
  congr 1
  unfold cellCoeff
  simp

/-! ### The remainder -/

/-- The cells of total degree `j ≥ 3`, indexed by `(m, j) ∈ ℕ × ℕ` (zero outside `3 ≤ j ≤ 2m`). -/
def remCell (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (x : Fock L) (q : ℕ × ℕ) : Fock L :=
  if 3 ≤ q.2 ∧ q.2 ≤ 2 * q.1 then cellDeg N q.1 q.2 (B q.1) u x else 0

lemma summable_contractedSlice_ext (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (hu : ‖u‖ = 1)
    (M A Q N : ℝ) (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q) (hN : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) :
    Summable (fun q : ℕ × ℕ => if 3 ≤ q.2 ∧ q.2 ≤ 2 * q.1 then contractedSliceCell q.1 q.2 B u Q N else 0) := by
  have hsource := Prop024WickSeriesR54.wickSourceCells_summable A Q N hA hQ hN
  have hactual : Summable (fun p : Prop024DoubleSeriesR53.WickSourceIndex =>
      contractedSliceCell p.val.1 p.val.2 B u Q N) :=
    Summable.of_nonneg_of_le
      (fun p => Prop024WickSeriesR54.contractedSliceCell_nonneg_local p.val.1 p.val.2 B u Q N)
      (fun p => contractedSliceCell_le_wickCell p.val.1 p.val.2 p.property.1 p.property.2
        B u hu M A Q N hM hA hB) (hsource.mul_left M)
  have := (summable_subtype_iff_indicator (s := {q : ℕ × ℕ | 3 ≤ q.2 ∧ q.2 ≤ 2 * q.1})
    (f := fun q : ℕ × ℕ => contractedSliceCell q.1 q.2 B u Q N)).1 hactual
  refine this.congr (fun q => ?_)
  simp only [Set.indicator_apply, Set.mem_setOf_eq]


lemma norm_cellDeg_le_slice (N m j : ℕ) (hN : 0 < N) (hj : 3 ≤ j) (B : ∀ r, HN L r →L[ℂ] HN L r)
    (u : L2T L) (x : physSmooth L) (Q : ℝ) (hQ : 1 ≤ Q) (hMom : PolyMoments Q x.1) :
    ‖cellDeg N m j (B m) u x.1‖ ≤ (N : ℝ) * contractedSliceCell m j B u Q N := by
  unfold cellDeg contractedSliceCell
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun a ha => ?_)
  have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  by_cases ha' : a ≤ m
  · by_cases hb' : j - a ≤ m
    · rw [dif_pos ha', dif_pos hb']
      exact norm_cellVec_le_contractedCell N m a (j - a) hN ⟨ha', hb'⟩ B u x Q hQ hMom (by omega)
    · rw [dif_pos ha', dif_neg hb', cellVec_out N m a (j - a) (B m) u x.1 (by omega), norm_zero, mul_zero]
  · rw [dif_neg ha', cellVec_out N m a (j - a) (B m) u x.1 (by omega), norm_zero, mul_zero]

lemma summable_norm_remCell (N : ℕ) (hN : 0 < N) (B : ∀ r, HN L r →L[ℂ] HN L r) (M A Q : ℝ)
    (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L)
    (hMom : PolyMoments Q x.1) :
    Summable (fun q : ℕ × ℕ => ‖remCell N B u x.1 q‖) := by
  have hs := (summable_contractedSlice_ext B u hu M A Q N hM hA hQ hNQ hB).mul_left (N : ℝ)
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) hs
  unfold remCell
  split_ifs with h
  · exact norm_cellDeg_le_slice N q.1 q.2 hN h.1 B u x Q hQ hMom
  · simp

lemma hasSum_remCell (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (x : Fock L)
    (hs : Summable (fun q : ℕ × ℕ => ‖remCell N B u x q‖)) :
    HasSum (fun m : ℕ => ∑ j ∈ Finset.Ico 3 (2 * (m + 1) + 1), cellDeg N (m + 1) j (B (m + 1)) u x)
      (∑' q : ℕ × ℕ, remCell N B u x q) := by
  have h1 : HasSum (remCell N B u x) (∑' q : ℕ × ℕ, remCell N B u x q) := hs.of_norm.hasSum
  have h2 : HasSum (fun m : ℕ => ∑ j ∈ Finset.Ico 3 (2 * m + 1), cellDeg N m j (B m) u x)
      (∑' q : ℕ × ℕ, remCell N B u x q) := by
    refine h1.prod_fiberwise (fun m => ?_)
    have this : HasSum (fun j : ℕ => remCell N B u x (m, j))
        (∑ j ∈ Finset.Ico 3 (2 * m + 1), remCell N B u x (m, j)) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => by
        unfold remCell
        rw [if_neg]
        simp only [Finset.mem_Ico] at hj
        omega)
    convert this using 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [Finset.mem_Ico] at hj
    unfold remCell
    rw [if_pos ⟨hj.1, by omega⟩]
  have h3 := (hasSum_nat_add_iff' 1).mpr h2
  simpa using h3


/-! ### The four terms and the total series -/

/-- The source constant `N F(u) = N ∑_m ⟨u^m, B_m u^m⟩`, as the series of the degree-`(0,0)` cells. -/
def constScalar (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) : ℂ :=
  ∑' m : ℕ, (N : ℂ) * PhysicalPlacements.zeroKernelScalar L
    (ck (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) (B (m+1)) u)

/-- The source linear term: the degree-one cells of all orders. -/
def linVec (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (x : Fock L) : Fock L :=
  ∑' m : ℕ, cellDeg N (m+1) 1 (B (m+1)) u x

/-- The source quadratic term: the degree-two cells of all orders. -/
def quadVec (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (x : Fock L) : Fock L :=
  ∑' m : ℕ, cellDeg N (m+1) 2 (B (m+1)) u x

/-- The entire Wick remainder: all cells of total degree `j ≥ 3`, `3 ≤ j ≤ 2m`, of all orders. -/
def remVec (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (x : Fock L) : Fock L :=
  ∑' q : ℕ × ℕ, remCell N B u x q

lemma norm_zeroKernelScalar_le (C : HN L 0 →L[ℂ] HN L 0) : ‖PhysicalPlacements.zeroKernelScalar L C‖ ≤ ‖C‖ := by
  unfold PhysicalPlacements.zeroKernelScalar
  rw [LinearIsometryEquiv.norm_map]
  calc ‖C ((PhysicalPlacements.physZeroSectorIso L).symm 1)‖ ≤ ‖C‖ * ‖(PhysicalPlacements.physZeroSectorIso L).symm 1‖ :=
        C.le_opNorm _
    _ = ‖C‖ := by rw [LinearIsometryEquiv.norm_map, norm_one, mul_one]

lemma summable_constScalar (N : ℕ) (B : ∀ r, HN L r →L[ℂ] HN L r) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 < A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) :
    Summable (fun m : ℕ => (N : ℂ) * PhysicalPlacements.zeroKernelScalar L
      (ck (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) (B (m+1)) u)) := by
  have hs := (summable_nat_add_iff 1).mpr (summable_poly_geom A hA 0)
  refine Summable.of_norm_bounded (hs.mul_left ((N : ℝ) * M)) (fun m => ?_)
  rw [norm_mul, Complex.norm_natCast]
  have h1 := norm_zeroKernelScalar_le (ck (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) (B (m+1)) u)
  have h2 : ‖ck (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) (B (m+1)) u‖ ≤
      M * A ^ (m+1) / Real.sqrt ((2 * (m+1)).factorial : ℝ) := by
    rw [← contractedKernel_eq_ck]
    exact contractedKernel_factorial_bound (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) B u hu M A hB (by omega)
  calc (N : ℝ) * ‖PhysicalPlacements.zeroKernelScalar L (ck (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) (B (m+1)) u)‖
      ≤ (N : ℝ) * (M * A ^ (m+1) / Real.sqrt ((2 * (m+1)).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Nat.cast_nonneg N)
    _ = (N : ℝ) * M * (((m + 1 : ℕ) : ℝ) ^ 0 * (A ^ (m+1) / Real.sqrt ((2 * (m+1)).factorial : ℝ))) := by
        rw [pow_zero, one_mul]; ring


/-- **The Hilbert-norm convergent cell expansion.**  Under the printed number-moment bounds, the
`m`-th order cell sums `∑_{a,b ≤ m}` converge absolutely, and their sum is the constant term plus the
linear, quadratic and entire remainder terms. -/
theorem hasSum_cellSum (N : ℕ) (hN : 0 < N) (B : ∀ r, HN L r →L[ℂ] HN L r) (M A Q : ℝ)
    (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q) (hNQ : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) (x : physSmooth L)
    (hMom : PolyMoments Q x.1) :
    HasSum (fun m : ℕ => cellSum N (m + 1) (B (m + 1)) u x.1)
      (constScalar N B u • x.1 + linVec N B u x.1 + quadVec N B u x.1 + remVec N B u x.1) := by
  have hx := momentFinite_of_mem x
  have h0 : HasSum (fun m : ℕ => cellDeg N (m + 1) 0 (B (m + 1)) u x.1) (constScalar N B u • x.1) := by
    have := (summable_constScalar N B M A hM hA hB u hu).hasSum.smul_const x.1
    have hfun : (fun m : ℕ => cellDeg N (m + 1) 0 (B (m + 1)) u x.1) = fun m : ℕ =>
        ((N : ℂ) * PhysicalPlacements.zeroKernelScalar L
          (ck (m+1) 0 0 (Nat.zero_le _) (Nat.zero_le _) (B (m+1)) u)) • x.1 :=
      funext fun m => cellDeg_zero N (m + 1) (B (m + 1)) u hx
    rw [hfun]
    exact this
  have h1 : HasSum (fun m : ℕ => cellDeg N (m + 1) 1 (B (m + 1)) u x.1) (linVec N B u x.1) :=
    (summable_norm_cellDeg N 1 B M A hM hA hB u hu x).of_norm.hasSum
  have h2 : HasSum (fun m : ℕ => cellDeg N (m + 1) 2 (B (m + 1)) u x.1) (quadVec N B u x.1) :=
    (summable_norm_cellDeg N 2 B M A hM hA hB u hu x).of_norm.hasSum
  have h3 : HasSum (fun m : ℕ => ∑ j ∈ Finset.Ico 3 (2 * (m + 1) + 1), cellDeg N (m + 1) j (B (m + 1)) u x.1)
      (remVec N B u x.1) :=
    hasSum_remCell N B u x.1 (summable_norm_remCell N hN B M A Q hM hA hQ hNQ hB u hu x hMom)
  have h := ((h0.add h1).add h2).add h3
  have hfun : (fun m : ℕ => cellSum N (m + 1) (B (m + 1)) u x.1) = fun m : ℕ =>
      cellDeg N (m + 1) 0 (B (m + 1)) u x.1 + cellDeg N (m + 1) 1 (B (m + 1)) u x.1 +
        cellDeg N (m + 1) 2 (B (m + 1)) u x.1 +
        ∑ j ∈ Finset.Ico 3 (2 * (m + 1) + 1), cellDeg N (m + 1) j (B (m + 1)) u x.1 := by
    funext m
    rw [cellSum_eq_deg, ← Finset.sum_range_add_sum_Ico _ (show 3 ≤ 2 * (m + 1) + 1 by omega)]
    simp [Finset.sum_range_succ]
  rw [hfun]
  exact h

end QuantumNLS.Prop024WSeries

#print axioms QuantumNLS.Prop024WSeries.cellSum_eq_deg
#print axioms QuantumNLS.Prop024WSeries.summable_norm_cellDeg
#print axioms QuantumNLS.Prop024WSeries.summable_norm_remCell
#print axioms QuantumNLS.Prop024WSeries.hasSum_remCell
#print axioms QuantumNLS.Prop024WSeries.cellDeg_zero
#print axioms QuantumNLS.Prop024WSeries.hasSum_cellSum

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WSeries." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WSeries." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop024WSeries aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
