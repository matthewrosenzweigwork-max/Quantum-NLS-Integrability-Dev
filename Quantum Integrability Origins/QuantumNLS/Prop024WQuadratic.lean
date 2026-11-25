import QuantumNLS.Prop024WLinear
import QuantumNLS.Prop022OQuadraticKet
import QuantumNLS.Ext006FiniteExponentialR39a
import QuantumNLS.Ext006PhysicalNormBridge
import QuantumNLS.MixedCommutator
import QuantumNLS.PlacementConsistency

/-! PROP-024 step (1), identification of the quadratic term (Prop024WQuadratic).

The degree-two Wick cells `quadVec` of `Prop024WSeries` are identified with the PROP-021 quadratic piece
`quadraticAction (numberCoefficient B u) (pairCoefficient B u)` of `Prop021RemainderInputR131.lowOrders`
(source `fluctuations.tex:274-276`: the `j = 2` terms are `𝕢(t) = dΓ(a) + ½{a*(b) + a(b)}`, eq. `Q7B:eq:quadratic`).

* `wickBlock_one_one`: `𝒲_{1,1}(K)` on the sector `1+k` is the DEF-009 number block `numberBlock K (1+k)`;
* `wickBlock_two_zero_eq`, `wickBlock_zero_two_eq`: `𝒲_{2,0}(C) = a*(b_C)` (pair creation), `𝒲_{0,2}(C) = a(b_{C†})`
  with the pair vector `b_C = C e`, via the symbols `symbol_creation` on product vectors;
* `cellDeg_two_eq`: the degree-two cell of order `m = r+1` is `quadraticAction (mixedTerm r) (pairShift r)`;
  the identification pairs against all single-sector vectors through the frozen sector matrix elements `Qp_matrix`;
* `quadVec_eq_quadraticAction`: `quadVec N B u x = quadraticAction (numberCoefficient B u) (pairCoefficient B u) ⟨x,h₂⟩`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
namespace QuantumNLS.Prop024WQuadratic
open TensorCarrier TensorPlacements PhysicalTensor BetheCoefficientTransform KernelDefinition
  Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022TensorCompressionR115 Prop022ACoherent
open Prop024WBlock Prop024WSector Prop024WWords Prop024WOrder Prop024WSeries Prop024WLinear
open Prop024ContractionsR54 Prop022FactorialCoefficientsR115
open Ext005Moments Prop022OQuadraticKet Prop022StrongOperatorR125
variable {L : ℝ} [Fact (0 < L)]

/-! ### Symbols of the pair creation and annihilation -/

lemma symbol_creation (b : HN L 2) (n : ℕ) (g h : L2T L) :
    ⟪power (2+n) g, Ext005PairSector.creation b n (power n h)⟫_ℂ =
      (Real.sqrt (((n : ℝ)+1)*((n : ℝ)+2)) : ℂ) * (⟪power 2 g, b⟫_ℂ * ⟪g, h⟫_ℂ ^ n) := by
  rw [Ext006PhysicalNormBridge.CreationFormula.creation_eq_projection, inner_smul_right,
    inner_proj_of_mem]
  congr 1
  change ⟪(htpow (2+n) g : TP L (2+n)),
    (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n).symm
      (htmul (b : TP L 2) (htpow n h : TP L n))⟫_ℂ = _
  rw [← (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n).inner_map_map, LinearIsometryEquiv.apply_symm_apply,
    KernelDefinition.split_htpow, inner_htmul, IntrinsicContact.inner_htpow]
  rfl

lemma factorial_two_add (k : ℕ) :
    (((2+k).factorial : ℕ) : ℝ) = ((k : ℝ)+1)*((k : ℝ)+2) * (k.factorial : ℝ) := by
  rw [Nat.add_comm 2 k, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

lemma wickCoeff_two_zero (k : ℕ) : wickCoeff 2 0 k = Real.sqrt (((k : ℝ)+1)*((k : ℝ)+2)) := by
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [wickCoeff_eq_prod, Nat.zero_add, div_self hk.ne', Real.sqrt_one, mul_one, factorial_two_add,
    mul_div_assoc, div_self hk.ne', mul_one]

lemma wickCoeff_zero_two (k : ℕ) : wickCoeff 0 2 k = Real.sqrt (((k : ℝ)+1)*((k : ℝ)+2)) := by
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [wickCoeff_eq_prod, Nat.zero_add, div_self hk.ne', Real.sqrt_one, one_mul, factorial_two_add,
    mul_div_assoc, div_self hk.ne', mul_one]

/-- `𝒲_{2,0}(C)` on the sector `0+k` is the physical pair creation of the vector `C e`. -/
lemma wickBlock_two_zero_eq (k : ℕ) (C : HN L 0 →L[ℂ] HN L 2) (e : L2T L) :
    wickBlock 2 0 k C =
      (Ext005PairSector.creation (C (power 0 e)) k).comp
        (castHN (Nat.zero_add k)).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply clm_ext_powers
  intro g h
  have hc : (castHN (Nat.zero_add k)).toContinuousLinearEquiv.toContinuousLinearMap
      (power (0+k) h : HN L (0+k)) = power k h := castHN_power _ h
  rw [symbol_wickBlock, ContinuousLinearMap.comp_apply, hc, symbol_creation, wickCoeff_two_zero,
    power_zero_eq h e]

lemma inner_creation_eq_inner_annihilation (b : HN L 2) (n : ℕ) (z : HN L n) (w : HN L (2+n)) :
    ⟪Ext005PairSector.creation b n z, w⟫_ℂ = ⟪z, Ext005PairSector.annihilation b n w⟫_ℂ := by
  rw [Ext005PairSector.creation, ContinuousLinearMap.adjoint_inner_left]

lemma ann_cast_symbol (V : HN L 2) (k : ℕ) (g h : L2T L) :
    ⟪(power (0+k) g : HN L (0+k)),
      (castHN (Nat.zero_add k).symm).toContinuousLinearEquiv.toContinuousLinearMap
        (Ext005PairSector.annihilation V k (power (2+k) h))⟫_ℂ =
      (Real.sqrt (((k : ℝ)+1)*((k : ℝ)+2)) : ℂ) * (⟪V, power 2 h⟫_ℂ * ⟪g, h⟫_ℂ ^ k) := by
  have h1 : ⟪(power (0+k) g : HN L (0+k)),
      (castHN (Nat.zero_add k).symm).toContinuousLinearEquiv.toContinuousLinearMap
        (Ext005PairSector.annihilation V k (power (2+k) h))⟫_ℂ =
      ⟪power k g, Ext005PairSector.annihilation V k (power (2+k) h)⟫_ℂ := by
    change ⟪(power (0+k) g : HN L (0+k)), castHN (Nat.zero_add k).symm _⟫_ℂ = _
    rw [castHN_symm_inner, castHN_symm, castHN_power]
  rw [h1, ← inner_creation_eq_inner_annihilation]
  calc ⟪Ext005PairSector.creation V k (power k g), power (2+k) h⟫_ℂ
      = starRingEnd ℂ ⟪power (2+k) h, Ext005PairSector.creation V k (power k g)⟫_ℂ :=
        (inner_conj_symm _ _).symm
    _ = starRingEnd ℂ ((Real.sqrt (((k : ℝ)+1)*((k : ℝ)+2)) : ℂ) *
          (⟪power 2 h, V⟫_ℂ * ⟪h, g⟫_ℂ ^ k)) := by rw [symbol_creation]
    _ = _ := by simp only [map_mul, map_pow, Complex.conj_ofReal, inner_conj_symm]

/-- `𝒲_{0,2}(C)` into the sector `0+k` is the physical pair annihilation of the vector `C† e`. -/
lemma wickBlock_zero_two_eq (k : ℕ) (C : HN L 2 →L[ℂ] HN L 0) (e : L2T L) :
    wickBlock 0 2 k C =
      (castHN (Nat.zero_add k).symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (Ext005PairSector.annihilation (C.adjoint (power 0 e)) k) := by
  apply clm_ext_powers
  intro g h
  rw [symbol_wickBlock, ContinuousLinearMap.comp_apply, ann_cast_symbol,
    ContinuousLinearMap.adjoint_inner_left, power_zero_eq g e, wickCoeff_zero_two]

/-! ### The number block -/

lemma numberBlock_zero (K : HN L 1 →L[ℂ] HN L 1) :
    Ext005QuadraticEnergyR108.numberBlock K 0 = 0 := by
  unfold Ext005QuadraticEnergyR108.numberBlock
  rw [dif_neg (show ¬ (1 ≤ 0) by omega)]

lemma wickCoeff_one_one (k : ℕ) : wickCoeff 1 1 k = ((1 + k : ℕ) : ℝ) := by
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [wickCoeff_balanced, Nat.add_comm 1 k, Nat.factorial_succ]
  push_cast
  first
  | (rw [mul_div_assoc, div_self hk.ne', mul_one])
  | field_simp

/-- `𝒲_{1,1}(K)` on the sector `1+k` is the DEF-009 number block of `K`. -/
lemma wickBlock_one_one (k : ℕ) (K : HN L 1 →L[ℂ] HN L 1) :
    wickBlock 1 1 k K = Ext005QuadraticEnergyR108.numberBlock K (1 + k) := by
  ext z : 1
  rw [wickBlock_balanced, wickCoeff_one_one]
  unfold Ext005QuadraticEnergyR108.numberBlock
  rw [dif_pos (Nat.le_add_right 1 k)]
  have h1 : PhysicalPlacements.physicalQ_N_p L (1 + k) 1 (Nat.le_add_right 1 k) K =
      KernelDefinition.U_N_r (r := 1) (q := k) K := by
    change KernelDefinition.physicalU_N_r L (1 + k) 1 (Nat.le_add_right 1 k) K = _
    rw [PlacementConsistency.physicalU_N_r_eq_genericU_N_r, QuantumNLS.MixedCommutator.genericU_add_eq]
  rw [h1]
  simp only [ContinuousLinearMap.smul_apply, Complex.ofReal_natCast]
  all_goals rfl

lemma numberBlock_smul (c : ℂ) (K : HN L 1 →L[ℂ] HN L 1) (j : ℕ) :
    Ext005QuadraticEnergyR108.numberBlock (c • K) j = c • Ext005QuadraticEnergyR108.numberBlock K j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · ext w
    simp [numberBlock_zero]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ j from hj)
    rw [← wickBlock_one_one, ← wickBlock_one_one, wickBlock_smul]

/-! ### Scalars -/

lemma inner_annihilation_smul (c : ℂ) (b : HN L 2) (n : ℕ) (z : HN L n) (w : HN L (2+n)) :
    ⟪z, Ext005PairSector.annihilation (c • b) n w⟫_ℂ =
      starRingEnd ℂ c * ⟪z, Ext005PairSector.annihilation b n w⟫_ℂ := by
  rw [← inner_creation_eq_inner_annihilation, ← inner_creation_eq_inner_annihilation,
    Ext006FiniteExponentialR39a.creation_smul, inner_smul_left]

lemma annihilation_zero_vec (n : ℕ) : Ext005PairSector.annihilation (0 : HN L 2) n = 0 := by
  have h := Prop022FormContinuityR119.annihilation_sub (0 : HN L 2) 0 n
  rw [sub_self, sub_self] at h
  exact h

lemma creation_zero_vec (n : ℕ) (z : HN L n) : Ext005PairSector.creation (0 : HN L 2) n z = 0 := by
  rw [Ext005PairSector.creation, annihilation_zero_vec, map_zero]
  all_goals rfl

lemma choose_two_mul (s : ℕ) : (s+2).choose 2 * 2 = (s+2) * (s+1) := by
  first
  | (have h := Nat.succ_mul_choose_eq (s+1) 1
     rw [Nat.choose_one_right] at h
     simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h.symm)
  | (rw [Nat.choose_two_right, show s + 2 - 1 = s + 1 by omega]
     exact Nat.div_mul_cancel (by
       have := Nat.even_mul_succ_self (s+1)
       rw [show s + 1 + 1 = s + 2 by omega, Nat.mul_comm] at this
       exact even_iff_two_dvd.mp this))

lemma cellCoeff_one_one (N m : ℕ) (hN : 0 < N) : cellCoeff N m 1 1 = (m : ℝ) ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cellCoeff
  rw [show (1 + 1 : ℕ) = 2 from rfl, Real.sq_sqrt hN'.le, div_self hN'.ne']
  simp [Nat.choose_one_right, sq]

lemma cellCoeff_zero_two (N m : ℕ) (hN : 0 < N) : cellCoeff N m 0 2 = (m.choose 2 : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cellCoeff
  rw [show (0 + 2 : ℕ) = 2 from rfl, Real.sq_sqrt hN'.le, div_self hN'.ne']
  simp

lemma cellCoeff_two_zero (N m : ℕ) (hN : 0 < N) : cellCoeff N m 2 0 = (m.choose 2 : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cellCoeff
  rw [show (2 + 0 : ℕ) = 2 from rfl, Real.sq_sqrt hN'.le, div_self hN'.ne']
  simp

/-! ### The pair coefficient, shifted to the order index `m = r+1` -/

/-- `m(m-1)` times the `m`-th pair vector, indexed by `r = m-1`; it vanishes at `r = 0`. -/
def pairShift (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : ℕ → HN L 2
  | 0 => 0
  | s+1 => pairTerm B u s

lemma insertSector_eq_insertion (r a : ℕ) (ha : a ≤ r + a) (u : L2T L) :
    insertSector (r + a) a ha u = insertion r a u :=
  ContinuousLinearMap.ext (fun x => Subtype.ext (insertSector_coe r a ha u x))

lemma mixedTerm_eq (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (r : ℕ) :
    mixedTerm B u r = (((r+1 : ℕ) : ℂ) ^ 2) •
      ck (r+1) 1 1 (Nat.le_add_left 1 r) (Nat.le_add_left 1 r) (B (r+1)) u := by
  unfold mixedTerm ck
  rw [insertSector_eq_insertion r 1 (Nat.le_add_left 1 r) u]

/-! ### Sector components of the three degree-two cells -/

lemma tsum_inner_incl (j : ℕ) (z : HN L j) (f : ∀ n, HN L n) :
    (∑' n, ⟪inclusion L j z n, f n⟫_ℂ) = ⟪z, f j⟫_ℂ := by
  rw [tsum_eq_single j]
  · rw [inclusion_apply_self]
  · intro n hn
    rw [inclusion_apply_ne j n z hn, inner_zero_left]

/-- Pairing of `Qp` with a single-sector vector in a sector `j < 2`. -/
lemma inner_Qp_incl_lt (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) {x : Fock L}
    (hx : x ∈ momentDomain (L := L) 2) (j : ℕ) (hj : j < 2) (z : HN L j) :
    ⟪inclusion L j z, Qp a b x⟫_ℂ =
      ⟪z, Ext005QuadraticEnergyR108.numberBlock a j (x j)⟫_ℂ +
        (1/2 : ℂ) * ⟪z, Ext005PairSector.annihilation b j (x (2+j))⟫_ℂ := by
  rw [Qp_matrix a b x _ hx (inclusion_mem 1 j z),
    tsum_inner_incl j z (fun n => Ext005QuadraticEnergyR108.numberBlock a n (x n)),
    tsum_inner_incl j z (fun n => Ext005PairSector.annihilation b n (x (2+n)))]
  have h3 : (∑' n, ⟪inclusion L j z (2+n), Ext005PairSector.creation b n (x n)⟫_ℂ) = 0 := by
    have h4 : ∀ n, ⟪inclusion L j z (2+n), Ext005PairSector.creation b n (x n)⟫_ℂ = 0 := by
      intro n
      rw [inclusion_apply_ne j (2+n) z (by omega), inner_zero_left]
    rw [tsum_congr h4, tsum_zero]
  rw [h3]
  ring

/-- Pairing of `Qp` with a single-sector vector in a sector `2+n`. -/
lemma inner_Qp_incl_add (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) {x : Fock L}
    (hx : x ∈ momentDomain (L := L) 2) (n : ℕ) (z : HN L (2+n)) :
    ⟪inclusion L (2+n) z, Qp a b x⟫_ℂ =
      ⟪z, Ext005QuadraticEnergyR108.numberBlock a (2+n) (x (2+n))⟫_ℂ +
        (1/2 : ℂ) * (⟪z, Ext005PairSector.annihilation b (2+n) (x (2+(2+n)))⟫_ℂ +
          ⟪z, Ext005PairSector.creation b n (x n)⟫_ℂ) := by
  rw [Qp_matrix a b x _ hx (inclusion_mem 1 (2+n) z),
    tsum_inner_incl (2+n) z (fun m => Ext005QuadraticEnergyR108.numberBlock a m (x m)),
    tsum_inner_incl (2+n) z (fun m => Ext005PairSector.annihilation b m (x (2+m)))]
  have h3 : (∑' m, ⟪inclusion L (2+n) z (2+m), Ext005PairSector.creation b m (x m)⟫_ℂ) =
      ⟪z, Ext005PairSector.creation b n (x n)⟫_ℂ := by
    rw [tsum_eq_single n]
    · rw [inclusion_apply_self]
    · intro m hm
      rw [inclusion_apply_ne (2+n) (2+m) z (by omega), inner_zero_left]
  rw [h3]

lemma inner_sector_smul {j : ℕ} (c : ℂ) (z : HN L j) (v : Fock L) :
    ⟪z, (c • v) j⟫_ℂ = c * ⟪z, v j⟫_ℂ := by
  simp only [lp.coeFn_smul, Pi.smul_apply, inner_smul_right]

lemma castHN_cancel {m n : ℕ} (h : m = n) (w : HN L n) : castHN h (castHN h.symm w) = w := by
  subst h; rfl

lemma wickFock_zero_two_sector (C : HN L 2 →L[ℂ] HN L 0) (e : L2T L) {y : Fock L}
    (hy : MomentFinite y) (j : ℕ) :
    (wickFock 0 2 C y) j = Ext005PairSector.annihilation (C.adjoint (power 0 e)) j (y (2+j)) := by
  have h1 := wickFock_sector 0 2 C hy j
  rw [wickBlock_zero_two_eq j C e] at h1
  have h2 : castHN (Nat.zero_add j) ((wickFock 0 2 C y) (0+j)) = (wickFock 0 2 C y) j :=
    castHN_fock _ _
  rw [← h2, h1]
  exact castHN_cancel (Nat.zero_add j) _

lemma wickFock_two_zero_sector (C : HN L 0 →L[ℂ] HN L 2) (e : L2T L) {y : Fock L}
    (hy : MomentFinite y) (n : ℕ) :
    (wickFock 2 0 C y) (2+n) = Ext005PairSector.creation (C (power 0 e)) n (y n) := by
  rw [wickFock_sector 2 0 C hy n, wickBlock_two_zero_eq n C e]
  change Ext005PairSector.creation (C (power 0 e)) n (castHN (Nat.zero_add n) (y (0+n))) = _
  rw [castHN_fock]

lemma cellDeg_two_expand (N m : ℕ) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) (x : Fock L) :
    cellDeg N m 2 Bm u x =
      cellVec N m 0 2 Bm u x + cellVec N m 1 1 Bm u x + cellVec N m 2 0 Bm u x := by
  unfold cellDeg
  simp [Finset.sum_range_succ]

/-- The `(1,1)` cell, paired with a sector vector. -/
lemma cell11_sector (N r : ℕ) (hN : 0 < N) (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) {x : Fock L}
    (hy : MomentFinite x) (j : ℕ) (z : HN L j) :
    ⟪z, (cellVec N (r+1) 1 1 (B (r+1)) u x) j⟫_ℂ =
      ⟪z, Ext005QuadraticEnergyR108.numberBlock (mixedTerm B u r) j (x j)⟫_ℂ := by
  unfold cellVec
  rw [dif_pos (show (1 ≤ r+1 ∧ 1 ≤ r+1) from ⟨Nat.le_add_left 1 r, Nat.le_add_left 1 r⟩),
    cellCoeff_one_one N (r+1) hN, inner_sector_smul, mixedTerm_eq, numberBlock_smul]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [wickFock_sector_lt 1 1 _ hy 0 (by omega), numberBlock_zero]
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ j from hj)
    rw [wickFock_sector 1 1 _ hy k, wickBlock_one_one, ContinuousLinearMap.smul_apply, inner_smul_right]
    have hc : ((((r+1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) = ((r+1 : ℕ) : ℂ) ^ 2 := by push_cast; ring
    rw [hc]

/-- The `(0,2)` cell, paired with a sector vector. -/
lemma cell02_sector (N r : ℕ) (hN : 0 < N) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (u : L2T L) {x : Fock L}
    (hy : MomentFinite x) (j : ℕ) (z : HN L j) :
    ⟪z, (cellVec N (r+1) 0 2 (B (r+1)) u x) j⟫_ℂ =
      (1/2 : ℂ) * ⟪z, Ext005PairSector.annihilation (pairShift B u r) j (x (2+j))⟫_ℂ := by
  rcases r with _ | s
  · unfold cellVec
    split_ifs with hab
    · exact absurd hab.2 (by omega)
    · simp [pairShift, annihilation_zero_vec]
  · unfold cellVec
    rw [dif_pos (show (0 ≤ s+1+1 ∧ 2 ≤ s+1+1) from ⟨Nat.zero_le _, by omega⟩),
      cellCoeff_zero_two N _ hN, inner_sector_smul, wickFock_zero_two_sector _ u hy,
      ck_adjoint (Nat.zero_le _) (show 2 ≤ s+1+1 by omega) (B _) (hs _) u, ck_vec]
    have e : (insertSector (s+1+1) 2 (show 2 ≤ s+1+1 by omega) u).adjoint
        (B (s+1+1) (power (s+1+1) u)) = (insertion s 2 u).adjoint (B (s+2) (power (s+2) u)) := by
      rw [show insertSector (s+1+1) 2 (show 2 ≤ s+1+1 by omega) u = insertion s 2 u from
        insertSector_eq_insertion s 2 (show 2 ≤ s+2 by omega) u]
    rw [e]
    have hp : pairShift B u (s+1) = (((s+2 : ℕ) : ℂ) * ((s+1 : ℕ) : ℂ)) •
        (insertion s 2 u).adjoint (B (s+2) (power (s+2) u)) := rfl
    rw [hp, inner_annihilation_smul]
    have hc : (((s+1+1).choose 2 : ℕ) : ℂ) * 2 = ((s+2 : ℕ) : ℂ) * ((s+1 : ℕ) : ℂ) := by
      exact_mod_cast choose_two_mul s
    simp only [map_mul, map_natCast]
    push_cast at hc ⊢
    linear_combination (1/2 : ℂ) *
      ⟪z, Ext005PairSector.annihilation ((insertion s 2 u).adjoint (B (s+2) (power (s+2) u))) j
        (x (2+j))⟫_ℂ * hc

/-- The `(2,0)` cell in a sector `j < 2` vanishes. -/
lemma cell20_sector_lt (N r : ℕ) (hN : 0 < N) (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) {x : Fock L}
    (hy : MomentFinite x) (j : ℕ) (hj : j < 2) (z : HN L j) :
    ⟪z, (cellVec N (r+1) 2 0 (B (r+1)) u x) j⟫_ℂ = 0 := by
  unfold cellVec
  split_ifs with hab
  · rw [inner_sector_smul, wickFock_sector_lt 2 0 _ hy j hj]
    simp
  · simp

/-- The `(2,0)` cell in a sector `2+n`, paired with a sector vector. -/
lemma cell20_sector_add (N r : ℕ) (hN : 0 < N) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (u : L2T L) {x : Fock L} (hy : MomentFinite x) (n : ℕ) (z : HN L (2+n)) :
    ⟪z, (cellVec N (r+1) 2 0 (B (r+1)) u x) (2+n)⟫_ℂ =
      (1/2 : ℂ) * ⟪z, Ext005PairSector.creation (pairShift B u r) n (x n)⟫_ℂ := by
  rcases r with _ | s
  · unfold cellVec
    split_ifs with hab
    · exact absurd hab.1 (by omega)
    · simp [pairShift, creation_zero_vec]
  · unfold cellVec
    rw [dif_pos (show (2 ≤ s+1+1 ∧ 0 ≤ s+1+1) from ⟨by omega, Nat.zero_le _⟩),
      cellCoeff_two_zero N _ hN, inner_sector_smul, wickFock_two_zero_sector _ u hy, ck_vec]
    have e : (insertSector (s+1+1) 2 (show 2 ≤ s+1+1 by omega) u).adjoint
        (B (s+1+1) (power (s+1+1) u)) = (insertion s 2 u).adjoint (B (s+2) (power (s+2) u)) := by
      rw [show insertSector (s+1+1) 2 (show 2 ≤ s+1+1 by omega) u = insertion s 2 u from
        insertSector_eq_insertion s 2 (show 2 ≤ s+2 by omega) u]
    rw [e]
    have hp : pairShift B u (s+1) = (((s+2 : ℕ) : ℂ) * ((s+1 : ℕ) : ℂ)) •
        (insertion s 2 u).adjoint (B (s+2) (power (s+2) u)) := rfl
    rw [hp, Ext006FiniteExponentialR39a.creation_smul, inner_smul_right]
    have hc : (((s+1+1).choose 2 : ℕ) : ℂ) * 2 = ((s+2 : ℕ) : ℂ) * ((s+1 : ℕ) : ℂ) := by
      exact_mod_cast choose_two_mul s
    push_cast at hc ⊢
    linear_combination (1/2 : ℂ) *
      ⟪z, Ext005PairSector.creation ((insertion s 2 u).adjoint (B (s+2) (power (s+2) u))) n (x n)⟫_ℂ * hc

/-! ### The degree-two cell of order `m = r+1` -/

lemma quadraticAction_eq_Qp (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) {x : Fock L}
    (hx : x ∈ momentDomain (L := L) 2) : quadraticAction a b ⟨x, hx⟩ = Qp a b x := by
  rw [Qp, quadraticAction, Ext005FormCutoffR109.rootLift_eq 2 x hx]
  all_goals rfl

/-- **The degree-two cell of order `r+1` is the PROP-021 quadratic action at the `(r+1)`-st coefficients.** -/
theorem cellDeg_two_eq (N r : ℕ) (hN : 0 < N) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (u : L2T L) {x : Fock L} (hx : x ∈ momentDomain (L := L) 2)
    (hy : MomentFinite x) :
    cellDeg N (r+1) 2 (B (r+1)) u x =
      quadraticAction (mixedTerm B u r) (pairShift B u r) ⟨x, hx⟩ := by
  rw [quadraticAction_eq_Qp, cellDeg_two_expand]
  apply fock_ext'
  intro j z
  rw [inner_incl]
  have hsplit : ⟪z, (cellVec N (r+1) 0 2 (B (r+1)) u x + cellVec N (r+1) 1 1 (B (r+1)) u x +
      cellVec N (r+1) 2 0 (B (r+1)) u x) j⟫_ℂ =
      ⟪z, (cellVec N (r+1) 0 2 (B (r+1)) u x) j⟫_ℂ + ⟪z, (cellVec N (r+1) 1 1 (B (r+1)) u x) j⟫_ℂ +
        ⟪z, (cellVec N (r+1) 2 0 (B (r+1)) u x) j⟫_ℂ := by
    simp only [lp.coeFn_add, Pi.add_apply, inner_add_right]
  rw [hsplit]
  rcases Nat.lt_or_ge j 2 with hj | hj
  · rw [inner_Qp_incl_lt _ _ hx j hj z, cell02_sector N r hN B hs u hy j z, cell11_sector N r hN B u hy j z,
      cell20_sector_lt N r hN B u hy j hj z]
    ring
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [inner_Qp_incl_add _ _ hx n z, cell02_sector N r hN B hs u hy (2+n) z,
      cell11_sector N r hN B u hy (2+n) z, cell20_sector_add N r hN B u hy n z]
    ring

/-! ### Summation over the interaction orders -/

lemma strongCoordinates_add' (a c : HN L 1 →L[ℂ] HN L 1) (b d : HN L 2) :
    strongCoordinates (a + c) (b + d) = strongCoordinates a b + strongCoordinates c d := by
  have h0 : strongCoordinates (0 : HN L 1 →L[ℂ] HN L 1) (0 : HN L 2) = 0 := by
    have h := strongCoordinates_sub (0 : HN L 1 →L[ℂ] HN L 1) 0 (0 : HN L 2) 0
    rw [sub_self, sub_self, sub_self] at h
    exact h
  have h1 := strongCoordinates_sub (0 : HN L 1 →L[ℂ] HN L 1) c (0 : HN L 2) d
  rw [zero_sub, zero_sub, h0] at h1
  have h2 := strongCoordinates_sub a (-c) b (-d)
  rw [sub_neg_eq_add, sub_neg_eq_add, h1] at h2
  rw [h2]
  abel

/-- The quadratic action at a fixed vector, as a function of the pair of coefficients. -/
def quadΘ (x : Fock L) (hx : x ∈ momentDomain (L := L) 2)
    (p : (HN L 1 →L[ℂ] HN L 1) × HN L 2) : Fock L :=
  quadraticAction p.1 p.2 ⟨x, hx⟩

lemma quadΘ_add (x : Fock L) (hx : x ∈ momentDomain (L := L) 2)
    (p q : (HN L 1 →L[ℂ] HN L 1) × HN L 2) :
    quadΘ x hx (p + q) = quadΘ x hx p + quadΘ x hx q := by
  show strongCoordinates (p.1 + q.1) (p.2 + q.2) (momentRoot 2 ⟨x, hx⟩) =
    strongCoordinates p.1 p.2 (momentRoot 2 ⟨x, hx⟩) + strongCoordinates q.1 q.2 (momentRoot 2 ⟨x, hx⟩)
  rw [strongCoordinates_add', ContinuousLinearMap.add_apply]

lemma continuous_of_norm_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (Θ : E → F) (C : ℝ) (hC : 0 ≤ C) (h : ∀ p q, ‖Θ p - Θ q‖ ≤ C * ‖p - q‖) : Continuous Θ :=
  (LipschitzWith.of_dist_le_mul (f := Θ) (K := Real.toNNReal C) (fun p q => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hC]
    exact h p q)).continuous

lemma continuous_quadΘ (x : Fock L) (hx : x ∈ momentDomain (L := L) 2) :
    Continuous (quadΘ x hx) := by
  have h3 : (0 : ℝ) ≤ 3 * ‖momentRoot 2 ⟨x, hx⟩‖ := by positivity
  refine continuous_of_norm_sub_le (quadΘ x hx) (3 * ‖momentRoot 2 ⟨x, hx⟩‖) h3 (fun p q => ?_)
  have hsub : quadΘ x hx p - quadΘ x hx q =
      strongCoordinates (p.1 - q.1) (p.2 - q.2) (momentRoot 2 ⟨x, hx⟩) := by
    show strongCoordinates p.1 p.2 (momentRoot 2 ⟨x, hx⟩) - strongCoordinates q.1 q.2 (momentRoot 2 ⟨x, hx⟩) = _
    rw [strongCoordinates_sub, ContinuousLinearMap.sub_apply]
  rw [hsub]
  have h1 := ContinuousLinearMap.le_opNorm (strongCoordinates (p.1 - q.1) (p.2 - q.2))
    (momentRoot 2 ⟨x, hx⟩)
  have h2 := strongCoordinates_norm (p.1 - q.1) (p.2 - q.2)
  have h4 : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have h5 : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  have h6 := norm_nonneg (momentRoot 2 ⟨x, hx⟩)
  calc ‖strongCoordinates (p.1 - q.1) (p.2 - q.2) (momentRoot 2 ⟨x, hx⟩)‖
      ≤ ‖strongCoordinates (p.1 - q.1) (p.2 - q.2)‖ * ‖momentRoot 2 ⟨x, hx⟩‖ := h1
    _ ≤ (‖p.1 - q.1‖ + 2 * ‖p.2 - q.2‖) * ‖momentRoot 2 ⟨x, hx⟩‖ :=
        mul_le_mul_of_nonneg_right h2 h6
    _ ≤ (3 * ‖p - q‖) * ‖momentRoot 2 ⟨x, hx⟩‖ := by
        apply mul_le_mul_of_nonneg_right _ h6
        linarith
    _ = 3 * ‖momentRoot 2 ⟨x, hx⟩‖ * ‖p - q‖ := by ring

lemma hasSum_map_of_add {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [AddCommGroup F]
    [TopologicalSpace F] (Θ : E → F) (hadd : ∀ p q, Θ (p + q) = Θ p + Θ q) (hc : Continuous Θ)
    {f : ℕ → E} {a : E} (h : HasSum f a) : HasSum (fun i => Θ (f i)) (Θ a) :=
  h.map (AddMonoidHom.mk' Θ hadd) hc

/-- **The quadratic term.**  `quadVec` is the PROP-021 quadratic action with the literal number and pair
coefficients `numberCoefficient B u`, `pairCoefficient B u` (source `Q7B:eq:quadratic`). -/
theorem quadVec_eq_quadraticAction (N : ℕ) (hN : 0 < N) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M Aa : ℝ) (hA : 0 ≤ Aa) (hB : FactorialBound B M Aa)
    (u : L2T L) (hu : ‖u‖ = 1) {x : Fock L} (hx : x ∈ momentDomain (L := L) 2) (hy : MomentFinite x) :
    quadVec N B u x = quadraticAction (numberCoefficient B u) (pairCoefficient B u) ⟨x, hx⟩ := by
  have hmix : HasSum (mixedTerm B u) (numberCoefficient B u) :=
    (mixed_summable B M Aa hA hB u hu).hasSum
  have hpair : HasSum (pairTerm B u) (pairCoefficient B u) :=
    (pair_summable B M Aa hA hB u hu).hasSum
  have hshift : HasSum (pairShift B u) (pairCoefficient B u) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [pairShift] using hpair
  have hprod : HasSum (fun r => (mixedTerm B u r, pairShift B u r))
      (numberCoefficient B u, pairCoefficient B u) := by
    first
    | exact hmix.prodMk hshift
    | exact hmix.prod_mk hshift
  have hmap := hasSum_map_of_add (quadΘ x hx) (quadΘ_add x hx) (continuous_quadΘ x hx) hprod
  unfold quadVec
  rw [tsum_congr (fun r => cellDeg_two_eq N r hN B hs u hx hy)]
  exact hmap.tsum_eq

end QuantumNLS.Prop024WQuadratic

#print axioms QuantumNLS.Prop024WQuadratic.wickBlock_two_zero_eq
#print axioms QuantumNLS.Prop024WQuadratic.wickBlock_zero_two_eq
#print axioms QuantumNLS.Prop024WQuadratic.wickBlock_one_one
#print axioms QuantumNLS.Prop024WQuadratic.cellDeg_two_eq
#print axioms QuantumNLS.Prop024WQuadratic.quadVec_eq_quadraticAction

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WQuadratic." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WQuadratic." then
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
  Lean.logInfo m!"Prop024WQuadratic aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
