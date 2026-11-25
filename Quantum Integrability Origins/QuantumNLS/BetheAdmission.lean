import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Finset.Max
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-!
Elementary actual Bethe-root constituents for DEF-006 and R-4C8D7C9E.
Report pin: 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
Source: chapters/definitions.tex:39--43, foundations/A03.tex:19--31,
foundations/periodic_basis.tex:133--161 and root_response/F01.tex:4--20.

Indices here are zero based and INCREASING. Thus I_i = n_i + i - (N-1)/2.
The decreasing convention in periodic_basis.tex is reversed, never negated.
The self interaction is zero, so the displayed sum over all j is exactly
the source sum over j != i. Real roots below mean solutions of this explicit
arctangent equation, not eigenvectors or a supplied abstract spectral basis.

This module proves at-most-one solution for every right-hand side, order of
any solution with corrected labels, and existence in the one-particle case.
It does not choose roots without an existence proof, assume a Bethe basis,
or identify the interacting coefficient transform U5 with Fourier U4 U3.
-/

noncomputable section
open scoped BigOperators

namespace QuantumNLS.BetheAdmission

/-- Sorted Bose labels, with repetitions retained. -/
abbrev CorrectedLabels (N : ℕ) := {n : Fin N → ℤ // Monotone n}

/-- Inverse of the corrected-label formula, in zero-based increasing order. -/
def quantumNumbers {N : ℕ} (n : Fin N → ℤ) (i : Fin N) : ℝ :=
  (n i : ℝ) + (i.val : ℝ) - ((N : ℝ) - 1) / 2

theorem corrected_recovery {N : ℕ} (n : Fin N → ℤ) (i : Fin N) :
    quantumNumbers n i - ((i.val : ℝ) + 1) + ((N : ℝ) + 1) / 2 = n i := by
  simp only [quantumNumbers]
  ring

/-- Membership in Z + (N-1)/2 is witnessed by an explicit integer. -/
theorem quantumNumbers_lattice {N : ℕ} (n : Fin N → ℤ) (i : Fin N) :
    ∃ z : ℤ, quantumNumbers n i = (z : ℝ) + ((N : ℝ) - 1) / 2 := by
  refine ⟨n i + (i.val : ℤ) - (N : ℤ) + 1, ?_⟩
  simp only [quantumNumbers, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one]
  ring

theorem quantumNumbers_strictMono {N : ℕ} (n : CorrectedLabels N) :
    StrictMono (quantumNumbers n.val) := by
  intro i j hij
  have hn : (n.val i : ℝ) ≤ n.val j := by exact_mod_cast n.property (le_of_lt hij)
  have hi : (i.val : ℝ) < j.val := by exact_mod_cast hij
  dsimp [quantumNumbers]
  linarith

/-- The converse uses the integer lattice: adjacent positive quantum-number
gaps are at least one, so the corrected labels are nondecreasing. -/
theorem quantumNumbers_strictMono_iff {N : ℕ} (n : Fin N → ℤ) :
    StrictMono (quantumNumbers n) ↔ Monotone n := by
  refine ⟨?_, fun hn => quantumNumbers_strictMono ⟨n, hn⟩⟩
  intro hs
  cases N with
  | zero => intro i; exact Fin.elim0 i
  | succ N =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have h := hs (Fin.castSucc_lt_succ (i := i))
    by_contra hn
    have hint : n i.succ + 1 ≤ n i.castSucc := by omega
    have hr : (n i.succ : ℝ) + 1 ≤ n i.castSucc := by exact_mod_cast hint
    simp only [quantumNumbers, Fin.val_castSucc, Fin.val_succ, Nat.cast_add,
      Nat.cast_one] at h
    linarith

/-- Exact conversion to the decreasing enumeration used in periodic_basis.tex:
the array is reversed; neither a root nor a physical label is negated. -/
theorem quantumNumbers_reverse {N : ℕ} (n : Fin N → ℤ) (i : Fin N) :
    quantumNumbers n i.rev =
      (n i.rev : ℝ) + (((N : ℝ) - 1) / 2 - (i.val : ℝ)) := by
  have hv : i.rev.val + i.val + 1 = N := by simp only [Fin.val_rev]; omega
  have hr : (i.rev.val : ℝ) + (i.val : ℝ) + 1 = N := by exact_mod_cast hv
  unfold quantumNumbers
  linarith

/-- The centering term contributes zero to total quantum momentum. -/
theorem sum_quantumNumbers {N : ℕ} (n : Fin N → ℤ) :
    ∑ i, quantumNumbers n i = ∑ i, (n i : ℝ) := by
  have hrank : ∑ i : Fin N, (i.val : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    clear n
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring
  simp only [quantumNumbers, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hrank, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The globally smooth logarithmic Bethe map, for arbitrary real configurations. -/
def logMap {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) (i : Fin N) : ℝ :=
  L * q i + 2 * ∑ j, Real.arctan ((q i - q j) / c)

theorem logMap_erase {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) (i : Fin N) :
    logMap L c q i =
      L * q i + 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan ((q i - q j) / c) := by
  unfold logMap
  congr 2
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm.trans (by simp)

/-- The actual DEF-006 equation with corrected labels, at arbitrary N. -/
def Solves {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop :=
  ∀ i, logMap L c q i = 2 * Real.pi * quantumNumbers n i

/-- Maximum-coordinate argument: positivity of L and c gives order comparison
without any assumed inverse Jacobian or existence of roots. -/
theorem logMap_order_reflecting {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {x y : Fin N → ℝ} (h : ∀ i, logMap L c x i ≤ logMap L c y i) :
    ∀ i, x i ≤ y i := by
  intro k
  by_contra hk
  have hk' : 0 < x k - y k := sub_pos.mpr (lt_of_not_ge hk)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j => x j - y j)
    ⟨k, Finset.mem_univ k⟩
  have hpos : 0 < x i - y i := lt_of_lt_of_le hk' (hi k (Finset.mem_univ k))
  have hs : (∑ j, Real.arctan ((y i - y j) / c)) ≤
      ∑ j, Real.arctan ((x i - x j) / c) := by
    apply Finset.sum_le_sum
    intro j _
    apply Real.arctan_mono
    apply (div_le_div_iff_of_pos_right hc).mpr
    have hj := hi j (Finset.mem_univ j)
    linarith
  have hp : 0 < L * (x i - y i) := mul_pos hL hpos
  have he := h i
  dsimp [logMap] at he
  nlinarith

theorem logMap_injective {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    Function.Injective (logMap (N := N) L c) := by
  intro x y hxy
  funext i
  exact le_antisymm
    (logMap_order_reflecting hL hc (fun j => le_of_eq (congrFun hxy j)) i)
    (logMap_order_reflecting hL hc (fun j => le_of_eq (congrFun hxy.symm j)) i)

/-- Uniqueness constituent of basis:lem:roots; existence is not a hypothesis
hidden in a root-selection definition. The tuples need not be sorted here. -/
theorem roots_unique {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} {q r : Fin N → ℝ} (hq : Solves L c n q) (hr : Solves L c n r) :
    q = r := by
  apply logMap_injective hL hc
  funext i
  exact (hq i).trans (hr i).symm

/-- The equations also recover the corrected labels from a real root tuple. -/
theorem roots_determine_labels {N : ℕ} {L c : ℝ} {n m : Fin N → ℤ}
    {q : Fin N → ℝ} (hn : Solves L c n q) (hm : Solves L c m q) : n = m := by
  funext i
  have he := (hn i).symm.trans (hm i)
  have hpi := Real.pi_pos
  have hnum : quantumNumbers n i = quantumNumbers m i := by nlinarith
  have hcast : (n i : ℝ) = m i := by
    unfold quantumNumbers at hnum
    linarith
  exact_mod_cast hcast

/-- Ordered forcing produces ordered roots, whenever both solutions exist. -/
theorem roots_order_of_labels {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n m : Fin N → ℤ} {q r : Fin N → ℝ}
    (hnm : ∀ i, n i ≤ m i) (hq : Solves L c n q) (hr : Solves L c m r) :
    ∀ i, q i ≤ r i := by
  apply logMap_order_reflecting hL hc
  intro i
  rw [hq i, hr i]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) Real.pi_pos.le)
  unfold quantumNumbers
  have hn : (n i : ℝ) ≤ m i := by exact_mod_cast hnm i
  linarith

/-- Order of coordinates of the Bethe map within one configuration. -/
theorem logMap_coordinate_mono {N : ℕ} {L c : ℝ} (hL : 0 ≤ L) (hc : 0 < c)
    (q : Fin N → ℝ) {i j : Fin N} (hij : q i ≤ q j) :
    logMap L c q i ≤ logMap L c q j := by
  apply add_le_add (mul_le_mul_of_nonneg_left hij hL)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro k _
  exact Real.arctan_mono ((div_le_div_iff_of_pos_right hc).mpr (sub_le_sub_right hij _))

/-- Every actual solution at sorted corrected labels has strictly increasing
rapidities. Repeated Bose labels still yield distinct roots at c > 0. -/
theorem roots_strictMono {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : CorrectedLabels N) {q : Fin N → ℝ} (hq : Solves L c n.val q) :
    StrictMono q := by
  intro i j hij
  by_contra hqij
  have hmap := logMap_coordinate_mono hL.le hc q (le_of_not_gt hqij)
  rw [hq j, hq i] at hmap
  have hn := quantumNumbers_strictMono n hij
  have hpi := Real.pi_pos
  nlinarith

/-- Odd pair interactions cancel exactly, including the zero diagonal. -/
theorem interaction_sum_zero {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    ∑ i, ∑ j, Real.arctan ((q i - q j) / c) = 0 := by
  have hpair (i j : Fin N) : Real.arctan ((q i - q j) / c) =
      -Real.arctan ((q j - q i) / c) := by
    rw [← Real.arctan_neg]
    congr 1
    ring
  have hswap := Finset.sum_comm (s := (Finset.univ : Finset (Fin N)))
    (t := Finset.univ) (f := fun i j => Real.arctan ((q i - q j) / c))
  have hneg : (∑ j, ∑ i, Real.arctan ((q i - q j) / c)) =
      -(∑ i, ∑ j, Real.arctan ((q i - q j) / c)) := by
    calc
      _ = ∑ j, ∑ i, -Real.arctan ((q j - q i) / c) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_congr rfl (fun i _ => hpair i j)
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

theorem sum_logMap {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) :
    ∑ i, logMap L c q i = L * ∑ i, q i := by
  simp only [logMap, Finset.sum_add_distrib, ← Finset.mul_sum,
    interaction_sum_zero, mul_zero, add_zero]

/-- Exact total momentum relation, independent of any spectral construction. -/
theorem roots_momentum {N : ℕ} {L c : ℝ} {n : Fin N → ℤ} {q : Fin N → ℝ}
    (hq : Solves L c n q) :
    L * ∑ i, q i = 2 * Real.pi * ∑ i, (n i : ℝ) := by
  calc
    _ = ∑ i, logMap L c q i := (sum_logMap L c q).symm
    _ = ∑ i, 2 * Real.pi * quantumNumbers n i :=
      Finset.sum_congr rfl (fun i _ => hq i)
    _ = 2 * Real.pi * ∑ i, quantumNumbers n i := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [sum_quantumNumbers]

/-- At N=1 the root is explicitly constructed, for every coupling. -/
theorem oneParticle_solves {L : ℝ} (hL : L ≠ 0) (c : ℝ) (n : Fin 1 → ℤ) :
    Solves L c n (fun i => 2 * Real.pi * (n i : ℝ) / L) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [logMap, quantumNumbers]
  field_simp

/-- A genuine existence-and-uniqueness statement in the one-particle sector.
For general N this module deliberately asserts only uniqueness of solutions. -/
theorem oneParticle_existsUnique {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin 1 → ℤ) : ∃! q : Fin 1 → ℝ, Solves L c n q := by
  exact ⟨_, oneParticle_solves hL.ne' c n,
    fun q hq => roots_unique hL hc hq (oneParticle_solves hL.ne' c n)⟩

end QuantumNLS.BetheAdmission

/- Kernel audits for every declaration in this owned module. -/
#print axioms QuantumNLS.BetheAdmission.CorrectedLabels
#print axioms QuantumNLS.BetheAdmission.quantumNumbers
#print axioms QuantumNLS.BetheAdmission.corrected_recovery
#print axioms QuantumNLS.BetheAdmission.quantumNumbers_lattice
#print axioms QuantumNLS.BetheAdmission.quantumNumbers_strictMono
#print axioms QuantumNLS.BetheAdmission.quantumNumbers_strictMono_iff
#print axioms QuantumNLS.BetheAdmission.quantumNumbers_reverse
#print axioms QuantumNLS.BetheAdmission.sum_quantumNumbers
#print axioms QuantumNLS.BetheAdmission.logMap
#print axioms QuantumNLS.BetheAdmission.logMap_erase
#print axioms QuantumNLS.BetheAdmission.Solves
#print axioms QuantumNLS.BetheAdmission.logMap_order_reflecting
#print axioms QuantumNLS.BetheAdmission.logMap_injective
#print axioms QuantumNLS.BetheAdmission.roots_unique
#print axioms QuantumNLS.BetheAdmission.roots_determine_labels
#print axioms QuantumNLS.BetheAdmission.roots_order_of_labels
#print axioms QuantumNLS.BetheAdmission.logMap_coordinate_mono
#print axioms QuantumNLS.BetheAdmission.roots_strictMono
#print axioms QuantumNLS.BetheAdmission.interaction_sum_zero
#print axioms QuantumNLS.BetheAdmission.sum_logMap
#print axioms QuantumNLS.BetheAdmission.roots_momentum
#print axioms QuantumNLS.BetheAdmission.oneParticle_solves
#print axioms QuantumNLS.BetheAdmission.oneParticle_existsUnique
