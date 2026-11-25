import NlsGge.Spectral.RTreeCore38
import NlsGge.Spectral.R3cUniformRiccati38
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # RTree piece T7: Born trees

`bornTrees38 ℓ` lists the `Cat_ℓ` ternary resolvent trees of `G_{2ℓ+1}` (all nodes `R`, all leaf orders
`0`), `bornG38 η N z ℓ = (-1)^ℓ * Σ_T eval T` is the Born term `G_{2ℓ+1}` of the Riccati solution
`Γ = G₁ + G₃ + ...`, with `G₁ = R Ū` and `G_{2ℓ+3} = -R(U Σ_{a+b=ℓ} G_{2a+1} G_{2b+1})`.
This file proves the recursion `bornG38_rec`, the counters `bornTrees38_nodes`, the count
`bornTrees38_length = catalan ℓ`, continuity/periodicity, and the sup bound
`‖bornG38 ℓ‖_∞ ≤ Cat_ℓ (A/(2η))^{2ℓ+1}`. -/

/-- T7: Born trees. The recursive call is written over `List.attach` to let Lean see termination;
`bornTrees38_succ` gives the unattached form. -/
def bornTrees38 : ℕ → List RTree38
  | 0 => [.base .R 0]
  | ℓ+1 => (List.range (ℓ+1)).attach.flatMap (fun a =>
      (bornTrees38 a.1).flatMap (fun A => (bornTrees38 (ℓ - a.1)).map (fun B => .node .R 0 A B)))
decreasing_by
  all_goals first | omega | (have := List.mem_range.mp a.2; omega)

theorem bornTrees38_zero : bornTrees38 0 = [.base .R 0] := by
  rw [bornTrees38]

theorem bornTrees38_succ (ℓ : ℕ) : bornTrees38 (ℓ+1) = (List.range (ℓ+1)).flatMap (fun a =>
      (bornTrees38 a).flatMap (fun A => (bornTrees38 (ℓ - a)).map (fun B => .node .R 0 A B))) := by
  rw [bornTrees38]
  simp [List.flatMap_def]

def bornG38 (η : ℝ) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) : ℝ → ℂ :=
  fun x => (-1:ℂ)^ℓ * ((bornTrees38 ℓ).map (fun T => T.eval η N z x)).sum

/-! ## Counters -/

theorem bornTrees38_nodes (ℓ : ℕ) :
    ∀ T ∈ bornTrees38 ℓ, T.nodes = 2*ℓ+1 ∧ T.dsum = 0 ∧ T.numR = 2*ℓ+1 := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    cases ℓ with
    | zero =>
      intro T hT
      rw [bornTrees38_zero] at hT
      simp only [List.mem_singleton] at hT
      subst hT
      simp [RTree38.nodes, RTree38.dsum, RTree38.numR]
    | succ ℓ =>
      intro T hT
      rw [bornTrees38_succ] at hT
      simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hT
      obtain ⟨a, ha, A, hA, B, hB, rfl⟩ := hT
      have h1 := ih a (by omega) A hA
      have h2 := ih (ℓ - a) (by omega) B hB
      simp only [RTree38.nodes, RTree38.dsum, RTree38.numR]
      refine ⟨by omega, by omega, ?_⟩
      simp only [ite_true]
      omega

theorem list_flatMap_sum38 {α β : Type*} (l : List α) (g : α → List β) (f : β → ℂ) :
    ((l.flatMap g).map f).sum = (l.map (fun a => ((g a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem list_range_sum38 {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem bornTrees38_length (ℓ : ℕ) : (bornTrees38 ℓ).length = catalan ℓ := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    cases ℓ with
    | zero => rw [bornTrees38_zero]; simp
    | succ ℓ =>
      rw [bornTrees38_succ, catalan_succ, List.length_flatMap]
      have e : ∀ a ∈ List.range (ℓ+1), ((bornTrees38 a).flatMap (fun A =>
          (bornTrees38 (ℓ - a)).map (fun B => RTree38.node .R 0 A B))).length =
          catalan a * catalan (ℓ - a) := by
        intro a ha
        have ha' := List.mem_range.mp ha
        rw [List.length_flatMap]
        simp [ih a (by omega), ih (ℓ - a) (by omega)]
      rw [List.map_congr_left e, list_range_sum38 (ℓ+1) (fun a => catalan a * catalan (ℓ - a))]
      rw [← Fin.sum_univ_eq_sum_range (fun a => catalan a * catalan (ℓ - a)) (ℓ+1)]

/-! ## Linearity of `R` -/

theorem resolv38_const_mul38 (η : ℝ) (c : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    resolv38 η (fun y => c * g y) x = c * resolv38 η g x := by
  unfold resolv38 resInt38
  have h : ∀ t, Real.exp (2 * η * t) • (c * g t) = c * (Real.exp (2 * η * t) • g t) :=
    fun t => (mul_smul_comm _ _ _).symm
  simp_rw [h]
  rw [integral_const_mul, mul_smul_comm]

/-! ## The sum over Born trees -/

def bornSum38 (η : ℝ) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) (x : ℝ) : ℂ :=
  ((bornTrees38 ℓ).map (fun T => T.eval η N z x)).sum

theorem bornG38_eq (η : ℝ) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) (x : ℝ) :
    bornG38 η N z ℓ x = (-1:ℂ)^ℓ * bornSum38 η N z ℓ x := rfl

theorem bornSum38_cont_per {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) :
    Continuous (bornSum38 η N z ℓ) ∧ Function.Periodic (bornSum38 η N z ℓ) 1 :=
  list_sum_cont_per38 (bornTrees38 ℓ) (fun T y => T.eval η N z y)
    (fun T _ => RTree38.eval_cont_per hη N z T)

theorem bornG38_cont_per {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) :
    Continuous (bornG38 η N z ℓ) ∧ Function.Periodic (bornG38 η N z ℓ) 1 := by
  have h := bornSum38_cont_per hη N z ℓ
  refine ⟨continuous_const.mul h.1, fun y => ?_⟩
  simp only [bornG38_eq, h.2 y]

theorem sum_nodes_pair38 {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N)
    (LA LB : List RTree38) (hLA : ∀ A ∈ LA, Continuous (A.eval η N z) ∧ Function.Periodic (A.eval η N z) 1)
    (hLB : ∀ B ∈ LB, Continuous (B.eval η N z) ∧ Function.Periodic (B.eval η N z) 1) (x : ℝ) :
    ((LA.flatMap fun A => LB.map fun B => RTree38.node .R 0 A B).map
        (fun T => T.eval η N z x)).sum =
      resolv38 η (fun y => leafU38 N z 0 y * ((LA.map fun A => A.eval η N z y).sum) *
        ((LB.map fun B => B.eval η N z y).sum)) x := by
  have hU := perC1_leafU38 N z 0
  rw [list_flatMap_sum38]
  have h1 : ∀ A ∈ LA, ((LB.map fun B => RTree38.node .R 0 A B).map
      (fun T => T.eval η N z x)).sum =
      resolv38 η (fun y => leafU38 N z 0 y * A.eval η N z y *
        ((LB.map fun B => B.eval η N z y).sum)) x := by
    intro A hA
    have hAc := hLA A hA
    have h := RKind38.act_list_sum hη .R LB
      (fun B y => leafU38 N z 0 y * A.eval η N z y * B.eval η N z y)
      (fun B hB => ⟨(hU.cont.mul hAc.1).mul (hLB B hB).1,
        fun y => by simp only [hU.per y, hAc.2 y, (hLB B hB).2 y]⟩) x
    simp only [RKind38.act] at h
    rw [List.map_map]
    simp only [Function.comp_def, RTree38.eval, RKind38.act]
    rw [← h]
    congr 2
    funext y
    rw [List.sum_map_mul_left]
  rw [List.map_congr_left h1]
  have h2 := RKind38.act_list_sum hη .R LA
    (fun A y => leafU38 N z 0 y * A.eval η N z y * ((LB.map fun B => B.eval η N z y).sum))
    (fun A hA => ⟨(hU.cont.mul (hLA A hA).1).mul (list_sum_cont_per38 LB (fun B y => B.eval η N z y) hLB).1,
      fun y => by
        simp only [hU.per y, (hLA A hA).2 y, (list_sum_cont_per38 LB (fun B y => B.eval η N z y) hLB).2 y]⟩) x
  simp only [RKind38.act] at h2
  rw [← h2]
  congr 2
  funext y
  rw [List.sum_map_mul_right, List.sum_map_mul_left]

theorem bornTrees38_eval_cont_per {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) :
    ∀ A ∈ bornTrees38 ℓ, Continuous (A.eval η N z) ∧ Function.Periodic (A.eval η N z) 1 :=
  fun A _ => RTree38.eval_cont_per hη N z A

theorem bornSum38_succ {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) (x : ℝ) :
    bornSum38 η N z (ℓ+1) x =
      resolv38 η (fun y => leafU38 N z 0 y *
        ∑ a ∈ Finset.range (ℓ+1), bornSum38 η N z a y * bornSum38 η N z (ℓ - a) y) x := by
  have hU := perC1_leafU38 N z 0
  unfold bornSum38
  rw [bornTrees38_succ, list_flatMap_sum38]
  have h1 : ∀ a ∈ List.range (ℓ+1), (((bornTrees38 a).flatMap (fun A =>
      (bornTrees38 (ℓ - a)).map (fun B => RTree38.node .R 0 A B))).map
        (fun T => T.eval η N z x)).sum =
      resolv38 η (fun y => leafU38 N z 0 y * (bornSum38 η N z a y * bornSum38 η N z (ℓ - a) y)) x := by
    intro a _
    rw [sum_nodes_pair38 hη N z _ _ (bornTrees38_eval_cont_per hη N z a)
      (bornTrees38_eval_cont_per hη N z (ℓ - a)) x]
    unfold bornSum38
    congr 2
    funext y
    ring
  rw [List.map_congr_left h1]
  have hF : ∀ a ∈ List.range (ℓ+1), Continuous (fun y => leafU38 N z 0 y *
      (bornSum38 η N z a y * bornSum38 η N z (ℓ - a) y)) ∧
      Function.Periodic (fun y => leafU38 N z 0 y *
      (bornSum38 η N z a y * bornSum38 η N z (ℓ - a) y)) 1 := by
    intro a _
    have ha := bornSum38_cont_per hη N z a
    have hb := bornSum38_cont_per hη N z (ℓ - a)
    exact ⟨hU.cont.mul (ha.1.mul hb.1), fun y => by simp only [hU.per y, ha.2 y, hb.2 y]⟩
  have h2 := RKind38.act_list_sum hη .R (List.range (ℓ+1))
    (fun a y => leafU38 N z 0 y * (bornSum38 η N z a y * bornSum38 η N z (ℓ - a) y)) hF x
  simp only [RKind38.act] at h2
  rw [← h2]
  congr 2
  funext y
  rw [← list_range_sum38, List.sum_map_mul_left]
  rfl

theorem bornG38_rec {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (ℓ : ℕ) :
    bornG38 η N z (ℓ+1) =
      fun x => -resolv38 η (fun y => leafU38 N z 0 y *
        ∑ a ∈ Finset.range (ℓ+1), bornG38 η N z a y * bornG38 η N z (ℓ - a) y) x := by
  funext x
  have e : ∀ y, ∑ a ∈ Finset.range (ℓ+1), bornG38 η N z a y * bornG38 η N z (ℓ - a) y =
      (-1:ℂ)^ℓ * ∑ a ∈ Finset.range (ℓ+1), bornSum38 η N z a y * bornSum38 η N z (ℓ - a) y := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : a ≤ ℓ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have : (-1:ℂ)^ℓ = (-1)^a * (-1)^(ℓ - a) := by rw [← pow_add]; congr 1; omega
    rw [bornG38_eq, bornG38_eq, this]
    ring
  have e2 : (fun y => leafU38 N z 0 y *
      ∑ a ∈ Finset.range (ℓ+1), bornG38 η N z a y * bornG38 η N z (ℓ - a) y) =
      fun y => (-1:ℂ)^ℓ * (leafU38 N z 0 y *
        ∑ a ∈ Finset.range (ℓ+1), bornSum38 η N z a y * bornSum38 η N z (ℓ - a) y) := by
    funext y
    rw [e y]
    ring
  rw [e2, resolv38_const_mul38, ← bornSum38_succ hη, bornG38_eq]
  rw [pow_succ]
  ring

theorem bornG38_zero (η : ℝ) (N : ℕ) (z : FourierPlane N) :
    bornG38 η N z 0 = resolv38 η (fun y => star (planeReal N z y)) := by
  funext x
  simp only [bornG38, bornTrees38_zero, RTree38.eval, RKind38.act, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, pow_zero, one_mul, add_zero]
  rfl

/-! ## Sup bounds -/

theorem RKind38.norm_act_le {η : ℝ} (hη : 0 < η) (κ : RKind38) {g : ℝ → ℂ} (hg : Continuous g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (x : ℝ) : ‖κ.act η g x‖ ≤ B / (2 * η) := by
  cases κ with
  | R => exact resolv38_bound hη hg hB x
  | S =>
    simp only [RKind38.act]
    rw [norm_div]
    have h2 : ‖(2 * (η : ℂ))‖ = 2 * η := by
      rw [norm_mul]; simp [abs_of_pos hη]
    rw [h2]
    exact div_le_div_of_nonneg_right (hB x) (by positivity)

/-- Trees with all leaf orders zero: `‖eval T‖_∞ ≤ (A/(2η))^{nodes}` when `‖U‖_∞ ≤ A`. -/
theorem RTree38.sup_le_dsum_zero {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) {A : ℝ}
    (hA : ∀ x, ‖planeReal N z x‖ ≤ A) :
    ∀ T : RTree38, T.dsum = 0 → ∀ x, ‖T.eval η N z x‖ ≤ (A / (2 * η)) ^ T.nodes
  | .base κ d, h, x => by
    have hd : d = 0 := h
    subst hd
    have := RKind38.norm_act_le hη κ (perC1_leafUbar38 N z 0).cont
      (B := A) (fun y => by
        show ‖star (planeReal N z y)‖ ≤ A
        rw [norm_star]; exact hA y) x
    simpa [RTree38.eval, RTree38.nodes] using this
  | .node κ d A' B', h, x => by
    simp only [RTree38.dsum] at h
    have hd : d = 0 := by omega
    have hdA : A'.dsum = 0 := by omega
    have hdB : B'.dsum = 0 := by omega
    subst hd
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
    have ha0 : 0 ≤ A / (2 * η) := by positivity
    have hAc := RTree38.eval_cont_per hη N z A'
    have hBc := RTree38.eval_cont_per hη N z B'
    have hUc := (perC1_leafU38 N z 0).cont
    have hb : ∀ y, ‖leafU38 N z 0 y * A'.eval η N z y * B'.eval η N z y‖ ≤
        (A / (2 * η)) ^ (1 + A'.nodes + B'.nodes) * (2 * η) := by
      intro y
      rw [norm_mul, norm_mul]
      have h1 : ‖leafU38 N z 0 y‖ ≤ A := hA y
      have h2 := RTree38.sup_le_dsum_zero hη N z hA A' hdA y
      have h3 := RTree38.sup_le_dsum_zero hη N z hA B' hdB y
      calc ‖leafU38 N z 0 y‖ * ‖A'.eval η N z y‖ * ‖B'.eval η N z y‖
          ≤ A * (A / (2 * η)) ^ A'.nodes * (A / (2 * η)) ^ B'.nodes :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hA0) h3 (norm_nonneg _)
              (mul_nonneg hA0 (pow_nonneg ha0 _))
        _ = (A / (2 * η)) ^ (1 + A'.nodes + B'.nodes) * (2 * η) := by
            have key : ∀ a : ℝ, A = a * (2 * η) →
                A * a ^ A'.nodes * a ^ B'.nodes = a ^ (1 + A'.nodes + B'.nodes) * (2 * η) := by
              intro a ha
              calc A * a ^ A'.nodes * a ^ B'.nodes = a * (2 * η) * a ^ A'.nodes * a ^ B'.nodes := by
                    rw [← ha]
                _ = _ := by ring
            exact key _ (by field_simp)
    have hg : Continuous (fun y => leafU38 N z 0 y * A'.eval η N z y * B'.eval η N z y) :=
      (hUc.mul hAc.1).mul hBc.1
    have := RKind38.norm_act_le hη κ hg hb x
    have e : (A / (2 * η)) ^ (1 + A'.nodes + B'.nodes) * (2 * η) / (2 * η) =
        (A / (2 * η)) ^ (1 + A'.nodes + B'.nodes) := by field_simp
    rw [e] at this
    simpa [RTree38.eval, RTree38.nodes] using this

theorem norm_list_sum_le_length_mul38 {α : Type*} (L : List α) (f : α → ℂ) (b : ℝ)
    (h : ∀ a ∈ L, ‖f a‖ ≤ b) : ‖(L.map f).sum‖ ≤ L.length * b := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun a ha => h a (by simp [ha]))
    calc ‖f a + (L.map f).sum‖ ≤ ‖f a‖ + ‖(L.map f).sum‖ := norm_add_le _ _
      _ ≤ _ := by push_cast; linarith

/-- Sup bound of the Born terms: `‖G_{2ℓ+1}‖_∞ ≤ Cat_ℓ (A/(2η))^{2ℓ+1}`. -/
theorem bornG38_norm_le {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) {A : ℝ}
    (hA : ∀ x, ‖planeReal N z x‖ ≤ A) (ℓ : ℕ) (x : ℝ) :
    ‖bornG38 η N z ℓ x‖ ≤ (catalan ℓ : ℝ) * (A / (2 * η)) ^ (2 * ℓ + 1) := by
  rw [bornG38_eq, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := norm_list_sum_le_length_mul38 (bornTrees38 ℓ) (fun T => T.eval η N z x)
    ((A / (2 * η)) ^ (2 * ℓ + 1)) (fun T hT => by
      obtain ⟨h1, h2, _⟩ := bornTrees38_nodes ℓ T hT
      have := RTree38.sup_le_dsum_zero hη N z hA T h2 x
      rwa [h1] at this)
  rw [bornTrees38_length] at this
  exact this

theorem bornG38_norm_le' {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) {A : ℝ}
    (hA : ∀ x, ‖planeReal N z x‖ ≤ A) (ℓ : ℕ) (x : ℝ) :
    ‖bornG38 η N z ℓ x‖ ≤ (catalan ℓ : ℝ) * A ^ (2 * ℓ + 1) / (2 * η) ^ (2 * ℓ + 1) := by
  have := bornG38_norm_le hη N z hA ℓ x
  rwa [div_pow, ← mul_div_assoc] at this

end NlsGge.SpectralFoundations
end
