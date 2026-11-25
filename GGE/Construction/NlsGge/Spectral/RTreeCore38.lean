import NlsGge.Spectral.R3cResolventCore38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # RTree piece T1: resolvent trees, evaluation, counters, bumps, and `perC1`

Fixed-arity resolvent trees for the general-`k` R3c argument (design
`R3C_GENERAL_K_DESIGN.md`, sections (b) and (d)). Leaf derivative orders are stored in the nodes.
The Leibniz derivative of a tree evaluation is the sum of the evaluations of its single-leaf
bumps (`RTree38.perC1`). -/

/-- node kinds: `R` = resolvent `(∂+2η)⁻¹`, `S` = scalar `1/(2η)` -/
inductive RKind38 | R | S
deriving DecidableEq

/-- fixed-arity resolvent trees; leaf derivative orders are stored in the nodes -/
inductive RTree38
  | base (κ : RKind38) (d : ℕ) : RTree38
  | node (κ : RKind38) (d : ℕ) (A B : RTree38) : RTree38
deriving DecidableEq

namespace RTree38

/-- number of `κ`-nodes (= number of leaves inside) -/
def nodes : RTree38 → ℕ
  | base _ _ => 1
  | node _ _ A B => 1 + nodes A + nodes B

/-- number of `R` nodes -/
def numR : RTree38 → ℕ
  | base κ _ => if κ = RKind38.R then 1 else 0
  | node κ _ A B => (if κ = RKind38.R then 1 else 0) + numR A + numR B

/-- sum of the leaf orders -/
def dsum : RTree38 → ℕ
  | base _ d => d
  | node _ d A B => d + dsum A + dsum B

/-- maximal leaf order -/
def maxd : RTree38 → ℕ
  | base _ d => d
  | node _ d A B => max d (max (maxd A) (maxd B))

/-- number of leaves of order exactly `k` -/
def cntEq (k : ℕ) : RTree38 → ℕ
  | base _ d => if d = k then 1 else 0
  | node _ d A B => (if d = k then 1 else 0) + cntEq k A + cntEq k B

/-- Leibniz: the list of single-leaf bumps -/
def bumps : RTree38 → List RTree38
  | base κ d => [base κ (d+1)]
  | node κ d A B =>
      node κ (d+1) A B :: ((bumps A).map (node κ d · B) ++ (bumps B).map (node κ d A ·))

end RTree38

/-- leaf functions for a plane -/
def leafU38 (N : ℕ) (z : FourierPlane N) (d : ℕ) : ℝ → ℂ :=
  planeReal N ((derivativePlane N)^[d] z)

def leafUbar38 (N : ℕ) (z : FourierPlane N) (d : ℕ) : ℝ → ℂ :=
  fun x => star (leafU38 N z d x)

def RKind38.act (η : ℝ) : RKind38 → (ℝ → ℂ) → ℝ → ℂ
  | .R, h => resolv38 η h
  | .S, h => fun x => h x / (2 * η)

def RTree38.eval (η : ℝ) (N : ℕ) (z : FourierPlane N) : RTree38 → ℝ → ℂ
  | .base κ d => κ.act η (leafUbar38 N z d)
  | .node κ d A B => κ.act η (fun x => leafU38 N z d x * A.eval η N z x * B.eval η N z x)

/-- a term `c (2η)^{-e} ∫ ∂^{d₀}U · eval T` -/
structure RTerm38 where
  c : ℂ
  e : ℕ
  d0 : ℕ
  T : RTree38

def RTerm38.val (η : ℝ) (N : ℕ) (z : FourierPlane N) (t : RTerm38) : ℂ :=
  t.c * ((2 * η : ℂ))⁻¹ ^ t.e * pair38 (leafU38 N z t.d0) (t.T.eval η N z)

def RTerm38.weight (t : RTerm38) : ℕ := t.T.nodes + t.e

/-! ## Leaves -/

theorem perC1_leafU38 (N : ℕ) (z : FourierPlane N) (d : ℕ) :
    PerC1_38 (leafU38 N z d) (leafU38 N z (d + 1)) := by
  have h := perC1_plane38 N ((derivativePlane N)^[d] z)
  unfold leafU38
  rw [Function.iterate_succ_apply']
  exact h

theorem perC1_leafUbar38 (N : ℕ) (z : FourierPlane N) (d : ℕ) :
    PerC1_38 (leafUbar38 N z d) (leafUbar38 N z (d + 1)) :=
  (perC1_leafU38 N z d).star

/-! ## Linearity of the node actions on continuous periodic functions -/

theorem resolv38_cont_per38 {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) :
    Continuous (resolv38 η g) := by
  obtain ⟨x₀, hx₀⟩ := periodic_norm_attains38 hg hp
  exact continuous_iff_continuousAt.mpr fun x => (resolv38_hasDerivAt hη hg hx₀ x).continuousAt

theorem resolv38_add_cp38 {η : ℝ} (hη : 0 < η) {f g : ℝ → ℂ} (hf : Continuous f)
    (hfp : Function.Periodic f 1) (hg : Continuous g) (hgp : Function.Periodic g 1) (x : ℝ) :
    resolv38 η (fun y => f y + g y) x = resolv38 η f x + resolv38 η g x := by
  obtain ⟨x1, h1⟩ := periodic_norm_attains38 hf hfp
  obtain ⟨x2, h2⟩ := periodic_norm_attains38 hg hgp
  unfold resolv38
  rw [← smul_add, ← integral_add (resInt38_integrableOn hη hf h1 x)
    (resInt38_integrableOn hη hg h2 x)]
  congr 2
  funext t
  unfold resInt38
  rw [smul_add]

theorem resolv38_zero_fun38 (η : ℝ) (x : ℝ) : resolv38 η (fun _ => (0 : ℂ)) x = 0 := by
  unfold resolv38 resInt38
  simp

theorem RKind38.perC1_act {η : ℝ} (hη : 0 < η) (κ : RKind38) {g g' : ℝ → ℂ}
    (h : PerC1_38 g g') : PerC1_38 (κ.act η g) (κ.act η g') := by
  cases κ with
  | R => exact perC1_resolv38 hη h
  | S =>
    exact
      { cont := h.cont.div_const _
        cont' := h.cont'.div_const _
        per := fun y => by simp only [RKind38.act, h.per y]
        per' := fun y => by simp only [RKind38.act, h.per' y]
        deriv := fun x => (h.deriv x).div_const _ }

theorem RKind38.act_cont_per {η : ℝ} (hη : 0 < η) (κ : RKind38) {g : ℝ → ℂ}
    (hg : Continuous g) (hp : Function.Periodic g 1) :
    Continuous (κ.act η g) ∧ Function.Periodic (κ.act η g) 1 := by
  cases κ with
  | R => exact ⟨resolv38_cont_per38 hη hg hp, resolv38_periodic hp⟩
  | S =>
    exact ⟨hg.div_const _, fun y => by simp only [RKind38.act, hp y]⟩

theorem RKind38.act_add {η : ℝ} (hη : 0 < η) (κ : RKind38) {f g : ℝ → ℂ} (hf : Continuous f)
    (hfp : Function.Periodic f 1) (hg : Continuous g) (hgp : Function.Periodic g 1) (x : ℝ) :
    κ.act η (fun y => f y + g y) x = κ.act η f x + κ.act η g x := by
  cases κ with
  | R => exact resolv38_add_cp38 hη hf hfp hg hgp x
  | S => simp only [RKind38.act, add_div]

theorem RKind38.act_zero (η : ℝ) (κ : RKind38) (x : ℝ) : κ.act η (fun _ => (0 : ℂ)) x = 0 := by
  cases κ with
  | R => exact resolv38_zero_fun38 η x
  | S => simp [RKind38.act]

theorem list_sum_cont_per38 {ι : Type*} (L : List ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ L, Continuous (F i) ∧ Function.Periodic (F i) 1) :
    Continuous (fun y => (L.map (fun i => F i y)).sum) ∧
      Function.Periodic (fun y => (L.map (fun i => F i y)).sum) 1 := by
  induction L with
  | nil => exact ⟨continuous_const, fun y => by simp⟩
  | cons a L ih =>
    have h1 := hF a (by simp)
    have h2 := ih (fun i hi => hF i (by simp [hi]))
    refine ⟨?_, fun y => ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact h1.1.add h2.1
    · simp only [List.map_cons, List.sum_cons]
      rw [h1.2 y]
      have := h2.2 y
      simp only at this
      rw [this]

theorem RKind38.act_list_sum {η : ℝ} (hη : 0 < η) (κ : RKind38) {ι : Type*} (L : List ι)
    (F : ι → ℝ → ℂ) (hF : ∀ i ∈ L, Continuous (F i) ∧ Function.Periodic (F i) 1) (x : ℝ) :
    κ.act η (fun y => (L.map (fun i => F i y)).sum) x =
      (L.map (fun i => κ.act η (F i) x)).sum := by
  induction L with
  | nil => simpa using RKind38.act_zero η κ x
  | cons a L ih =>
    have h1 := hF a (by simp)
    have h2 := list_sum_cont_per38 L F (fun i hi => hF i (by simp [hi]))
    have := RKind38.act_add hη κ h1.1 h1.2 h2.1 h2.2 x
    simp only [List.map_cons, List.sum_cons]
    rw [this, ih (fun i hi => hF i (by simp [hi]))]

/-! ## Evaluation is continuous and periodic -/

theorem RTree38.eval_cont_per {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) :
    ∀ T : RTree38, Continuous (T.eval η N z) ∧ Function.Periodic (T.eval η N z) 1
  | .base κ d => by
    have h := perC1_leafUbar38 N z d
    exact RKind38.act_cont_per hη κ h.cont h.per
  | .node κ d A B => by
    have hU := perC1_leafU38 N z d
    have hA := RTree38.eval_cont_per hη N z A
    have hB := RTree38.eval_cont_per hη N z B
    exact RKind38.act_cont_per hη κ ((hU.cont.mul hA.1).mul hB.1)
      (fun y => by simp only [hU.per y, hA.2 y, hB.2 y])

/-! ## `perC1` : Leibniz derivative of a tree through `R` and `S` -/

theorem RTree38.perC1 {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (T : RTree38) :
    PerC1_38 (T.eval η N z) (fun x => ((T.bumps).map (fun T' => T'.eval η N z x)).sum) := by
  induction T with
  | base κ d =>
    have h := RKind38.perC1_act hη κ (perC1_leafUbar38 N z d)
    simpa [RTree38.bumps, RTree38.eval] using h
  | node κ d A B ihA ihB =>
    have hU := perC1_leafU38 N z d
    have hg := (hU.mul ihA).mul ihB
    have h := RKind38.perC1_act hη κ hg
    have hAc := RTree38.eval_cont_per hη N z A
    have hBc := RTree38.eval_cont_per hη N z B
    have hUc : Continuous (leafU38 N z d) ∧ Function.Periodic (leafU38 N z d) 1 :=
      ⟨hU.cont, hU.per⟩
    have hU'c : Continuous (leafU38 N z (d+1)) ∧ Function.Periodic (leafU38 N z (d+1)) 1 :=
      ⟨(perC1_leafU38 N z (d+1)).cont, (perC1_leafU38 N z (d+1)).per⟩
    have e1 : ∀ x, (((RTree38.node κ d A B).bumps).map
        (fun T' => T'.eval η N z x)).sum =
        κ.act η (fun y => leafU38 N z (d+1) y * A.eval η N z y * B.eval η N z y) x +
        (κ.act η (fun y => ((A.bumps).map (fun T =>
          leafU38 N z d y * T.eval η N z y * B.eval η N z y)).sum) x +
         κ.act η (fun y => ((B.bumps).map (fun T =>
          leafU38 N z d y * A.eval η N z y * T.eval η N z y)).sum) x) := by
      intro x
      rw [RKind38.act_list_sum hη κ A.bumps
          (fun T y => leafU38 N z d y * T.eval η N z y * B.eval η N z y)
          (fun T _ => ⟨(hUc.1.mul (RTree38.eval_cont_per hη N z T).1).mul hBc.1,
            fun y => by
              simp only [hUc.2 y, (RTree38.eval_cont_per hη N z T).2 y, hBc.2 y]⟩) x,
        RKind38.act_list_sum hη κ B.bumps
          (fun T y => leafU38 N z d y * A.eval η N z y * T.eval η N z y)
          (fun T _ => ⟨(hUc.1.mul hAc.1).mul (RTree38.eval_cont_per hη N z T).1,
            fun y => by
              simp only [hUc.2 y, hAc.2 y, (RTree38.eval_cont_per hη N z T).2 y]⟩) x]
      simp only [RTree38.bumps, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, RTree38.eval]
    have e2 : (fun x => (((RTree38.node κ d A B).bumps).map
        (fun T' => T'.eval η N z x)).sum) = κ.act η (fun y =>
        (leafU38 N z (d+1) y * A.eval η N z y +
          leafU38 N z d y * ((A.bumps).map (fun T' => T'.eval η N z y)).sum) *
            B.eval η N z y +
          leafU38 N z d y * A.eval η N z y * ((B.bumps).map (fun T' => T'.eval η N z y)).sum) := by
      funext x
      rw [e1 x]
      have hs1 := list_sum_cont_per38 A.bumps
        (fun T y => leafU38 N z d y * T.eval η N z y * B.eval η N z y)
        (fun T _ => ⟨(hUc.1.mul (RTree38.eval_cont_per hη N z T).1).mul hBc.1,
            fun y => by
              simp only [hUc.2 y, (RTree38.eval_cont_per hη N z T).2 y, hBc.2 y]⟩)
      have hs2 := list_sum_cont_per38 B.bumps
        (fun T y => leafU38 N z d y * A.eval η N z y * T.eval η N z y)
        (fun T _ => ⟨(hUc.1.mul hAc.1).mul (RTree38.eval_cont_per hη N z T).1,
            fun y => by
              simp only [hUc.2 y, hAc.2 y, (RTree38.eval_cont_per hη N z T).2 y]⟩)
      have hg1 : Continuous (fun y => leafU38 N z (d+1) y * A.eval η N z y * B.eval η N z y) :=
        (hU'c.1.mul hAc.1).mul hBc.1
      have hg1p : Function.Periodic
          (fun y => leafU38 N z (d+1) y * A.eval η N z y * B.eval η N z y) 1 :=
        fun y => by simp only [hU'c.2 y, hAc.2 y, hBc.2 y]
      have hs12c : Continuous (fun y =>
          ((A.bumps).map (fun T => leafU38 N z d y * T.eval η N z y * B.eval η N z y)).sum +
          ((B.bumps).map (fun T => leafU38 N z d y * A.eval η N z y * T.eval η N z y)).sum) :=
        hs1.1.add hs2.1
      rw [← RKind38.act_add hη κ hs1.1 hs1.2 hs2.1 hs2.2 x,
        ← RKind38.act_add hη κ hg1 hg1p hs12c
          (fun y => by simp only [hs1.2 y, hs2.2 y]) x]
      congr 1
      funext y
      simp only [List.sum_map_mul_left, List.sum_map_mul_right, add_mul, mul_assoc]
      ring
    simp only [RTree38.eval] at h ⊢
    rw [e2]
    exact h

/-! ## Counter lemmas for bumps -/

theorem RTree38.nodes_pos : ∀ T : RTree38, 1 ≤ T.nodes
  | .base _ _ => le_refl _
  | .node _ _ A B => by simp only [RTree38.nodes]; omega

theorem RTree38.length_bumps : ∀ T : RTree38, T.bumps.length = T.nodes
  | .base _ _ => rfl
  | .node _ _ A B => by
    simp only [RTree38.bumps, RTree38.nodes, List.length_cons, List.length_append,
      List.length_map, RTree38.length_bumps A, RTree38.length_bumps B]
    omega

theorem RTree38.mem_bumps_node {κ : RKind38} {d : ℕ} {A B T' : RTree38} :
    T' ∈ (RTree38.node κ d A B).bumps ↔
      T' = RTree38.node κ (d+1) A B ∨ (∃ A' ∈ A.bumps, T' = RTree38.node κ d A' B) ∨
        ∃ B' ∈ B.bumps, T' = RTree38.node κ d A B' := by
  simp only [RTree38.bumps, List.mem_cons, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨A', hA', h.symm⟩)
    · exact Or.inr (Or.inr ⟨B', hB', h.symm⟩)
  · rintro (h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨A', hA', h.symm⟩)
    · exact Or.inr (Or.inr ⟨B', hB', h.symm⟩)

theorem RTree38.nodes_of_mem_bumps : ∀ (T : RTree38), ∀ T' ∈ T.bumps, T'.nodes = T.nodes
  | .base _ _, T', h => by
    simp only [RTree38.bumps, List.mem_singleton] at h
    subst h; rfl
  | .node κ d A B, T', h => by
    rcases RTree38.mem_bumps_node.mp h with h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩
    · subst h; rfl
    · subst h
      simp only [RTree38.nodes, RTree38.nodes_of_mem_bumps A A' hA']
    · subst h
      simp only [RTree38.nodes, RTree38.nodes_of_mem_bumps B B' hB']

theorem RTree38.numR_of_mem_bumps : ∀ (T : RTree38), ∀ T' ∈ T.bumps, T'.numR = T.numR
  | .base _ _, T', h => by
    simp only [RTree38.bumps, List.mem_singleton] at h
    subst h; rfl
  | .node κ d A B, T', h => by
    rcases RTree38.mem_bumps_node.mp h with h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩
    · subst h; rfl
    · subst h
      simp only [RTree38.numR, RTree38.numR_of_mem_bumps A A' hA']
    · subst h
      simp only [RTree38.numR, RTree38.numR_of_mem_bumps B B' hB']

theorem RTree38.dsum_of_mem_bumps : ∀ (T : RTree38), ∀ T' ∈ T.bumps, T'.dsum = T.dsum + 1
  | .base _ _, T', h => by
    simp only [RTree38.bumps, List.mem_singleton] at h
    subst h; rfl
  | .node κ d A B, T', h => by
    rcases RTree38.mem_bumps_node.mp h with h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩
    · subst h; simp only [RTree38.dsum]; omega
    · subst h
      simp only [RTree38.dsum, RTree38.dsum_of_mem_bumps A A' hA']
      omega
    · subst h
      simp only [RTree38.dsum, RTree38.dsum_of_mem_bumps B B' hB']
      omega

theorem RTree38.maxd_of_mem_bumps_le : ∀ (T : RTree38), ∀ T' ∈ T.bumps, T'.maxd ≤ T.maxd + 1
  | .base _ _, T', h => by
    simp only [RTree38.bumps, List.mem_singleton] at h
    subst h; rfl
  | .node κ d A B, T', h => by
    rcases RTree38.mem_bumps_node.mp h with h | ⟨A', hA', h⟩ | ⟨B', hB', h⟩
    · subst h; simp only [RTree38.maxd]; omega
    · subst h
      have := RTree38.maxd_of_mem_bumps_le A A' hA'
      simp only [RTree38.maxd]; omega
    · subst h
      have := RTree38.maxd_of_mem_bumps_le B B' hB'
      simp only [RTree38.maxd]; omega

/-! ## Leaf norms used by the norm bounds (piece T3) -/

/-- sup norm of the `d`-th leaf (totalized `iSup`; bounded by `norm_leafU38_le_leafSup38`) -/
def leafSup38 (N : ℕ) (z : FourierPlane N) (d : ℕ) : ℝ := ⨆ x : ℝ, ‖leafU38 N z d x‖

/-- `L²(0,1)` norm of the `d`-th leaf -/
def leafL2_38 (N : ℕ) (z : FourierPlane N) (d : ℕ) : ℝ := Real.sqrt (l2sq38 (leafU38 N z d))

/-- the leaf factor: `L²` norm at order `k`, sup norm otherwise -/
def leafFactor38 (k : ℕ) (N : ℕ) (z : FourierPlane N) (d : ℕ) : ℝ :=
  if d = k then leafL2_38 N z d else leafSup38 N z d

/-- `b_k(T)`: product over the leaves of `leafFactor38` -/
def RTree38.leafBound (k : ℕ) (N : ℕ) (z : FourierPlane N) : RTree38 → ℝ
  | .base _ d => leafFactor38 k N z d
  | .node _ d A B => leafFactor38 k N z d * A.leafBound k N z * B.leafBound k N z

theorem norm_leafU38_le_leafSup38 (N : ℕ) (z : FourierPlane N) (d : ℕ) (x : ℝ) :
    ‖leafU38 N z d x‖ ≤ leafSup38 N z d := by
  have h := perC1_leafU38 N z d
  obtain ⟨x₀, hx₀⟩ := periodic_norm_attains38 h.cont h.per
  exact le_ciSup (⟨‖leafU38 N z d x₀‖, by rintro _ ⟨y, rfl⟩; exact hx₀ y⟩ :
    BddAbove (Set.range fun x : ℝ => ‖leafU38 N z d x‖)) x

theorem leafSup38_nonneg (N : ℕ) (z : FourierPlane N) (d : ℕ) : 0 ≤ leafSup38 N z d :=
  (norm_nonneg _).trans (norm_leafU38_le_leafSup38 N z d 0)

theorem leafFactor38_nonneg (k : ℕ) (N : ℕ) (z : FourierPlane N) (d : ℕ) :
    0 ≤ leafFactor38 k N z d := by
  unfold leafFactor38
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact leafSup38_nonneg N z d

theorem RTree38.leafBound_nonneg (k : ℕ) (N : ℕ) (z : FourierPlane N) :
    ∀ T : RTree38, 0 ≤ T.leafBound k N z
  | .base _ d => leafFactor38_nonneg k N z d
  | .node _ d A B =>
    mul_nonneg (mul_nonneg (leafFactor38_nonneg k N z d) (RTree38.leafBound_nonneg k N z A))
      (RTree38.leafBound_nonneg k N z B)

end NlsGge.SpectralFoundations
end
