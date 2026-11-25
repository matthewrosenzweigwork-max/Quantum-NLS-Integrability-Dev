import NlsGge.Spectral.RTreeCore38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # RTree piece T5: one expansion step `R h = h/2η − R(h′)/2η` on trees

At the root of a tree whose root kind is `R`, the step replaces the root by `S` and produces the
single-leaf bumps of the whole tree (each with root kind `R`, i.e. `R (∂ᵢ g)`, the summands of
`R (g′)`). If the root kind is `S`, the step recurses into a child that still contains an `R` node.
The weight / derivative bookkeeping is the conjunction of the counter equalities. -/

/-- one-step expansion of the resolvent in terms of a derivative witness of its output
(`L4`, `resolv38_expand38`, with the derivative of `R g` identified from the ODE). -/
theorem resolv38_eq_of_hasDerivAt38 {η : ℝ} (hη : 0 < η) {g s : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) (hs : ∀ x, HasDerivAt (resolv38 η g) (s x) x) (x : ℝ) :
    resolv38 η g x = g x / (2 * (η : ℂ)) - s x / (2 * (η : ℂ)) := by
  have h1 := (hs x).unique (resolv38_hasDerivAt_periodic38 hη hg hp x)
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  rw [h1]
  field_simp
  ring

/-- root kind `R` case: `eval T = eval (T with root kind S) − (2η)⁻¹ · Σ eval (bumps T)` -/
theorem RTree38.eval_root_R_expand {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N)
    (d : ℕ) (x : ℝ) :
    (RTree38.base RKind38.R d).eval η N z x =
      (RTree38.base RKind38.S d).eval η N z x -
        (2 * (η : ℂ))⁻¹ * (((RTree38.base RKind38.R d).bumps).map
          (fun T' => T'.eval η N z x)).sum := by
  have h := (RTree38.base RKind38.R d).perC1 hη N z
  have hc := perC1_leafUbar38 N z d
  have := resolv38_eq_of_hasDerivAt38 hη hc.cont hc.per
    (s := fun x => (((RTree38.base RKind38.R d).bumps).map (fun T' => T'.eval η N z x)).sum)
    (fun y => by simpa only [RTree38.eval, RKind38.act] using h.deriv y) x
  simp only [RTree38.eval, RKind38.act] at this ⊢
  rw [this]
  simp only [div_eq_mul_inv]
  ring

theorem RTree38.eval_node_root_R_expand {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N)
    (d : ℕ) (A B : RTree38) (x : ℝ) :
    (RTree38.node RKind38.R d A B).eval η N z x =
      (RTree38.node RKind38.S d A B).eval η N z x -
        (2 * (η : ℂ))⁻¹ * (((RTree38.node RKind38.R d A B).bumps).map
          (fun T' => T'.eval η N z x)).sum := by
  have h := (RTree38.node RKind38.R d A B).perC1 hη N z
  have hU := perC1_leafU38 N z d
  have hA := RTree38.eval_cont_per hη N z A
  have hB := RTree38.eval_cont_per hη N z B
  have hg : Continuous (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) :=
    (hU.cont.mul hA.1).mul hB.1
  have hgp : Function.Periodic
      (fun y => leafU38 N z d y * A.eval η N z y * B.eval η N z y) 1 :=
    fun y => by simp only [hU.per y, hA.2 y, hB.2 y]
  have := resolv38_eq_of_hasDerivAt38 hη hg hgp
    (s := fun x => (((RTree38.node RKind38.R d A B).bumps).map
      (fun T' => T'.eval η N z x)).sum)
    (fun y => by simpa only [RTree38.eval, RKind38.act] using h.deriv y) x
  simp only [RTree38.eval, RKind38.act] at this ⊢
  rw [this]
  simp only [div_eq_mul_inv]
  ring

/-- numR of a tree with root kind `S` -/
theorem RTree38.numR_node_S (d : ℕ) (A B : RTree38) :
    (RTree38.node RKind38.S d A B).numR = A.numR + B.numR := by
  simp [RTree38.numR]

/-- T5: one expansion step.  The statement of `R3C_GENERAL_K_DESIGN.md` (b) verbatim, apart from
the explicit cast of `(2*η)⁻¹` to `ℂ`. -/
theorem RTree38.expand_step {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (T : RTree38)
    (hR : 0 < T.numR) :
    ∃ (T₁ : RTree38) (Ts : List RTree38),
      T₁.numR + 1 = T.numR ∧ T₁.nodes = T.nodes ∧ T₁.dsum = T.dsum ∧
      (∀ T' ∈ Ts, T'.numR = T.numR ∧ T'.nodes = T.nodes ∧ T'.dsum = T.dsum + 1) ∧
      Ts.length ≤ T.nodes ∧
      ∀ x, T.eval η N z x = T₁.eval η N z x - (2*η)⁻¹ * (Ts.map (fun T' => T'.eval η N z x)).sum := by
  induction T with
  | base κ d =>
    cases κ with
    | S => simp [RTree38.numR] at hR
    | R =>
      refine ⟨.base .S d, (RTree38.base .R d).bumps, by simp [RTree38.numR],
        by simp [RTree38.nodes], by simp [RTree38.dsum], ?_, by simp [RTree38.length_bumps],
        fun x => ?_⟩
      · intro T' hT'
        exact ⟨RTree38.numR_of_mem_bumps _ T' hT', RTree38.nodes_of_mem_bumps _ T' hT',
          RTree38.dsum_of_mem_bumps _ T' hT'⟩
      · have := RTree38.eval_root_R_expand hη N z d x
        push_cast
        exact this
  | node κ d A B ihA ihB =>
    cases κ with
    | R =>
      refine ⟨.node .S d A B, (RTree38.node .R d A B).bumps, ?_, by simp [RTree38.nodes],
        by simp [RTree38.dsum], ?_, by simp [RTree38.length_bumps], fun x => ?_⟩
      · simp [RTree38.numR]; omega
      · intro T' hT'
        exact ⟨RTree38.numR_of_mem_bumps _ T' hT', RTree38.nodes_of_mem_bumps _ T' hT',
          RTree38.dsum_of_mem_bumps _ T' hT'⟩
      · have := RTree38.eval_node_root_R_expand hη N z d A B x
        push_cast
        exact this
    | S =>
      rw [RTree38.numR_node_S] at hR
      by_cases hA : 0 < A.numR
      · obtain ⟨A₁, As, h1, h2, h3, h4, h5, h6⟩ := ihA hA
        refine ⟨.node .S d A₁ B, As.map (fun A' => .node .S d A' B), ?_, ?_, ?_, ?_, ?_, fun x => ?_⟩
        · simp only [RTree38.numR_node_S]; omega
        · simp only [RTree38.nodes]; omega
        · simp only [RTree38.dsum]; omega
        · intro T' hT'
          obtain ⟨A', hA', rfl⟩ := List.mem_map.mp hT'
          obtain ⟨a1, a2, a3⟩ := h4 A' hA'
          refine ⟨?_, ?_, ?_⟩
          · simp only [RTree38.numR_node_S]; omega
          · simp only [RTree38.nodes]; omega
          · simp only [RTree38.dsum]; omega
        · simp only [List.length_map, RTree38.nodes]
          have := RTree38.nodes_pos B
          omega
        · have hx := h6 x
          have key : ∀ (l : List RTree38) (c b e : ℂ),
              (l.map (fun A' => c * A'.eval η N z x * b / e)).sum =
                c * b / e * (l.map (fun A' => A'.eval η N z x)).sum := by
            intro l c b e
            induction l with
            | nil => simp
            | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
          simp only [RTree38.eval, RKind38.act, List.map_map, Function.comp_def, key]
          rw [hx]
          push_cast
          ring
      · have hB : 0 < B.numR := by omega
        obtain ⟨B₁, Bs, h1, h2, h3, h4, h5, h6⟩ := ihB hB
        refine ⟨.node .S d A B₁, Bs.map (fun B' => .node .S d A B'), ?_, ?_, ?_, ?_, ?_, fun x => ?_⟩
        · simp only [RTree38.numR_node_S]; omega
        · simp only [RTree38.nodes]; omega
        · simp only [RTree38.dsum]; omega
        · intro T' hT'
          obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hT'
          obtain ⟨a1, a2, a3⟩ := h4 B' hB'
          refine ⟨?_, ?_, ?_⟩
          · simp only [RTree38.numR_node_S]; omega
          · simp only [RTree38.nodes]; omega
          · simp only [RTree38.dsum]; omega
        · simp only [List.length_map, RTree38.nodes]
          have := RTree38.nodes_pos A
          omega
        · have hx := h6 x
          have key : ∀ (l : List RTree38) (c a e : ℂ),
              (l.map (fun B' => c * a * B'.eval η N z x / e)).sum =
                c * a / e * (l.map (fun B' => B'.eval η N z x)).sum := by
            intro l c a e
            induction l with
            | nil => simp
            | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
          simp only [RTree38.eval, RKind38.act, List.map_map, Function.comp_def, key]
          rw [hx]
          push_cast
          ring

end NlsGge.SpectralFoundations
end
