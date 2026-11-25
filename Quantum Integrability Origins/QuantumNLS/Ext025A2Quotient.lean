import Mathlib

/-! GP-01: compact group orbit quotients, descended invariants, and phase separation.
The actual orbit/coherent-kernel instantiation remains separately tracked.
No compactness of a full infinite dimensional norm ball is used. -/
set_option autoImplicit false
noncomputable section
open Set Topology InnerProductSpace
namespace QuantumNLS.Ext025A2
section Quotient
variable {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MulAction G X] [ContinuousSMul G X]

/-- A compact group acting on a compact Hausdorff space acts properly. -/
theorem gp01_compact_action_proper : ProperSMul G X := by
  exact ⟨(continuous_smul.prodMk continuous_snd).isProperMap⟩

/-- The common phase quotient is compact Hausdorff whenever the full orbit is. -/
theorem gp01_quotient_compact_hausdorff :
    CompactSpace (Quotient (MulAction.orbitRel G X)) ∧
      T2Space (Quotient (MulAction.orbitRel G X)) := by
  let : ProperSMul G X := gp01_compact_action_proper
  exact ⟨inferInstance, inferInstance⟩

/-- The orbit equivalence relation is closed, with no unproved separation assumption. -/
theorem gp01_orbit_relation_closed :
    IsClosed {p : X × X | (MulAction.orbitRel G X) p.1 p.2} := by
  let : T2Space (Quotient (MulAction.orbitRel G X)) :=
    gp01_quotient_compact_hausdorff.2
  have h := isClosed_eq
    ((continuous_quotient_mk' (s := MulAction.orbitRel G X)).comp continuous_fst)
    ((continuous_quotient_mk' (s := MulAction.orbitRel G X)).comp continuous_snd)
  simpa only [Function.comp_def, Quotient.eq'] using h

omit [TopologicalSpace G] [CompactSpace G] [T2Space X] [ContinuousSMul G X] in
/-- The complex unital conjugation-closed algebra on the actual orbit quotient is dense. -/
theorem gp01_quotient_stone_weierstrass
    (A : StarSubalgebra ℂ C(Quotient (MulAction.orbitRel G X), ℂ))
    (hA : A.SeparatesPoints) : A.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA

/-- Continuous invariant functions descend continuously to the quotient. -/
def gp01_descend (f : C(X, ℂ)) (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    C(Quotient (MulAction.orbitRel G X), ℂ) where
  toFun := Quotient.lift f (by
    intro x y h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
    rw [← hg]
    exact hf g y)
  continuous_toFun := f.continuous.quotient_lift _

omit [TopologicalSpace G] [CompactSpace G] [CompactSpace X] [T2Space X] [ContinuousSMul G X] in
@[simp] theorem gp01_descend_mk (f : C(X, ℂ)) (hf : ∀ (g : G) (x : X), f (g • x) = f x) (x : X) :
    gp01_descend f hf (Quotient.mk (MulAction.orbitRel G X) x) = f x := rfl
end Quotient

/-- Equality of all rank-one quadratic tests separates unit vectors modulo phase.
The single test w=u attains equality in Cauchy--Schwarz. -/
theorem gp01_quadratics_separate_phase {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hq : ∀ w : H, ‖inner ℂ w u‖ ^ 2 = ‖inner ℂ w v‖ ^ 2) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • u := by
  have hun : u ≠ 0 := by intro h; simp [h] at hu
  have hvn : v ≠ 0 := by intro h; simp [h] at hv
  have hii : ‖inner ℂ u u‖ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have he : ‖inner ℂ u v‖ = ‖u‖ * ‖v‖ := by
    have h := hq u
    rw [hii] at h
    rw [hu, hv]
    nlinarith [norm_nonneg (inner ℂ u v)]
  obtain ⟨c, _, hc⟩ := (norm_inner_eq_norm_iff hun hvn).mp he
  refine ⟨c, ?_, hc⟩
  have hh := congrArg norm hc
  simpa [norm_smul, hu, hv] using hh.symm

end QuantumNLS.Ext025A2
#print axioms QuantumNLS.Ext025A2.gp01_compact_action_proper
#print axioms QuantumNLS.Ext025A2.gp01_quotient_compact_hausdorff
#print axioms QuantumNLS.Ext025A2.gp01_orbit_relation_closed
#print axioms QuantumNLS.Ext025A2.gp01_quotient_stone_weierstrass
#print axioms QuantumNLS.Ext025A2.gp01_descend
#print axioms QuantumNLS.Ext025A2.gp01_descend_mk
#print axioms QuantumNLS.Ext025A2.gp01_quadratics_separate_phase
