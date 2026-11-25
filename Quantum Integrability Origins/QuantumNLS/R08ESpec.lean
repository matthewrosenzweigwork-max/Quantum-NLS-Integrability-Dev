import QuantumNLS.CollisionCapacity

/-! integrator-authored trusted spec for R-08EE7BE5 `contact:lem:capacity` (A01.tex:62-75).
E = ⋃ over distinct unordered pairs {i,j} ≠ {k,l} of {x_i = x_j} ∩ {x_k = x_l} ⊆ T_L^N.
(1) There are smooth lattice-periodic η_M with 0 ≤ η_M ≤ 1, η_M ≡ 1 on an open neighbourhood of E,
and ‖η_M‖_{H¹} → 0 (physical H¹ norm). (2) An H⁻¹ distribution (continuous linear functional on
H¹(T_L^N)) supported on E — vanishing on every smooth test whose closed support misses E — is zero. -/

open MeasureTheory
open QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.ProductWeakDerivatives
open QuantumNLS.CollisionIdentification

namespace QuantumNLS.R08ESpec

def specE (L : ℝ) (N : ℕ) : Set (Fin N → AddCircle L) :=
  {y | ∃ i j k l : Fin N, i < j ∧ k < l ∧ (i, j) ≠ (k, l) ∧ y i = y j ∧ y k = y l}

theorem specE_eq (L : ℝ) (N : ℕ) : specE L N = QuantumNLS.CollisionCapacity.coincE L N := by
  ext y
  simp only [specE, QuantumNLS.CollisionCapacity.coincE, QuantumNLS.CollisionCapacity.collSet,
    Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
  constructor
  · rintro ⟨i, j, k, l, hij, hkl, hne, h1, h2⟩
    exact ⟨⟨(i, j), hij⟩, ⟨(k, l), hkl⟩, fun h => hne (congrArg Subtype.val h), h1, h2⟩
  · rintro ⟨p, q, hne, h1, h2⟩
    exact ⟨p.1.1, p.1.2, q.1.1, q.1.2, p.2, q.2, fun h => hne (Subtype.ext h), h1, h2⟩

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ),
    (∃ (η : ℕ → (Fin N → ℝ) → ℂ) (hη : ∀ M, IsTorusTest L (η M)),
      (∀ M x, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ η M x = r) ∧
      (∀ M, 1 ≤ M → ∃ U : Set (Fin N → AddCircle L), IsOpen U ∧ specE L N ⊆ U ∧
        ∀ y ∈ U, liftK (L := L) (η M) y = 1) ∧
      Filter.Tendsto (fun M => ‖smoothH1 (hη M)‖) Filter.atTop (nhds 0)) ∧
    (∀ R : PhysH1 L N →L[ℂ] ℂ,
      (∀ (φ : (Fin N → ℝ) → ℂ), IsTorusTest L φ →
        Disjoint (tsupport (liftK (L := L) φ)) (specE L N) →
        ∀ ψ : PhysH1 L N, (ψ.val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
          liftK (L := L) φ → R ψ = 0) →
      R = 0)

theorem spec : Spec := by
  intro L _ N
  rw [specE_eq]
  refine ⟨QuantumNLS.CollisionCapacity.exists_capacity_cutoffs, fun R hR => ?_⟩
  apply QuantumNLS.CollisionCapacity.eq_zero_of_supportedOnE
  intro φ hφ hd
  refine hR φ hφ hd _ ?_
  rw [smoothH1_val]
  exact MemLp.coeFn_toLp _

end QuantumNLS.R08ESpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R08ESpec.spec
  IO.println s!"R08ESpec.spec axioms: {ax}"
