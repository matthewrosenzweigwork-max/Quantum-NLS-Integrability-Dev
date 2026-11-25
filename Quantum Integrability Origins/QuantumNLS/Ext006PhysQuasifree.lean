import QuantumNLS.Ext006PhysSymplectic
import QuantumNLS.Ext006PhysFockCoord
import QuantumNLS.Ext006QuasifreeWeak

/-! PROP-023 physical-form interface, stage 3: "pure quasifree" in the source's physical form
implies the formal `Ext006QuasifreeWeak.PureQuasifree` predicate.

Source (fluctuations.tex, Lemma `Q7B:lem:pair`): `S(t,s) v = α v + β v̄` is the symplectic
isomorphism given by the real-linear variational flow; the unitary propagator `𝕍(t,s)` of the
quadratic Hamiltonian implements it, i.e. on the physical Fock space the Heisenberg fields
`𝕍* a_j 𝕍` solve the linearized equation `i ∂_t v = a v + b v̄` with `a`, `a*` playing `v`, `v̄`:

  `𝕍* a_d 𝕍 = Σ_c α'_{dc} a_c + β'_{dc} a_c^*`  and its adjoint  `𝕍* a_d^* 𝕍 = Σ_c ᾱ'_{dc} a_c^* + β̄'_{dc} a_c`,

with `(α', β') = (α, β)` the blocks of `S`, and `ξ = 𝕍 Ω` is "pure quasifree".

`PhysicalQuasifreeSource x` states exactly this on the repository's physical Fock space
(`Ext025B3PhysicalSectors.Fock L`), the repository's creation/annihilation objects
(`Occupation.Cre/Ann/ket` transported by `Ext006PhysFockCoord.physCore`), in the weak
matrix-element form between core vectors (no operator domains):
`HeisAnn`:  `⟨Ψ(Cre_d n), 𝕍 Ψ(m)⟩ = (α' u)_d + (β' w)_d`,
`HeisCre`:  `⟨Ψ(Ann_d n), 𝕍 Ψ(m)⟩ = (ᾱ' w)_d + (β̄' u)_d`,
where `u_c = ⟨Ψ(n), 𝕍 Ψ(Ann_c m)⟩`, `w_c = ⟨Ψ(n), 𝕍 Ψ(Cre_c m)⟩` (`⟨Ψ(n), a_d^{(*)}𝕍Ψ(m)⟩` is
moved onto the core vector, `⟨Ψ(n), 𝕍 a_c^{(*)}Ψ(m)⟩` is a matrix element of `𝕍` between core
vectors).  `PhysSymplectic` is the symplecticity of `S` (preserves `Im⟨·,·⟩`, bijective).

`physical_implies_pureQuasifree`: this implies `PureQuasifree (coefficient x)` by the inverse pair
`(α, β) = (α'†, -β'ᵀ)` (`Ext006PhysSymplectic`) and the transport `Ṽ = Φ 𝕍 Φ⁻¹` to occupation
coordinates (`Ext006PhysFockCoord.Phi`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006PhysQuasifree
open Occupation OccupationHilbert Ext006PhysFockCoord Ext006PhysSymplectic Ext006BogoliubovAlg
  Ext006QuasifreeWeak Ext006PhysicalVacuum
open scoped ComplexConjugate InnerProductSpace
variable {L : ℝ} [Fact (0 < L)]

/-- Weak form of `𝕍* a_d 𝕍 = Σ_c α'_{dc} a_c + β'_{dc} a_c^*`. -/
def HeisAnn (𝕍 : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) : Prop :=
  ∀ (d : ℤ) (n m : Occ) (u w : H),
    (∀ c, u c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Ann c (ket m))))) →
    (∀ c, w c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Cre c (ket m))))) →
    inner ℂ (physCore (L := L) (Cre d (ket n))) (𝕍 (physCore (ket m))) = (A u) d + (B w) d

/-- Weak form of the adjoint relation `𝕍* a_d^* 𝕍 = Σ_c conj α'_{dc} a_c^* + conj β'_{dc} a_c`
(`Ā = conj ∘ A ∘ conj` is the entrywise conjugate matrix). -/
def HeisCre (𝕍 : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) : Prop :=
  ∀ (d : ℤ) (n m : Occ) (u w : H),
    (∀ c, u c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Ann c (ket m))))) →
    (∀ c, w c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Cre c (ket m))))) →
    inner ℂ (physCore (L := L) (Ann d (ket n))) (𝕍 (physCore (ket m))) =
      (bar A w) d + (bar B u) d

/-- **A pure quasifree vacuum in the source's physical form**: `x = 𝕍 Ω` where `𝕍` is a unitary of
the physical Fock space whose Heisenberg action on the creation/annihilation operators is the
Bogoliubov map of the symplectic isomorphism `S = (α', β')`. -/
def PhysicalQuasifreeSource (x : Ext025B3PhysicalSectors.Fock L) : Prop :=
  ∃ (𝕍 : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L) (A B : H →L[ℂ] H),
    PhysSymplectic A B ∧ HeisAnn 𝕍 A B ∧ HeisCre 𝕍 A B ∧ x = 𝕍 (vac (L := L))

/-! ### Transport to occupation coordinates -/

variable (𝕍 : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)

/-- `Ṽ = Φ 𝕍 Φ⁻¹` on `ℓ²(Occ)`. -/
def Vtil : L2 Occ ≃ₗᵢ[ℂ] L2 Occ := ((Phi (L := L)).symm.trans 𝕍).trans Phi

lemma Vtil_apply (w : L2 Occ) : Vtil 𝕍 w = Phi (𝕍 ((Phi (L := L)).symm w)) := rfl

lemma Vtil_single_apply (k n : Occ) :
    (Vtil 𝕍 (lp.single 2 k (1 : ℂ))) n =
      inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (ket k))) := by
  rw [Vtil_apply, Phi_apply, ← physCore_ket, inner_physCore_ket]

lemma ME_conj (n k : Occ) :
    inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (ket k))) =
      conj (Phi (𝕍.symm (physCore (ket n))) k) := by
  have h := 𝕍.inner_map_map (𝕍.symm (physCore (L := L) (ket n))) (physCore (ket k))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h, ← inner_conj_symm, inner_physCore_ket]
  rfl

/-- The vector `z = Φ 𝕍⁻¹ Ψ(n)` whose conjugate coordinates are the `n`-th row of `𝕍`. -/
def zvec (n : Occ) : L2 Occ := Phi (𝕍.symm (physCore (L := L) (ket n)))

/-- `u_c = ⟨Ψ(n), 𝕍 Ψ(Ann_c m)⟩` as an element of `ℓ²(ℤ)`. -/
def uvec (n m : Occ) : H := star (yvec (zvec 𝕍 n) m)

/-- `w_c = ⟨Ψ(n), 𝕍 Ψ(Cre_c m)⟩` as an element of `ℓ²(ℤ)`. -/
def wvec (n m : Occ) : H := star (xvec (zvec 𝕍 n) m)

lemma inner_Ann_core (n m : Occ) (c : ℤ) :
    inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Ann c (ket m)))) =
      (Real.sqrt (m c : ℝ) : ℂ) * inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (ket (m - e c)))) := by
  rw [Ann_ket, map_smul, map_smul, inner_smul_right]

lemma inner_Cre_core (n m : Occ) (c : ℤ) :
    inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Cre c (ket m)))) =
      (Real.sqrt ((m c : ℝ) + 1) : ℂ) *
        inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (ket (m + e c)))) := by
  rw [Cre_ket, map_smul, map_smul, inner_smul_right]

lemma uvec_apply (n m : Occ) (c : ℤ) :
    uvec 𝕍 n m c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Ann c (ket m)))) := by
  rw [inner_Ann_core, ME_conj, uvec, lp.star_apply, yvec_apply, ycoord]
  simp [zvec]

lemma wvec_apply (n m : Occ) (c : ℤ) :
    wvec 𝕍 n m c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Cre c (ket m)))) := by
  rw [inner_Cre_core, ME_conj, wvec, lp.star_apply, xvec_apply, xcoord]
  simp [zvec]

/-- The hypotheses of `HeisAnn`/`HeisCre` are not vacuous: the vectors exist. -/
lemma exists_uw (n m : Occ) : ∃ u w : H,
    (∀ c, u c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Ann c (ket m))))) ∧
    (∀ c, w c = inner ℂ (physCore (L := L) (ket n)) (𝕍 (physCore (Cre c (ket m))))) :=
  ⟨uvec 𝕍 n m, wvec 𝕍 n m, uvec_apply 𝕍 n m, wvec_apply 𝕍 n m⟩

lemma xvec_Vtil (m n : Occ) (c : ℤ) :
    xvec (Vtil 𝕍 (lp.single 2 m (1 : ℂ))) n c =
      inner ℂ (physCore (L := L) (Cre c (ket n))) (𝕍 (physCore (ket m))) := by
  rw [xvec_apply, xcoord, Vtil_single_apply, inner_physCore_Cre, inner_physCore_ket]

lemma yvec_Vtil (m n : Occ) (c : ℤ) :
    yvec (Vtil 𝕍 (lp.single 2 m (1 : ℂ))) n c =
      inner ℂ (physCore (L := L) (Ann c (ket n))) (𝕍 (physCore (ket m))) := by
  rw [yvec_apply, ycoord, inner_physCore_Ann]
  rw [Vtil_apply, Phi_apply, ← physCore_ket]

/-- **Source physical form ⟹ formal `PureQuasifree`.** -/
theorem physical_implies_pureQuasifree {x : Ext025B3PhysicalSectors.Fock L}
    (h : PhysicalQuasifreeSource x) : Ext006QuasifreeWeak.PureQuasifree (coefficient x) := by
  obtain ⟨𝕍, A, B, hs, hA, hC, rfl⟩ := h
  refine ⟨Vtil 𝕍, ContinuousLinearMap.adjoint A, -(tp B), invpair_isBogoliubov hs, ?_, ?_⟩
  · intro d m n
    have hX : xvec (Vtil 𝕍 (lp.single 2 m (1 : ℂ))) n = A (uvec 𝕍 n m) + B (wvec 𝕍 n m) := by
      apply lp.ext; funext c
      rw [xvec_Vtil]
      exact hA c n m _ _ (uvec_apply 𝕍 n m) (wvec_apply 𝕍 n m)
    have hY : yvec (Vtil 𝕍 (lp.single 2 m (1 : ℂ))) n =
        star (A (star (wvec 𝕍 n m))) + star (B (star (uvec 𝕍 n m))) := by
      apply lp.ext; funext c
      rw [yvec_Vtil]
      have := hC c n m _ _ (uvec_apply 𝕍 n m) (wvec_apply 𝕍 n m)
      rw [this, bar_apply, bar_apply]
      rfl
    have hid := invpair_identity hs hX hY
    have hd := congrArg (fun z : H => z d) hid
    simp only [lp.coeFn_sub, Pi.sub_apply] at hd
    rw [uvec_apply, inner_Ann_core] at hd
    simp only [neg_apply, lp.coeFn_neg, Pi.neg_apply]
    rw [Vtil_single_apply]
    rw [hd]
    ring
  · intro n
    rw [Vtil_single_apply, inner_physCore_ket]
    rfl

end QuantumNLS.Ext006PhysQuasifree
#print axioms QuantumNLS.Ext006PhysQuasifree.physical_implies_pureQuasifree
#print axioms QuantumNLS.Ext006PhysQuasifree.exists_uw
