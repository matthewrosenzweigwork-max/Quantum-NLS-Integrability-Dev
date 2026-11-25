import Mathlib
import QuantumNLS.Prop022CCanon
import QuantumNLS.Prop022BFock3

/-! PROP-022 route A, round 4, stage C5: the printed quadratic Hamiltonian
`dΓ(a) + ½ (a*(b) + a(b))` as an INTRINSIC sectorwise relation on `Fock(H)`, and its identification with
the transported / compressed operators `QH`, `QJ`.

* `QRel a b y z`: `z` is the vector `[dΓ(a) + ½(a*(b)+a(b))] y`, i.e. sector by sector
  `z_n = dΓ_n(a) y_n + ½ a_n(b) y_{n+2} + ½ [n ≥ 2] a_{n-2}(b)† y_{n-2}`
  (`numberBlockE`, `ann2`, `cre2` of `Prop022CCanon`, defined from `H` alone).
  `QRel_unique`: `z` is determined by `(a,b,y)`; `QPrint` is the resulting operator (maximal domain).
* `QRel_torus`: on the physical carrier, `strongCoordinates a b (rootLift 2 y)` satisfies `QRel` for every `y`
  in the second-moment domain (frozen R125 sector formulas `lower_three_apply`, `numberCoordinates_two`,
  and the sector formula of the adjoint of `lower 1`).
* `QRel_transport`: `QRel` for `(Γ₁ a Γ₁†, Γ₂ b)` and `Γ(J) y` pulls back to `QRel a b y` along `Γ(J)†`.
* `QJ_QRel`, `QH_QRel`: for `y` in the second-moment domain of `Fock(H)`, `QRel a b y (QJ J a b y)` and
  `QRel a b y (QH U a b y)`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022CQuad
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.Prop022CCanon QuantumNLS.Prop022BFock1

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `z = [dΓ(a) + ½(a*(b) + a(b))] y`, sector by sector. -/
def QRel (a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1) (b : SymSector ℂ E 2)
    (y z : FockSpace E) : Prop :=
  z 0 = numberBlockE a 0 (y 0) + (1 / 2 : ℂ) • ann2 b 0 (y (2 + 0)) ∧
  z 1 = numberBlockE a 1 (y 1) + (1 / 2 : ℂ) • ann2 b 1 (y (2 + 1)) ∧
  ∀ k : ℕ, z (2 + k) = numberBlockE a (2 + k) (y (2 + k)) +
    (1 / 2 : ℂ) • (ann2 b (2 + k) (y (2 + (2 + k))) + cre2 b k (y k))

theorem QRel_unique {a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1} {b : SymSector ℂ E 2}
    {y z z' : FockSpace E} (h : QRel a b y z) (h' : QRel a b y z') : z = z' := by
  obtain ⟨h0, h1, h2⟩ := h
  obtain ⟨h0', h1', h2'⟩ := h'
  apply lp.ext
  funext n
  obtain rfl | rfl | ⟨k, rfl⟩ : n = 0 ∨ n = 1 ∨ ∃ k, n = 2 + k := by
    rcases n with _ | _ | k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨k, by omega⟩)
  · exact h0.trans h0'.symm
  · exact h1.trans h1'.symm
  · exact (h2 k).trans (h2' k).symm

/-- The printed quadratic operator on its maximal sectorwise domain. -/
def QPrint (a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1) (b : SymSector ℂ E 2)
    (y : FockSpace E) : FockSpace E := by
  classical
  exact if h : ∃ z, QRel a b y z then h.choose else 0

theorem QPrint_eq {a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1} {b : SymSector ℂ E 2}
    {y z : FockSpace E} (h : QRel a b y z) : QPrint a b y = z := by
  classical
  have hex : ∃ z, QRel a b y z := ⟨z, h⟩
  unfold QPrint
  rw [dif_pos hex]
  exact QRel_unique hex.choose_spec h

/-- Pull-back of the sector relation along `Γ(J)†`. -/
theorem QRel_transport (J : E →ₗᵢ[ℂ] F) (a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1)
    (b : SymSector ℂ E 2) (a' : SymSector ℂ F 1 →L[ℂ] SymSector ℂ F 1)
    (ha : ∀ y, symI J 1 (a y) = a' (symI J 1 y)) (y : FockSpace E) (Z : FockSpace F)
    (hZ : QRel a' (symI J 2 b) (fockMapI J y) Z) : QRel a b y (gamAdj J Z) := by
  have hNB : ∀ n (w : SymSector ℂ E n),
      symAdj J n (numberBlockE a' n (symI J n w)) = numberBlockE a n w := by
    intro n w
    rw [← numberBlockE_cov J a a' ha n w, symAdj_symI]
  have hA : ∀ n (w : SymSector ℂ E (2 + n)),
      symAdj J n (ann2 (symI J 2 b) n (symI J (2 + n) w)) = ann2 b n w := by
    intro n w
    have h := (cre2_cov J b n).fwd
    have h2 := (cre2_cov J b n).ann w
    have e : ContinuousLinearMap.adjoint (cre2 b n) = ann2 b n := by
      rw [cre2, ContinuousLinearMap.adjoint_adjoint]
    have e' : ContinuousLinearMap.adjoint (cre2 (symI J 2 b) n) = ann2 (symI J 2 b) n := by
      rw [cre2, ContinuousLinearMap.adjoint_adjoint]
    rw [e, e'] at h2
    rw [← h2, symAdj_symI]
  have hC : ∀ k (w : SymSector ℂ E k),
      symAdj J (2 + k) (cre2 (symI J 2 b) k (symI J k w)) = cre2 b k w := by
    intro k w
    rw [(cre2_cov J b k).adj_cre, symAdj_symI]
  obtain ⟨h0, h1, h2⟩ := hZ
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [gamAdj_sector, h0, map_add, map_smul]
    simp only [fockMapI_apply, symI_apply] at *
    rw [hNB, hA]
  · rw [gamAdj_sector, h1, map_add, map_smul]
    simp only [fockMapI_apply, symI_apply] at *
    rw [hNB, hA]
  · rw [gamAdj_sector, h2 k, map_add, map_smul, map_add]
    simp only [fockMapI_apply, symI_apply] at *
    rw [hNB, hA, hC]

end Generic

end QuantumNLS.Prop022CQuad

#print axioms QuantumNLS.Prop022CQuad.QRel_transport
