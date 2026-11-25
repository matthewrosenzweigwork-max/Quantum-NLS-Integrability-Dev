import Mathlib
import QuantumNLS.Prop022CQuad
import QuantumNLS.GenericPlacementsZero

/-! PROP-022 route A, round 5, stage D1: `dΓ(1) = N`, intrinsically.

For an arbitrary complex Hilbert space `E` (no basis, no torus), `Prop022CCanon.numberBlockE a n` is the
DEF-041 placement `n · Q_{n,1}(a)` of a one-body operator `a ∈ B(Sym¹ E)` on the sector `n`.  This module proves
that for `a = 1` the DEF-041 average placement is the identity, hence

* `numberBlockE_one`:   `dΓ_n(1) = n · 1` on `Sym^n E` (all `n`, including `n = 0` where both sides vanish);
* `dGamma_one_eq_number`: sectorwise `(dΓ(1) x)_n = n • x_n`, i.e. `dΓ(1)` is the number operator `N`
  (`numSeq`) on every vector of `Fock(E)` (maximal domain);
* `QRel_one_zero_iff`: the printed quadratic relation `Prop022CQuad.QRel` for the data `(a, b) = (1, 0)` says
  exactly `z = N y`;
* `inner_dGamma_one_sector`, `numExp_term_eq`, `numExpH_eq_dGamma`: `⟪x_n, (dΓ(1)x)_n⟫ = n ‖x_n‖²`, and
  `Prop022AFock.numExpH x = ∑' n, ofReal Re ⟪x_n, (dΓ(1) x)_n⟫` (`numExpH x = ∑_n n ‖x_n‖²`, the quantity of the
  printed identity `⟨ξ, Num ξ⟩ = ‖β‖²_HS`).

Everything is generic in `E`; the identity of the average placement is proved from the literal definition
`symmetrizedPlacement` (permutation average of `permRep σ ∘ firstPlacement ∘ permRep σ⁻¹`). -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace ENNReal
open QuantumNLS.TensorCarrier

namespace QuantumNLS.Prop022DNumber
open QuantumNLS.Prop022GTensor QuantumNLS.Prop022CCanon QuantumNLS.Prop022CQuad
open QuantumNLS.TensorPlacements

section Placement
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- On the one-fold tensor power the symmetrizing projection is the identity. -/
lemma symProj_one : symProj ℂ E 1 = ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E 1) := by
  rw [symProj_eq_factorial_average]
  have h1 : (Equiv.Perm (Fin 1)) ≃ Unit := ⟨fun _ => (), fun _ => 1, fun σ => Subsingleton.elim _ _,
    fun _ => rfl⟩
  rw [Finset.univ_unique, Finset.sum_singleton]
  have : (default : Equiv.Perm (Fin 1)) = 1 := Subsingleton.elim _ _
  rw [this, map_one]
  simp
  rfl

lemma extendSymKernel_id_one :
    extendSymKernel (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) =
      ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E 1) := by
  ext x
  change ((symProjToSector 1 x : SymSector ℂ E 1) : HilbertTensorPower ℂ E 1) = x
  change symProj ℂ E 1 x = x
  rw [symProj_one]
  rfl

lemma firstPlacement_id_one {q : ℕ} :
    firstPlacement (p := 1) (q := q) (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) =
      ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E (1 + q)) := by
  unfold firstPlacement
  simp only
  rw [extendSymKernel_id_one, GenericPlacementsZero.htmap_id_id]
  ext z
  simp

lemma permutedPlacement_id_one {q : ℕ} (σ : Equiv.Perm (Fin (1 + q))) :
    permutedPlacement σ (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) =
      ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E (1 + q)) := by
  unfold permutedPlacement
  rw [firstPlacement_id_one]
  ext z
  have h : (permRep ℂ E (1 + q) σ :
      HilbertTensorPower ℂ E (1 + q) →L[ℂ] HilbertTensorPower ℂ E (1 + q)) *
      (permRep ℂ E (1 + q) σ⁻¹ :
      HilbertTensorPower ℂ E (1 + q) →L[ℂ] HilbertTensorPower ℂ E (1 + q)) = 1 := by
    have h0 : permRep ℂ E (1 + q) σ * permRep ℂ E (1 + q) σ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg Subtype.val h0
  have h2 := congrArg (fun g : HilbertTensorPower ℂ E (1 + q) →L[ℂ] HilbertTensorPower ℂ E (1 + q) => g z) h
  exact h2

/-- **The DEF-041 average one-body placement of the identity is the identity.** -/
lemma Q_N_p_id_one {q : ℕ} :
    Q_N_p (p := 1) (q := q) (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) =
      ContinuousLinearMap.id ℂ (SymSector ℂ E (1 + q)) := by
  ext x
  change symmetrizedPlacement (p := 1) (q := q) (ContinuousLinearMap.id ℂ (SymSector ℂ E 1))
    (x : HilbertTensorPower ℂ E (1 + q)) = x
  unfold symmetrizedPlacement
  have hs : ∑ σ : Equiv.Perm (Fin (1 + q)),
      permutedPlacement σ (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) =
      Fintype.card (Equiv.Perm (Fin (1 + q))) • ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E (1 + q)) := by
    rw [Finset.sum_congr rfl (fun σ _ => permutedPlacement_id_one σ), Finset.sum_const, Finset.card_univ]
  have hc : (Fintype.card (Equiv.Perm (Fin (1 + q))) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hs, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rfl

lemma castSymOp_id {m n : ℕ} (h : m = n) :
    castSymOp h (ContinuousLinearMap.id ℂ (SymSector ℂ E m)) =
      ContinuousLinearMap.id ℂ (SymSector ℂ E n) := by
  subst h
  rfl

lemma physQ_id (n : ℕ) (hn : 1 ≤ n) :
    physQ n 1 hn (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) =
      ContinuousLinearMap.id ℂ (SymSector ℂ E n) := by
  unfold physQ
  rw [Q_N_p_id_one, castSymOp_id]

/-- **`dΓ_n(1) = n · 1`** on `Sym^n E`, for every `n`. -/
theorem numberBlockE_one (n : ℕ) :
    numberBlockE (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) n =
      (n : ℂ) • ContinuousLinearMap.id ℂ (SymSector ℂ E n) := by
  unfold numberBlockE
  by_cases hn : 1 ≤ n
  · simp only [hn, ↓reduceDIte, physQ_id]
  · have h0 : n = 0 := by omega
    subst h0
    ext y
    simp [hn]

end Placement

section FockLevel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The number operator `N` on `Fock(E)`: `(N x)_n = n x_n` (as a sector sequence). -/
def numSeq (x : FockSpace E) (n : ℕ) : SymSector ℂ E n := (n : ℂ) • x n

/-- The second quantization `dΓ(a)` of a one-body operator, sectorwise: `(dΓ(a) x)_n = dΓ_n(a) x_n`. -/
def dGammaSeq (a : SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1) (x : FockSpace E) (n : ℕ) :
    SymSector ℂ E n :=
  numberBlockE a n (x n)

/-- **`dΓ(1) = N`**: sector by sector, on every vector of `Fock(E)`. -/
theorem dGamma_one_eq_number (x : FockSpace E) :
    dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) x = numSeq x := by
  funext n
  unfold dGammaSeq numSeq
  rw [numberBlockE_one]
  rfl

/-- The printed quadratic relation for `(a, b) = (1, 0)` is exactly `z = N y`. -/
theorem QRel_one_zero_iff (y z : FockSpace E) :
    QRel (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) (0 : SymSector ℂ E 2) y z ↔
      ∀ n : ℕ, z n = numSeq y n := by
  have hz : ∀ n (w : SymSector ℂ E (2 + n)), ann2 (0 : SymSector ℂ E 2) n w = 0 := by
    intro n w
    unfold ann2
    have hc : ∀ Φ : HilbertTensor ℂ (HilbertTensorPower ℂ E 2) (HilbertTensorPower ℂ E n),
        IntrinsicContact.contractL (F := HilbertTensorPower ℂ E n)
          (0 : HilbertTensorPower ℂ E 2) Φ = 0 := by
      intro Φ
      apply ext_inner_left ℂ
      intro v
      rw [IntrinsicContact.inner_contractL, inner_zero_right]
      have : htmul (0 : HilbertTensorPower ℂ E 2) v =
          (0 : HilbertTensor ℂ (HilbertTensorPower ℂ E 2) (HilbertTensorPower ℂ E n)) := by
        have h := htmul_smul_left (0 : ℂ) (0 : HilbertTensorPower ℂ E 2) v
        simpa using h
      rw [this, inner_zero_left]
    simp [hc]
  have hc2 : ∀ k (w : SymSector ℂ E k), cre2 (0 : SymSector ℂ E 2) k w = 0 := by
    intro k w
    unfold cre2
    have : ann2 (0 : SymSector ℂ E 2) k = 0 := by
      ext w'
      exact congrArg Subtype.val (hz k w')
    rw [this]
    simp
  constructor
  · rintro ⟨h0, h1, h2⟩ n
    obtain rfl | rfl | ⟨k, rfl⟩ : n = 0 ∨ n = 1 ∨ ∃ k, n = 2 + k := by
      rcases n with _ | _ | k
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨k, by omega⟩)
    · rw [h0, hz]; simp [numSeq, numberBlockE_one]
    · rw [h1, hz]; simp [numSeq, numberBlockE_one]
    · rw [h2, hz, hc2]; simp [numSeq, numberBlockE_one]
  · intro h
    refine ⟨?_, ?_, fun k => ?_⟩
    · rw [h 0, hz]; simp [numSeq, numberBlockE_one]
    · rw [h 1, hz]; simp [numSeq, numberBlockE_one]
    · rw [h (2 + k), hz, hc2]; simp [numSeq, numberBlockE_one]

/-- `⟪x, dΓ(1) x⟫ = ∑_n n ‖x_n‖²`, termwise. -/
theorem inner_dGamma_one_sector (x : FockSpace E) (n : ℕ) :
    ⟪x n, dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) x n⟫_ℂ = (n : ℂ) * ((‖x n‖ ^ 2 : ℝ) : ℂ) := by
  rw [dGamma_one_eq_number]
  unfold numSeq
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- The number expectation `⟨x, N x⟩ = ∑ n ‖x_n‖²` of `Prop022AFock.numExpH` is the `ENNReal`-valued
quadratic form of `dΓ(1)`, sector by sector. -/
theorem numExp_term_eq (x : FockSpace E) (n : ℕ) :
    (n : ℝ≥0∞) * ENNReal.ofReal (‖x n‖ ^ 2) =
      ENNReal.ofReal ((⟪x n, dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) x n⟫_ℂ).re) := by
  rw [inner_dGamma_one_sector]
  have : ((n : ℂ) * ((‖x n‖ ^ 2 : ℝ) : ℂ)).re = (n : ℝ) * ‖x n‖ ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-- **`numExpH = ⟨·, dΓ(1) ·⟩`**: the number expectation of `Prop022AFock` (the quantity in the printed identity
`⟨ξ, Num ξ⟩ = ‖β‖²_HS`) is the quadratic form of the intrinsic `dΓ(1)`. -/
theorem numExpH_eq_dGamma (x : FockSpace E) :
    Prop022AFock.numExpH x =
      ∑' n : ℕ, ENNReal.ofReal ((⟪x n, dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) x n⟫_ℂ).re) :=
  tsum_congr (numExp_term_eq x)

end FockLevel

end QuantumNLS.Prop022DNumber

#print axioms QuantumNLS.Prop022DNumber.numberBlockE_one
#print axioms QuantumNLS.Prop022DNumber.dGamma_one_eq_number
#print axioms QuantumNLS.Prop022DNumber.QRel_one_zero_iff
#print axioms QuantumNLS.Prop022DNumber.numExp_term_eq
#print axioms QuantumNLS.Prop022DNumber.numExpH_eq_dGamma
