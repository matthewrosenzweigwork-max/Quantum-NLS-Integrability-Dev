import Mathlib
import QuantumNLS.Prop022CQuad
import QuantumNLS.Prop022AFock
import QuantumNLS.Prop022StrongOperatorR125

/-! PROP-022 route A, round 4, stage C6: the torus sector formula of the physical quadratic operator
and the H-level identification of `QH`, `QJ` with the printed intrinsic operator.

`QRel_torus`: for `y` in the second-moment domain of the physical Fock space,
`strongCoordinates a b (rootLift 2 y)` is sector by sector `dΓ_n(a) y_n + ½ a_n(b) y_{n+2} + ½ a_{n-2}(b)† y_{n-2}`.
`QJ_QRel` / `QH_QRel`: hence `QJ`, `QH` satisfy the intrinsic relation `QRel` of `Prop022CQuad`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022CQuadTorus
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.Prop022CCanon QuantumNLS.Prop022BFock1
open QuantumNLS.Prop022CQuad QuantumNLS.Prop022StrongOperatorR125
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors

variable {L : ℝ} [Fact (0 < L)]

lemma numberBlockE_torus (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) :
    numberBlockE a n = Ext005QuadraticEnergyR108.numberBlock a n := rfl

lemma ann2_torus (b : HN L 2) (n : ℕ) : ann2 b n = Ext005PairSector.annihilation b n := rfl

lemma cre2_torus (b : HN L 2) (n : ℕ) : cre2 b n = Ext005PairSector.creation b n := rfl

lemma lower_single (j : ℕ) (hj : 1 ≤ j) (b : HN L 2) (k : ℕ) (w : HN L (2 + k)) :
    lower j hj b (lp.single 2 (2 + k) w : Fock L) = lp.single 2 k (lowerBlock j b k w) := by
  apply lp.ext
  funext n
  change lowerBlock j b n ((lp.single 2 (2 + k) w : Fock L) (2 + n)) = _
  by_cases hn : n = k
  · subst hn
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ (by omega : 2 + n ≠ 2 + k), lp.single_apply_ne _ _ _ hn,
      map_zero]

lemma lower_single_small (j : ℕ) (hj : 1 ≤ j) (b : HN L 2) (m : ℕ) (hm : m < 2) (w : HN L m) :
    lower j hj b (lp.single 2 m w : Fock L) = 0 := by
  apply lp.ext
  funext n
  change lowerBlock j b n ((lp.single 2 m w : Fock L) (2 + n)) = _
  rw [lp.single_apply_ne _ _ _ (by omega : 2 + n ≠ m), map_zero]
  rfl

lemma lowerAdj_small (b : HN L 2) (X : Fock L) (m : ℕ) (hm : m < 2) :
    ((lower 1 le_rfl b).adjoint X) m = 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [inner_zero_right, ← lp.inner_single_left (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_right,
    lower_single_small 1 le_rfl b m hm w, inner_zero_left]

lemma lowerAdj_succ (b : HN L 2) (X y : Fock L)
    (hX : Ext005FormScaleR109.embedding 2 X = y) (k : ℕ) :
    ((lower 1 le_rfl b).adjoint X) (2 + k) = Ext005PairSector.creation b k (y k) := by
  apply ext_inner_left ℂ
  intro w
  have hyk : y k = ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) • X k := by
    have h := congrArg (fun z : Fock L => z k) hX
    change Ext005FormScaleR109.embedding 2 X k = y k at h
    rw [embedding_two_apply] at h
    exact h.symm
  have e1 : ⟪w, ((lower 1 le_rfl b).adjoint X) (2 + k)⟫_ℂ = ⟪lowerBlock 1 b k w, X k⟫_ℂ := by
    rw [← lp.inner_single_left (𝕜 := ℂ) (2 + k) w ((lower 1 le_rfl b).adjoint X),
      ContinuousLinearMap.adjoint_inner_right, lower_single, lp.inner_single_left (𝕜 := ℂ)]
  rw [e1, hyk]
  unfold lowerBlock Ext005PairSector.creation
  rw [smul_apply, inner_smul_left, Complex.conj_ofReal, ContinuousLinearMap.adjoint_inner_right,
    inner_smul_right]
  simp [Nat.cast_one]

/-- **Sector formula of the physical quadratic operator.** -/
theorem QRel_torus (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (y : Fock L)
    (hy : y ∈ Ext005Moments.momentDomain (L := L) 2) :
    QRel a b y (strongCoordinates a b (Ext005FormCutoffR109.rootLift 2 y)) := by
  set X := Ext005FormCutoffR109.rootLift 2 y with hXdef
  have hX : Ext005FormScaleR109.embedding 2 X = y := by
    rw [hXdef, Ext005FormCutoffR109.rootLift_eq 2 y hy]
    exact Ext005FormScaleR109.embedding_root 2 ⟨y, hy⟩
  have hXn : ∀ n, Ext005FormScaleR109.embedding 2 X n = y n :=
    fun n => congrArg (fun z : Fock L => z n) hX
  have hsc : ∀ n, (strongCoordinates a b X) n =
      Ext005QuadraticEnergyR108.numberBlock a n (y n) +
        (1 / 2 : ℂ) • (Ext005PairSector.annihilation b n (y (2 + n)) +
          ((lower 1 le_rfl b).adjoint X) n) := by
    intro n
    have h1 : (Ext005PhysicalNumberFormR114.numberCoordinates a X) n =
        Ext005QuadraticEnergyR108.numberBlock a n (y n) :=
      (numberCoordinates_two a X n).trans (by rw [hXn])
    have h3 : (lower 3 (by omega) b X) n = Ext005PairSector.annihilation b n (y (2 + n)) :=
      (lower_three_apply b X n).trans (by rw [hXn])
    show (Ext005PhysicalNumberFormR114.numberCoordinates a X) n +
      (1 / 2 : ℂ) • ((lower 3 (by omega) b X) n + ((lower 1 (by omega) b).adjoint X) n) = _
    rw [h1, h3]
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [hsc 0, lowerAdj_small b X 0 (by omega), add_zero]
    rfl
  · rw [hsc 1, lowerAdj_small b X 1 (by omega), add_zero]
    rfl
  · rw [hsc (2 + k), lowerAdj_succ b X y hX k]
    rfl

/-! ### Transport -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem QJ_QRel (J : H →ₗᵢ[ℂ] L2T L) (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1)
    (b : SymSector ℂ H 2) (y : FockSpace H)
    (hy : y ∈ Prop022AFock.momentDomainH 2) :
    QRel a b y (Prop022BFock2.QJ J a b y) := by
  have hY := Prop022BFock3.gam_mem_moment J 2 y hy
  have h := QRel_torus (symI J 1 ∘L a ∘L symAdj J 1) (symI J 2 b) (fockMapI J y) hY
  refine QRel_transport J a b _ (fun w => ?_) y _ h
  simp only [ContinuousLinearMap.comp_apply, symAdj_symI]

lemma symI_equiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E ≃ₗᵢ[ℂ] L2T L) (n : ℕ) (x : SymSector ℂ E n) :
    symI U.toLinearIsometry n x = symMap U n x :=
  Subtype.ext (tensorMapI_equiv U n (x : HilbertTensorPower ℂ E n))

lemma gamAdj_equiv (U : H ≃ₗᵢ[ℂ] L2T L) (z : Fock L) :
    gamAdj U.toLinearIsometry z = (fockMap U).symm z := by
  have h := gamAdj_gam U.toLinearIsometry ((fockMap U).symm z)
  rw [fockMapI_equiv, LinearIsometryEquiv.apply_symm_apply] at h
  exact h

theorem QH_QRel (U : H ≃ₗᵢ[ℂ] L2T L) (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1)
    (b : SymSector ℂ H 2) (y : FockSpace H)
    (hy : y ∈ Prop022AFock.momentDomainH 2) :
    QRel a b y (Prop022AFock.QH U a b y) := by
  have hY : Prop022AFock.gam U y ∈ Ext005Moments.momentDomain (L := L) 2 :=
    (Prop022AFock.gam_mem_momentDomain U 2 y).2 hy
  have h := QRel_torus (Prop022GClassical.conjSym U 1 a) (symMap U 2 b) (Prop022AFock.gam U y) hY
  have hg : Prop022AFock.gam U y = fockMapI U.toLinearIsometry y := (fockMapI_equiv U y).symm
  have hb : symMap U 2 b = symI U.toLinearIsometry 2 b := (symI_equiv U 2 b).symm
  have h' : QRel (Prop022GClassical.conjSym U 1 a) (symI U.toLinearIsometry 2 b)
      (fockMapI U.toLinearIsometry y)
      (Prop022StrongOperatorR125.strongCoordinates (Prop022GClassical.conjSym U 1 a) (symMap U 2 b)
        (Ext005FormCutoffR109.rootLift 2 (Prop022AFock.gam U y))) := by
    rw [← hg, ← hb]
    exact h
  have h2 := QRel_transport U.toLinearIsometry a b (Prop022GClassical.conjSym U 1 a)
    (fun w => by
      rw [symI_equiv, symI_equiv, Prop022GClassical.conjSym_apply, LinearIsometryEquiv.symm_apply_apply])
    y _ h'
  rw [gamAdj_equiv] at h2
  exact h2

end QuantumNLS.Prop022CQuadTorus

#print axioms QuantumNLS.Prop022CQuadTorus.QRel_torus
#print axioms QuantumNLS.Prop022CQuadTorus.QJ_QRel
#print axioms QuantumNLS.Prop022CQuadTorus.QH_QRel
