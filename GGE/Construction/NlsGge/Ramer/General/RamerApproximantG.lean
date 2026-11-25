import NlsGge.Ramer.General.TruncatedFieldConvergenceG
import NlsGge.Ramer.RamerApproximant

/-!
# Ramer's approximant on the general source law (GB4)

Generalization of `NlsGge/Ramer/RamerApproximant.lean` to a `RamerSetting S`.
The generic `L²` dominated-convergence lemma `tendsto_eLpNorm_two_of_dominated`, the index set
`basisIndex` and `card_basisIndex` are reused from the old file.  The only anisotropy-sensitive
change is `‖S.incl b_p‖ ≤ √ratioSup` in place of `‖i b_p‖ ≤ 1`, which enters the constant of
`abs_ramerSum_sub_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### Coordinate basis of `H` -/

/-- Pairing against a basis vector depends only on the coordinate at its frequency. -/
theorem inner_basis_congr (p : ℤ × Fin 2)
    {x y : S.H} (h : S.hcoord x p.1 = S.hcoord y p.1) :
    ⟪weightedRealHilbertBasis S.cmWeight p, x⟫ =
      ⟪weightedRealHilbertBasis S.cmWeight p, y⟫ := by
  rw [weightedRealHilbertBasis_apply, weightedRealBasisVector_inner,
    weightedRealBasisVector_inner, weightedIsometry_apply, weightedIsometry_apply]
  have h' : (show WeightedHilbert S.cmWeight from x) p.1 =
      (show WeightedHilbert S.cmWeight from y) p.1 := h
  simp only [weightedCoordinates]
  rw [show ((show WeightedHilbert S.cmWeight from x : WeightedHilbert S.cmWeight) :
      ℤ → ℂ) p.1 = (show WeightedHilbert S.cmWeight from y : ℤ → ℂ) p.1 from h']

/-- The truncation `P_n` acts on the pairing with a basis vector by killing frequencies
outside `-n..n`. -/
theorem inner_basis_cmTrunc (n : ℕ) (p : ℤ × Fin 2) (y : S.H) :
    ⟪weightedRealHilbertBasis S.cmWeight p, ((S.cmTrunc n y : S.head n) : S.H)⟫ =
      if p.1 ∈ symmetricModes n then ⟪weightedRealHilbertBasis S.cmWeight p, y⟫ else 0 := by
  split_ifs with hp
  · apply S.inner_basis_congr
    rw [S.hcoord_cmTrunc]; simp only [hp, ↓reduceIte]
  · have h0 : S.hcoord (((S.cmTrunc n y : S.head n) : S.H)) p.1 =
        S.hcoord (0 : S.H) p.1 := by
      rw [S.hcoord_cmTrunc]; simp only [hp, ↓reduceIte]; rfl
    rw [S.inner_basis_congr p h0]; exact inner_zero_right _

theorem hcoord_basis_ne (p : ℤ × Fin 2) (m : ℤ)
    (hm : m ≠ p.1) : S.hcoord (weightedRealHilbertBasis S.cmWeight p) m = 0 := by
  rw [weightedRealHilbertBasis_apply]
  change (show WeightedHilbert S.cmWeight from
    weightedRealBasisVector S.cmWeight p) m = 0
  rw [weightedRealBasisVector_apply]
  simp [hm]

theorem ramerBasis_mem_head (N : ℕ) (p : ℤ × Fin 2)
    (hp : p.1 ∈ symmetricModes N) :
    weightedRealHilbertBasis S.cmWeight p ∈ S.head N := by
  intro m hm
  exact S.hcoord_basis_ne p m (fun h => hm (h ▸ hp))

theorem norm_basis (p : ℤ × Fin 2) :
    ‖weightedRealHilbertBasis S.cmWeight p‖ = 1 :=
  (weightedRealHilbertBasis S.cmWeight).orthonormal.1 p

/-! ### An orthonormal basis of the head `V_N` from the coordinate basis -/

/-- The coordinate basis vector `b p`, `p ∈ W N`, viewed in the head `V_N`. -/
def headBasisVec (N : ℕ) (p : basisIndex N) : S.head N :=
  ⟨weightedRealHilbertBasis S.cmWeight p.1,
    S.ramerBasis_mem_head N p.1 (Finset.mem_product.1 p.2).1⟩

theorem coe_headBasisVec (N : ℕ) (p : basisIndex N) :
    ((S.headBasisVec N p : S.head N) : S.H) =
      weightedRealHilbertBasis S.cmWeight p.1 := rfl

theorem headBasisVec_orthonormal (N : ℕ) :
    Orthonormal ℝ (S.headBasisVec N) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  have h := orthonormal_iff_ite.1 (weightedRealHilbertBasis S.cmWeight).orthonormal p.1 q.1
  change ⟪weightedRealHilbertBasis S.cmWeight p.1,
    weightedRealHilbertBasis S.cmWeight q.1⟫ = _
  rw [h]
  simp only [Subtype.ext_iff]

theorem finrank_head (N : ℕ) :
    Module.finrank ℝ (S.head N) = 2 * (2 * N + 1) := by
  rw [(S.headCoord N).finrank_eq, Module.finrank_pi_fintype]
  simp
  ring

/-- The orthonormal basis of `V_N` given by the coordinate basis vectors of `W N`. -/
def ramerHeadBasis (N : ℕ) :
    OrthonormalBasis (basisIndex N) ℝ (S.head N) :=
  OrthonormalBasis.mk (S.headBasisVec_orthonormal N)
    ((S.headBasisVec_orthonormal N).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [card_basisIndex, S.finrank_head])).ge

theorem ramerHeadBasis_apply (N : ℕ) (p : basisIndex N) :
    S.ramerHeadBasis N p = S.headBasisVec N p := by
  simp [ramerHeadBasis]

/-! ### The two approximants -/

/-- **Ramer's approximant** `a_n(x) = ⟨P_n K x, x⟩ - tr(P_n D K(x))` for `K = G : E → H`,
evaluated at the realization of the sample `z`, in the coordinate basis of `H`. -/
def ramerA (n : ℕ) (G : S.E → S.H) (z : ℤ → ℂ) : ℝ :=
  ∑ p ∈ basisIndex n,
    (⟪(S.headPt n z : S.H), weightedRealHilbertBasis S.cmWeight p⟫ *
      ⟪weightedRealHilbertBasis S.cmWeight p, G (S.R z)⟫ -
      ⟪weightedRealHilbertBasis S.cmWeight p,
        fderiv ℝ G (S.R z) (S.incl (weightedRealHilbertBasis S.cmWeight p))⟫)

/-- The level-`N` cylindrical field `v ↦ P_n G(v)` (`v ∈ V_N`, `v` viewed in `E`), `n ≤ N`,
with values in `V_n ⊆ V_N`. -/
def gRamer {n N : ℕ} (h : n ≤ N) (G : S.E → S.H) (v : S.head N) : S.head N :=
  S.levelIncl h (S.cmTrunc n (G (S.headToE N v)))

theorem fderiv_gRamer {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : Differentiable ℝ G) (v : S.head N) :
    fderiv ℝ (S.gRamer h G) v =
      (S.levelIncl h).comp ((S.cmTrunc n).comp
        ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N))) := by
  have h1 := (S.headToE N).hasFDerivAt (x := v)
  have h2 := (hG (S.headToE N v)).hasFDerivAt.comp v h1
  have h3 := (S.cmTrunc n).hasFDerivAt.comp v h2
  have h4 := (S.levelIncl h).hasFDerivAt.comp v h3
  exact h4.fderiv

theorem headToE_headBasisVec (N : ℕ) (p : basisIndex N) :
    S.headToE N (S.headBasisVec N p) =
      S.incl (weightedRealHilbertBasis S.cmWeight p.1) := rfl

/-! ### Goal 1: the finite identity -/

/-- **Finite identity** (`n ≤ N`): the divergence of the level-`N` cylindrical field
`P_n G(P_N ·)` is Ramer's approximant with `P_N x` in place of `x` in `G`, `DG`. -/
theorem cylDiv_gRamer {n N : ℕ}
    (h : n ≤ N) (G : S.E → S.H) (hG : ContDiff ℝ 1 G)
    (z : ℤ → ℂ) :
    S.cylDiv N (S.gRamer h G) z =
      ∑ p ∈ basisIndex n,
        (⟪(S.headPt n z : S.H), weightedRealHilbertBasis S.cmWeight p⟫ *
          ⟪weightedRealHilbertBasis S.cmWeight p,
            G (S.headToE N (S.headPt N z))⟫ -
          ⟪weightedRealHilbertBasis S.cmWeight p,
            fderiv ℝ G (S.headToE N (S.headPt N z))
              (S.incl (weightedRealHilbertBasis S.cmWeight p))⟫) := by
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  set x := S.headPt N z with hx
  set b := weightedRealHilbertBasis S.cmWeight with hb
  set i := S.incl with hi
  -- the general term at `p`
  let T : ℤ × Fin 2 → ℝ := fun p =>
    ⟪(x : S.H), b p⟫ * ⟪b p, ((S.cmTrunc n (G (S.headToE N x)) : S.head n) :
        S.H)⟫ -
      ⟪b p, ((S.cmTrunc n (fderiv ℝ G (S.headToE N x) (i (b p))) : S.head n) :
        S.H)⟫
  have hterm : ∀ p : basisIndex N,
      ⟪x, S.ramerHeadBasis N p⟫ * ⟪S.ramerHeadBasis N p, S.gRamer h G x⟫ -
        ⟪S.ramerHeadBasis N p, fderiv ℝ (S.gRamer h G) x (S.ramerHeadBasis N p)⟫ = T p.1 := by
    intro p
    rw [S.ramerHeadBasis_apply, S.fderiv_gRamer h G hGd]
    have e1 : ⟪x, S.headBasisVec N p⟫ = ⟪(x : S.H), b p.1⟫ := rfl
    have e2 : ⟪S.headBasisVec N p, S.gRamer h G x⟫ =
        ⟪b p.1, ((S.cmTrunc n (G (S.headToE N x)) : S.head n) : S.H)⟫ := rfl
    have e3 : ⟪S.headBasisVec N p, ((S.levelIncl h).comp ((S.cmTrunc n).comp
        ((fderiv ℝ G (S.headToE N x)).comp (S.headToE N)))) (S.headBasisVec N p)⟫ =
        ⟪b p.1, ((S.cmTrunc n (fderiv ℝ G (S.headToE N x) (i (b p.1))) : S.head n) :
          S.H)⟫ := by
      rw [← S.headToE_headBasisVec N p]
      rfl
    rw [e1, e2, e3]
  unfold cylDiv
  rw [finiteGaussianDivergence_eq_sum_orthonormalBasis (S.ramerHeadBasis N)]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Finset.sum_coe_sort (basisIndex N) T]
  have hsub : basisIndex n ⊆ basisIndex N := by
    intro p hp
    exact Finset.mem_product.2 ⟨symmetricModes_mono h (Finset.mem_product.1 hp).1,
      Finset.mem_univ _⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp1 : p.1 ∈ symmetricModes n := (Finset.mem_product.1 hp).1
    simp only [T]
    rw [S.inner_basis_cmTrunc, S.inner_basis_cmTrunc]
    simp only [hp1, ↓reduceIte]
    congr 2
    have hc : S.hcoord (x : S.H) p.1 = S.hcoord (S.headPt n z : S.H) p.1 := by
      rw [hx, S.hcoord_headPt, S.hcoord_headPt]
      simp only [symmetricModes_mono h hp1, hp1, ↓reduceIte]
    exact (real_inner_comm _ _).symm.trans ((S.inner_basis_congr p hc).trans (real_inner_comm _ _))
  · intro p hpN hpn
    have hp1 : p.1 ∉ symmetricModes n := fun h1 => hpn (Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩)
    simp only [T]
    rw [S.inner_basis_cmTrunc, S.inner_basis_cmTrunc]
    simp [hp1]

/-! ### The summand family `ramerSum` -/

/-- Ramer's sum with the point `x ∈ H` and the argument `y ∈ E` of `G`, `DG` kept separate:
`Σ_{p ∈ W n} (⟨x, b_p⟩ ⟨b_p, G y⟩ - ⟨b_p, DG(y)(i b_p)⟩)`. -/
def ramerSum (n : ℕ) (G : S.E → S.H) (x : S.H) (y : S.E) : ℝ :=
  ∑ p ∈ basisIndex n,
    (⟪x, weightedRealHilbertBasis S.cmWeight p⟫ *
      ⟪weightedRealHilbertBasis S.cmWeight p, G y⟫ -
      ⟪weightedRealHilbertBasis S.cmWeight p,
        fderiv ℝ G y (S.incl (weightedRealHilbertBasis S.cmWeight p))⟫)

theorem ramerA_eq (n : ℕ) (G : S.E → S.H) (z : ℤ → ℂ) :
    S.ramerA n G z = S.ramerSum n G (S.headPt n z : S.H) (S.R z) := rfl

theorem cylDiv_gRamer_eq {n N : ℕ}
    (h : n ≤ N) (G : S.E → S.H) (hG : ContDiff ℝ 1 G)
    (z : ℤ → ℂ) :
    S.cylDiv N (S.gRamer h G) z = S.ramerSum n G (S.headPt n z : S.H)
      (S.headToE N (S.headPt N z)) :=
  S.cylDiv_gRamer h G hG z

theorem continuous_ramerSum (n : ℕ)
    (G : S.E → S.H) (hG : ContDiff ℝ 1 G) (x : S.H) :
    Continuous (fun y => S.ramerSum n G x y) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  unfold ramerSum
  refine continuous_finsetSum _ (fun p _ => ?_)
  exact (continuous_const.mul (continuous_const.inner hG.continuous)).sub
    (continuous_const.inner (hD.clm_apply continuous_const))

/-- Anisotropic replacement of `‖i b_p‖ ≤ 1`: `‖i b_p‖ ≤ √ratioSup`. -/
theorem norm_inclusion_basis_le (p : ℤ × Fin 2) :
    ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ ≤ Real.sqrt S.ratioSup := by
  refine (S.incl_norm_le _).trans ?_
  rw [S.norm_basis, mul_one]

theorem abs_ramerSum_sub_le (n : ℕ)
    (G : S.E → S.H) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (x : S.H) (y y' : S.E) :
    |S.ramerSum n G x y - S.ramerSum n G x y'| ≤
      ((basisIndex n).card : ℝ) * (2 * B * (1 + Real.sqrt S.ratioSup)) * (1 + ‖x‖) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set κ := Real.sqrt S.ratioSup with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  set i := S.incl with hi
  set b := weightedRealHilbertBasis S.cmWeight with hb
  unfold ramerSum
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (2 * B * (1 + κ) * (1 + ‖x‖)) (fun p _ => ?_)).trans ?_
  · have hbn : ‖b p‖ = 1 := S.norm_basis p
    have h1 : |⟪x, b p⟫| ≤ ‖x‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hbn, mul_one]
    have h2 : |⟪b p, G y⟫ - ⟪b p, G y'⟫| ≤ 2 * B := by
      have e : ⟪b p, G y⟫ - ⟪b p, G y'⟫ = ⟪b p, G y - G y'⟫ := (inner_sub_right _ _ _).symm
      rw [e]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hbn, one_mul]
      refine (norm_sub_le _ _).trans ?_
      linarith [hB y, hB y']
    have h3 : |⟪b p, fderiv ℝ G y (i (b p))⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫| ≤ 2 * B * κ := by
      have e : ⟪b p, fderiv ℝ G y (i (b p))⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫ =
          ⟪b p, fderiv ℝ G y (i (b p)) - fderiv ℝ G y' (i (b p))⟫ := (inner_sub_right _ _ _).symm
      rw [e]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hbn, one_mul]
      refine (norm_sub_le _ _).trans ?_
      have hib : ‖i (b p)‖ ≤ κ := S.norm_inclusion_basis_le p
      have e1 : ‖fderiv ℝ G y (i (b p))‖ ≤ B * κ :=
        ((fderiv ℝ G y).le_opNorm _).trans
          (by nlinarith [hDB y, norm_nonneg (i (b p)), norm_nonneg (fderiv ℝ G y)])
      have e2 : ‖fderiv ℝ G y' (i (b p))‖ ≤ B * κ :=
        ((fderiv ℝ G y').le_opNorm _).trans
          (by nlinarith [hDB y', norm_nonneg (i (b p)), norm_nonneg (fderiv ℝ G y')])
      linarith
    have e : ⟪x, b p⟫ * ⟪b p, G y⟫ - ⟪b p, fderiv ℝ G y (i (b p))⟫ -
        (⟪x, b p⟫ * ⟪b p, G y'⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫) =
        ⟪x, b p⟫ * (⟪b p, G y⟫ - ⟪b p, G y'⟫) -
          (⟪b p, fderiv ℝ G y (i (b p))⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have hx0 := norm_nonneg x
    have : |⟪x, b p⟫| * |⟪b p, G y⟫ - ⟪b p, G y'⟫| ≤ ‖x‖ * (2 * B) :=
      mul_le_mul h1 h2 (abs_nonneg _) hx0
    nlinarith [mul_nonneg hB0 hκ0, mul_nonneg (mul_nonneg hB0 hκ0) hx0]
  · rw [nsmul_eq_mul]
    nlinarith [norm_nonneg x]

theorem measurable_ramerSum_comp (n : ℕ)
    (G : S.E → S.H) (hG : ContDiff ℝ 1 G)
    {α : Type*} [MeasurableSpace α] (X : α → S.head n) (Y : α → S.E)
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun z => S.ramerSum n G ((X z : S.head n) : S.H) (Y z)) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  unfold ramerSum
  refine Finset.measurable_sum _ (fun p _ => ?_)
  have f1 : Continuous (fun v : S.head n =>
      ⟪(v : S.H), weightedRealHilbertBasis S.cmWeight p⟫) :=
    continuous_subtype_val.inner continuous_const
  have f2 : Continuous (fun y : S.E =>
      ⟪weightedRealHilbertBasis S.cmWeight p, G y⟫) :=
    continuous_const.inner hG.continuous
  have f3 : Continuous (fun y : S.E =>
      ⟪weightedRealHilbertBasis S.cmWeight p, fderiv ℝ G y
        (S.incl (weightedRealHilbertBasis S.cmWeight p))⟫) :=
    continuous_const.inner (hD.clm_apply continuous_const)
  exact ((f1.measurable.comp hX).mul (f2.measurable.comp hY)).sub (f3.measurable.comp hY)

/-! ### Goal 2: `L²(γ)` convergence of the cylindrical divergences to Ramer's approximant -/

/-- **`cylDiv (P_n G(P_N ·)) → a_n(G)` in `L²(γ)`** as `N → ∞` (levels `N + n ≥ n`), for `G` of
class `C¹` from `E` to `H` with `G` and `DG` bounded by `B`. -/
theorem tendsto_eLpNorm_cylDiv_gRamer (n : ℕ)
    (G : S.E → S.H) (hG : ContDiff ℝ 1 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N : ℕ => eLpNorm (fun z =>
        S.cylDiv (N + n) (S.gRamer (Nat.le_add_left n N) G) z -
          S.ramerA n G z) 2 S.γ) atTop (𝓝 0) := by
  set γ := S.γ with hγ
  set R := S.R with hR
  have hRm : Measurable R := S.measurable_R
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set K : ℝ := ((basisIndex n).card : ℝ) * (2 * B * (1 + Real.sqrt S.ratioSup)) with hK
  set D : (ℤ → ℂ) → ℝ := fun z => K * (1 + ‖S.headPt n z‖) with hD
  let F : ℕ → (ℤ → ℂ) → ℝ := fun N z =>
    S.cylDiv (N + n) (S.gRamer (Nat.le_add_left n N) G) z - S.ramerA n G z
  have hFeq : ∀ N z, F N z =
      S.ramerSum n G (S.headPt n z : S.H)
        (S.headToE (N + n) (S.headPt (N + n) z)) -
      S.ramerSum n G (S.headPt n z : S.H) (R z) := by
    intro N z
    simp only [F]
    rw [S.cylDiv_gRamer_eq (Nat.le_add_left n N) G hG z, S.ramerA_eq]
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    have e : F N = fun z => S.ramerSum n G (S.headPt n z : S.H)
        (S.headToE (N + n) (S.headPt (N + n) z)) -
      S.ramerSum n G (S.headPt n z : S.H) (R z) := funext (hFeq N)
    rw [e]
    exact (S.measurable_ramerSum_comp n G hG _ _ (S.measurable_headPt n)
      ((S.headToE (N + n)).continuous.measurable.comp (S.measurable_headPt (N + n)))).sub
      (S.measurable_ramerSum_comp n G hG _ _ (S.measurable_headPt n) hRm)
  have hDint : Integrable (fun z => D z ^ 2) γ := by
    have h1 : Integrable (fun v : S.head n => K ^ 2 * (1 + ‖v‖) ^ 2)
        (finiteStdGaussian (S.head n)) :=
      (integrable_pow_one_add_norm 2).const_mul (K ^ 2)
    have h2 := (S.integrable_comp_headPt_iff n
      (fun v : S.head n => K ^ 2 * (1 + ‖v‖) ^ 2) (by fun_prop)).2 h1
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp only [hD]
    ring
  have hbd : ∀ N, ∀ᵐ z ∂γ, ‖F N z‖ ≤ D z := by
    intro N
    refine Eventually.of_forall fun z => ?_
    rw [hFeq, Real.norm_eq_abs]
    have := S.abs_ramerSum_sub_le n G B hB hDB (S.headPt n z : S.H)
      (S.headToE (N + n) (S.headPt (N + n) z)) (R z)
    exact this
  have hae := S.coord_R_ae
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz
    have h1 := S.tendsto_headToE_headPt z hz
    have h2 : Tendsto (fun N : ℕ => S.headToE (N + n) (S.headPt (N + n) z)) atTop (𝓝 (R z)) :=
      h1.comp (tendsto_add_atTop_nat n)
    have h3 := ((S.continuous_ramerSum n G hG (S.headPt n z : S.H)).tendsto
      (R z)).comp h2
    have h4 := h3.sub_const (S.ramerSum n G (S.headPt n z : S.H) (R z))
    rw [sub_self] at h4
    refine h4.congr (fun N => ?_)
    rw [hFeq]
    rfl
  exact tendsto_eLpNorm_two_of_dominated F (fun N => (hFm N).aestronglyMeasurable) D hDint hbd hlim

/-! ### Goal 3: `L²(γ; H)` convergence of the cylindrical fields -/

/-- **`P_n G(P_N ·) → P_n G` in `L²(γ; H)`** as `N → ∞` (levels `N + n ≥ n`), for continuous
`G : E → H` bounded by `B`. -/
theorem tendsto_eLpNorm_cylField_gRamer (n : ℕ)
    (G : S.E → S.H) (hG : Continuous G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N : ℕ => eLpNorm (fun z =>
        ‖S.cylField (N + n) (S.gRamer (Nat.le_add_left n N) G) z -
          ((S.cmTrunc n (G (S.R z)) : S.head n) : S.H)‖) 2
        S.γ) atTop (𝓝 0) := by
  set γ := S.γ with hγ
  let _ : MeasurableSpace S.H := borel _
  have _ : BorelSpace S.H := ⟨rfl⟩
  set R := S.R with hR
  have hRm : Measurable R := S.measurable_R
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let F : ℕ → (ℤ → ℂ) → ℝ := fun N z =>
    ‖S.cylField (N + n) (S.gRamer (Nat.le_add_left n N) G) z -
      ((S.cmTrunc n (G (R z)) : S.head n) : S.H)‖
  have hfield : ∀ N z, S.cylField (N + n) (S.gRamer (Nat.le_add_left n N) G) z =
      ((S.cmTrunc n (G (S.headToE (N + n) (S.headPt (N + n) z))) : S.head n) :
        S.H) := by
    intro N z
    rfl
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    have h1 : Measurable (fun z => S.cylField (N + n) (S.gRamer (Nat.le_add_left n N) G) z) := by
      have hc : Continuous (fun v : S.head (N + n) =>
          ((S.gRamer (Nat.le_add_left n N) G v : S.head (N + n)) : S.H)) :=
        continuous_subtype_val.comp ((S.levelIncl (Nat.le_add_left n N)).continuous.comp
          ((S.cmTrunc n).continuous.comp (hG.comp (S.headToE (N + n)).continuous)))
      exact hc.measurable.comp (S.measurable_headPt (N + n))
    have h2 : Measurable (fun z => ((S.cmTrunc n (G (R z)) : S.head n) : S.H)) :=
      (continuous_subtype_val.comp ((S.cmTrunc n).continuous.comp hG)).measurable.comp hRm
    exact (h1.sub h2).norm
  have hbd : ∀ N, ∀ᵐ z ∂γ, ‖F N z‖ ≤ 2 * B := by
    intro N
    refine Eventually.of_forall fun z => ?_
    simp only [F]
    rw [norm_norm, hfield]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((S.cmTrunc n (G (S.headToE (N + n) (S.headPt (N + n) z))) :
        S.head n) : S.H)‖ ≤ B := (S.norm_cmTrunc_le n _).trans (hB _)
    have h2 : ‖((S.cmTrunc n (G (R z)) : S.head n) : S.H)‖ ≤ B :=
      (S.norm_cmTrunc_le n _).trans (hB _)
    linarith
  have hae := S.coord_R_ae
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz
    have h1 := S.tendsto_headToE_headPt z hz
    have h2 : Tendsto (fun N : ℕ => S.headToE (N + n) (S.headPt (N + n) z)) atTop (𝓝 (R z)) :=
      h1.comp (tendsto_add_atTop_nat n)
    have hcont : Continuous (fun y : S.E =>
        ((S.cmTrunc n (G y) : S.head n) : S.H)) :=
      continuous_subtype_val.comp ((S.cmTrunc n).continuous.comp hG)
    have h3 := (hcont.tendsto (R z)).comp h2
    have h4 := tendsto_iff_norm_sub_tendsto_zero.1 h3
    refine h4.congr (fun N => ?_)
    simp only [F, Function.comp, hfield]
  have hDint : Integrable (fun _ : ℤ → ℂ => (2 * B) ^ 2) γ := integrable_const _
  exact tendsto_eLpNorm_two_of_dominated F (fun N => (hFm N).aestronglyMeasurable) (fun _ => 2 * B)
    hDint hbd hlim

end NlsGge.Ramer.General.RamerSetting
