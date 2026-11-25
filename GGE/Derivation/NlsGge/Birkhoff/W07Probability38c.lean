import NlsGge.Birkhoff.W07Probability38b
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Birkhoff.W08Compact38b
import NlsGge.Birkhoff.W09Approx38b

/-! # W07, part c: the finite determinant `|det D(P_N T P_N)|` of the Ramer density is F01's `|det L_N|`

Source: `paper/v2.tex` l.1561-1573 ("Use Lemma `lem:determinants` ... They give `|det L_N| → 1`") and
`prop:gaussiancommon` (finite-dimensional identity). Conditional on `B`, `O`.

The finite map of the cylindrical density is `T_N(w) = w + P_N K(P_N w)` on the head `P_N H`
(`H = ActualCM c`, CM norm), and `finiteRamerDensity T_N = |det DT_N| e^{-(‖T_N v‖² - ‖v‖²)/2}`.
We prove `det DT_N(v) = det L_N` (F01's `detLN`, the determinant of `P_N DT(x_N) P_N` on `P_N h⁰`)
by conjugating with the coordinate identification `P_N H ≅ P_N h⁰` (determinants are basis
independent), using the compatibility of the derivative of `T` on `E_s` and on `h⁰`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Incl

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

/-- The coordinate inclusion `E_s ↪ h^r` as a continuous real-linear map. -/
def eToCarrierCLM38 (s r : ℝ) : ECarrier38 c s →L[ℝ] SobolevCarrier38 r where
  toFun x := toCarrier38 r (fullWeightedToSobolev c s r x)
  map_add' x y := (fullWeightedToSobolev c s r).map_add x y
  map_smul' a x := (fullWeightedToSobolev c s r).map_smul a x
  cont := (fullWeightedToSobolev c s r).continuous

theorem carrierCoe_eToCarrierCLM38 (s r : ℝ) (x : ECarrier38 c s) :
    carrierCoe38 r (eToCarrierCLM38 c s r x) = eCoe38 c s x := by
  funext n
  exact fullWeightedToSobolev_apply c s r x n

end Incl

section HeadEquiv

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)

/-- The coordinate identification of the Cameron-Martin head `P_N H` with a subspace of `h⁰`. -/
def headToH0 : actualCMHead c N →ₗ[ℝ] SobolevCarrier38 ((0 : ℕ) : ℝ) :=
  ((eToCarrierCLM38 c s ((0 : ℕ) : ℝ)).comp (headToE c s N)).toLinearMap

theorem carrierCoe_headToH0 (w : actualCMHead c N) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (headToH0 c s N w) n = cmCoord (w : ActualCM c) n := by
  have := congrFun (carrierCoe_eToCarrierCLM38 c s ((0 : ℕ) : ℝ) (headToE c s N w)) n
  exact this

theorem projC_headToH0 (w : actualCMHead c N) :
    projC38 ((0 : ℕ) : ℝ) N (headToH0 c s N w) = headToH0 c s N w := by
  apply carrierExt38
  funext n
  rw [carrierCoe38_projC38, carrierCoe_headToH0]
  split_ifs with hn
  · rfl
  · exact (w.2 n hn).symm

theorem headToH0_mem (w : actualCMHead c N) : headToH0 c s N w ∈ (cp38 N).V :=
  ((cp38 N).mem_V_iff _).2 (projC_headToH0 c s N w)

/-- The linear equivalence `P_N H ≃ P_N h⁰` (coordinates). -/
def headEquiv : actualCMHead c N ≃ₗ[ℝ] (cp38 N).V :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (cp38 N).V (headToH0 c s N) (headToH0_mem c s N))
    ⟨fun a b hab => by
      have h := congrArg Subtype.val hab
      apply Subtype.ext
      apply cmCoord_ext
      intro n
      have := congrArg (fun t => carrierCoe38 ((0 : ℕ) : ℝ) t n) h
      simpa only [LinearMap.codRestrict_apply, carrierCoe_headToH0] using this,
     fun w => by
      refine ⟨headPt c N (carrierCoe38 ((0 : ℕ) : ℝ) (w : SobolevCarrier38 ((0 : ℕ) : ℝ))), ?_⟩
      apply Subtype.ext
      apply carrierExt38
      funext n
      have hw : projC38 ((0 : ℕ) : ℝ) N (w : SobolevCarrier38 ((0 : ℕ) : ℝ)) = w :=
        ((cp38 N).mem_V_iff _).1 w.2
      show carrierCoe38 ((0 : ℕ) : ℝ) (headToH0 c s N _) n = _
      rw [carrierCoe_headToH0, cmCoord_headPt]
      have := congrArg (fun t => carrierCoe38 ((0 : ℕ) : ℝ) t n) hw
      simp only [carrierCoe38_projC38] at this
      split_ifs at this ⊢ with hn
      · rfl
      · exact this⟩

theorem headEquiv_coord (w : actualCMHead c N) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) ((headEquiv c s N w : (cp38 N).V) : SobolevCarrier38 ((0 : ℕ) : ℝ)) n =
      cmCoord (w : ActualCM c) n :=
  carrierCoe_headToH0 c s N w n

end HeadEquiv

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

/-- `K' = T - Id : E_s → E_0` (the map of W06's `KW06_38` before `E_0 = H`). -/
def Kp38 (hs1 : s ≤ 1) : ECarrier38 c s → ECarrier38 c 0 :=
  eMap38 c s 0 (fun y => B.T y - y) (B.differences_mem_E0_38 O c hs1).1

theorem KW06_eq_Kp38 (hs1 : s ≤ 1) (x : ECarrier38 c s) :
    B.KW06_38 O c hs1 x = cmOfE0_38 c (B.Kp38 O c hs1 x) := rfl

theorem differentiableAt_Kp38 (hs1 : s ≤ 1) (x : ECarrier38 c s) :
    DifferentiableAt ℝ (B.Kp38 O c hs1) x :=
  ((B.analytic_differences_E0_38 O c hs1).1 x trivial).differentiableAt

/-- `T = Id + K'` coordinatewise, read in `h⁰`. -/
theorem TC0_comp_eToCarrier (hs1 : s ≤ 1) (y : ECarrier38 c s) :
    B.TC 0 (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) y) =
      eToCarrierCLM38 c s ((0 : ℕ) : ℝ) y +
        eToCarrierCLM38 c 0 ((0 : ℕ) : ℝ) (B.Kp38 O c hs1 y) := by
  apply carrierExt38
  funext n
  show carrierCoe38 ((0 : ℕ) : ℝ) (B.TC 0 (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) y)) n = _
  have e1 : carrierCoe38 ((0 : ℕ) : ℝ) (B.TC 0 (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) y)) =
      B.T (carrierCoe38 ((0 : ℕ) : ℝ) (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) y)) := rfl
  rw [e1, carrierCoe_eToCarrierCLM38]
  have e2 : carrierCoe38 ((0 : ℕ) : ℝ) (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) y +
      eToCarrierCLM38 c 0 ((0 : ℕ) : ℝ) (B.Kp38 O c hs1 y)) n =
      carrierCoe38 ((0 : ℕ) : ℝ) (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) y) n +
      carrierCoe38 ((0 : ℕ) : ℝ) (eToCarrierCLM38 c 0 ((0 : ℕ) : ℝ) (B.Kp38 O c hs1 y)) n := rfl
  rw [e2, carrierCoe_eToCarrierCLM38, carrierCoe_eToCarrierCLM38]
  unfold Kp38
  rw [eCoe38_eMap38]
  show B.T (eCoe38 c s y) n = eCoe38 c s y n + (B.T (eCoe38 c s y) n - eCoe38 c s y n)
  ring

/-- **Derivative compatibility.** The `h⁰`-derivative of `T` at an `E_s` point, in direction `u ∈ E_s`,
has coordinates `u_n + (D K(x) u)_n`. -/
theorem lop_coord_W07 (hs1 : s ≤ 1) (x u : ECarrier38 c s) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (B.Lop (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) x)
        (eToCarrierCLM38 c s ((0 : ℕ) : ℝ) u)) n =
      eCoe38 c s u n + NlsGge.Ramer.cmCoord (fderiv ℝ (B.KW06_38 O c hs1) x u) n := by
  set js := eToCarrierCLM38 c s ((0 : ℕ) : ℝ) with hjs
  set j0 := eToCarrierCLM38 c 0 ((0 : ℕ) : ℝ) with hj0
  have h1 : HasFDerivAt (B.TC 0 ∘ js) ((B.Lop (js x)).comp js) x :=
    (B.differentiableAt_TC0 (js x)).hasFDerivAt.comp x js.hasFDerivAt
  have h2 : HasFDerivAt (fun y => js y + j0 (B.Kp38 O c hs1 y))
      (js + j0.comp (fderiv ℝ (B.Kp38 O c hs1) x)) x :=
    js.hasFDerivAt.add (j0.hasFDerivAt.comp x (B.differentiableAt_Kp38 O c hs1 x).hasFDerivAt)
  have hfun : (B.TC 0 ∘ js) = fun y => js y + j0 (B.Kp38 O c hs1 y) :=
    funext fun y => B.TC0_comp_eToCarrier O c hs1 y
  rw [hfun] at h1
  have huniq := h1.unique h2
  have hu := congrArg (fun L => L u) huniq
  simp only [ContinuousLinearMap.comp_apply, add_apply] at hu
  rw [hu]
  have e3 : carrierCoe38 ((0 : ℕ) : ℝ) (js u + j0 ((fderiv ℝ (B.Kp38 O c hs1) x) u)) n =
      carrierCoe38 ((0 : ℕ) : ℝ) (js u) n +
        carrierCoe38 ((0 : ℕ) : ℝ) (j0 ((fderiv ℝ (B.Kp38 O c hs1) x) u)) n := rfl
  rw [e3, hjs, hj0, carrierCoe_eToCarrierCLM38, carrierCoe_eToCarrierCLM38]
  have hch : fderiv ℝ (B.KW06_38 O c hs1) x =
      (cmOfE0_38 c).comp (fderiv ℝ (B.Kp38 O c hs1) x) :=
    ((cmOfE0_38 c).hasFDerivAt.comp x (B.differentiableAt_Kp38 O c hs1 x).hasFDerivAt).fderiv
  rw [hch]
  rfl

theorem contDiff_KW06_W07 (hs1 : s ≤ 1) : ContDiff ℝ 2 (B.KW06_38 O c hs1) :=
  (B.analytic_KW06_38 O c hs1).contDiff

/-- The finite map `T_N(w) = w + P_N K(P_N w)` of the cylindrical Ramer density. -/
def TNfin38 (hs1 : s ≤ 1) (N : ℕ) : actualCMHead c N → actualCMHead c N :=
  fun w => w + truncField c s (B.KW06_38 O c hs1) N w

theorem hasFDerivAt_TNfin38 (hs1 : s ≤ 1) (N : ℕ) (v : actualCMHead c N) :
    HasFDerivAt (B.TNfin38 O c hs1 N)
      (ContinuousLinearMap.id ℝ _ + fderiv ℝ (truncField c s (B.KW06_38 O c hs1) N) v) v :=
  (hasFDerivAt_id v).add
    (((contDiff_truncField c s _ (B.contDiff_KW06_W07 O c hs1) N).differentiable
      (by norm_num)) v).hasFDerivAt

theorem fderiv_TNfin38_apply (hs1 : s ≤ 1) (N : ℕ) (v w : actualCMHead c N) :
    fderiv ℝ (B.TNfin38 O c hs1 N) v w =
      w + cmTrunc c N (fderiv ℝ (B.KW06_38 O c hs1) (headToE c s N v) (headToE c s N w)) := by
  rw [(B.hasFDerivAt_TNfin38 O c hs1 N v).fderiv,
    fderiv_truncField c s _ (B.contDiff_KW06_W07 O c hs1) N v]
  rfl

/-- The intertwining of the head derivative with `P_N DT(x_N) |_{P_N h⁰}`. -/
theorem headEquiv_intertwine_W07 (hs1 : s ≤ 1) (N : ℕ) (v w : actualCMHead c N) :
    headEquiv c s N (fderiv ℝ (B.TNfin38 O c hs1 N) v w) =
      B.DTN N (headEquiv c s N v) (headEquiv c s N w) := by
  apply Subtype.ext
  apply carrierExt38
  funext n
  rw [headEquiv_coord, B.fderiv_TNfin38_apply O c hs1 N v w]
  show _ = carrierCoe38 ((0 : ℕ) : ℝ) (projC38 ((0 : ℕ) : ℝ) N
    (B.Lop (headToH0 c s N v) (headToH0 c s N w))) n
  rw [carrierCoe38_projC38]
  have hl := B.lop_coord_W07 O c hs1 (headToE c s N v) (headToE c s N w) n
  have e1 : headToH0 c s N v = eToCarrierCLM38 c s ((0 : ℕ) : ℝ) (headToE c s N v) := rfl
  have e2 : headToH0 c s N w = eToCarrierCLM38 c s ((0 : ℕ) : ℝ) (headToE c s N w) := rfl
  rw [e1, e2, hl]
  have e3 : cmCoord ((w + cmTrunc c N (fderiv ℝ (B.KW06_38 O c hs1) (headToE c s N v)
      (headToE c s N w)) : actualCMHead c N) : ActualCM c) n =
      cmCoord (w : ActualCM c) n + cmCoord ((cmTrunc c N (fderiv ℝ (B.KW06_38 O c hs1)
        (headToE c s N v) (headToE c s N w)) : actualCMHead c N) : ActualCM c) n := rfl
  rw [e3, cmCoord_cmTrunc]
  by_cases hn : n ∈ symmetricModes N
  · simp only [hn, ↓reduceIte]; rfl
  · simp only [hn, ↓reduceIte, w.2 n hn]; simp

/-- `DT_N = e ∘ A ∘ e⁻¹`. -/
theorem DTN_eq_conj_W07 (hs1 : s ≤ 1) (N : ℕ) (v : actualCMHead c N) :
    ((B.DTN N (headEquiv c s N v) : (cp38 N).V →L[ℝ] (cp38 N).V) :
        (cp38 N).V →ₗ[ℝ] (cp38 N).V) =
      ((headEquiv c s N : actualCMHead c N ≃ₗ[ℝ] (cp38 N).V) : actualCMHead c N →ₗ[ℝ] (cp38 N).V)
        ∘ₗ ((fderiv ℝ (B.TNfin38 O c hs1 N) v : actualCMHead c N →L[ℝ] actualCMHead c N) :
          actualCMHead c N →ₗ[ℝ] actualCMHead c N) ∘ₗ
        ((headEquiv c s N).symm : (cp38 N).V →ₗ[ℝ] actualCMHead c N) := by
  apply LinearMap.ext
  intro w
  have := B.headEquiv_intertwine_W07 O c hs1 N v ((headEquiv c s N).symm w)
  simp only [LinearEquiv.apply_symm_apply] at this
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
  rw [this]

/-- **Determinant bridge.** The determinant of the derivative of the finite Ramer map
`T_N(w) = w + P_N K(P_N w)` at the head point `v = P_N x` equals F01's `det L_N`. -/
theorem det_TNfin_eq_detLN_W07 (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    (fderiv ℝ (B.TNfin38 O c hs1 N) (headPt c N (coordE c s x))).det =
      B.detLN (eToSob38 c s ((1 : ℕ) : ℝ) x) N := by
  set v := headPt c N (coordE c s x) with hv
  set y1 := eToSob38 c s ((1 : ℕ) : ℝ) x with hy1
  set x1 := projC38 ((1 : ℕ) : ℝ) N y1 with hx1
  have hx1' : projC38 ((1 : ℕ) : ℝ) N x1 = x1 := projC38_idem _ N y1
  have hp : ((headEquiv c s N v : (cp38 N).V) : H0_38) = i10_38 x1 := by
    apply carrierExt38
    funext n
    rw [headEquiv_coord, carrierCoe38_i10, hx1, carrierCoe38_projC38, cmCoord_headPt]
    split_ifs with hn
    · exact (congrFun (carrierCoe_eToSob38 c s ((1 : ℕ) : ℝ) x) n)
    · rfl
  have h1 : B.detTN N (headEquiv c s N v) = B.detLN x1 N :=
    B.detTN_eq_detLN N x1 hx1' (headEquiv c s N v) hp
  have h2 : B.detLN x1 N = B.detLN y1 N := by
    have hb : baseN38 x1 N = baseN38 y1 N := by
      unfold baseN38
      rw [hx1']
    have hL : B.LxN x1 N = B.LxN y1 N := by
      unfold LxN
      rw [hb]
    simp only [detLN, LNmap, hL]
  have h3 : B.detTN N (headEquiv c s N v) =
      LinearMap.det ((B.DTN N (headEquiv c s N v) : (cp38 N).V →L[ℝ] (cp38 N).V) :
        (cp38 N).V →ₗ[ℝ] (cp38 N).V) := by
    unfold detTN
    rw [B.fderiv_TN]
  have h4 := LinearMap.det_conj
    ((fderiv ℝ (B.TNfin38 O c hs1 N) v : actualCMHead c N →L[ℝ] actualCMHead c N) :
      actualCMHead c N →ₗ[ℝ] actualCMHead c N) (headEquiv c s N)
  rw [← B.DTN_eq_conj_W07 O c hs1 N v] at h4
  rw [← h2, ← h1, h3, h4]

end BirkhoffInput38

end NlsGge.Birkhoff
