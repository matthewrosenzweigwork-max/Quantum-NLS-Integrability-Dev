import NlsGge.Birkhoff.F05Identity38c

/-! # F05, file d: the finite Jacobian `|det ψ_N'| = |det L_N| → 1` (F05.05, via F01)

`ψ_N = P_N T P_N` on the finite head `V_N = P_N H` of `S_m.H`, with `H`-norm.  Its derivative at a
head point, read in coordinates, is `L_N = P_N DT(x_N) P_N |_{V_N}` of F01 (derivative of `T` on
`h⁰`, compatible with the derivative on `h^{m-1}` by A1.3).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General Filter Topology
open scoped ENNReal

section Deriv

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- The smoothing map `K : h^{m-1} → h^m` on carriers. -/
def KC05 : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) → SobolevCarrier38 ((m - 1 + 1 : ℕ) : ℝ) :=
  carrierMap38 ((m - 1 : ℕ) : ℝ) ((m - 1 + 1 : ℕ) : ℝ) (fun y => B.T y - y)
    (O.smooth_T (m - 1) (one_le_pred05 hm))

theorem K05_eq (x : (S05 m β hm hβ).E) :
    K05 B O hm hβ x = cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)
      (KC05 B O hm ((Eq05 m β hm hβ).symm x)) := rfl

theorem differentiableAt_KC05 (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) :
    DifferentiableAt ℝ (KC05 B O hm) y :=
  ((O.analytic_smooth_T (m - 1) (one_le_pred05 hm)) y trivial).differentiableAt

/-- `ι ∘ K = T - Id` on `h^{m-1}`, differentiated. -/
theorem incl_fderiv_KC05 (y η : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) :
    carrierIncl38 (Nat.cast_le.2 (Nat.le_succ (m - 1)) :
        ((m - 1 : ℕ) : ℝ) ≤ ((m - 1 + 1 : ℕ) : ℝ)) (fderiv ℝ (KC05 B O hm) y η) =
      fderiv ℝ (B.TC (m - 1)) y η - η := by
  set ι := carrierIncl38 (Nat.cast_le.2 (Nat.le_succ (m - 1)) :
        ((m - 1 : ℕ) : ℝ) ≤ ((m - 1 + 1 : ℕ) : ℝ)) with hι
  have hf : (fun y => B.TC (m - 1) y - y) = ι ∘ (KC05 B O hm) := by
    funext y
    apply carrierExt38
    funext n
    show B.T (carrierCoe38 _ y) n - carrierCoe38 _ y n = _
    rfl
  have h1 : HasFDerivAt (fun y => B.TC (m - 1) y - y)
      (fderiv ℝ (B.TC (m - 1)) y - ContinuousLinearMap.id ℝ _) y :=
    (((B.analyticOnNhd_TC (m - 1)) y trivial).differentiableAt.hasFDerivAt).sub
      (hasFDerivAt_id y)
  have h2 : HasFDerivAt (ι ∘ (KC05 B O hm)) (ι.comp (fderiv ℝ (KC05 B O hm) y)) y :=
    ι.hasFDerivAt.comp y (differentiableAt_KC05 B O hm y).hasFDerivAt
  rw [← hf] at h2
  have := h1.unique h2
  have := congrArg (fun L => L η) this
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply] at this
  exact this.symm

theorem hcoord_fderiv_K05 (x ξ : (S05 m β hm hβ).E) (n : ℤ) :
    (S05 m β hm hβ).hcoord (fderiv ℝ (K05 B O hm hβ) x ξ) n =
      carrierCoe38 _ (fderiv ℝ (B.TC (m - 1)) ((Eq05 m β hm hβ).symm x)
        ((Eq05 m β hm hβ).symm ξ)) n - carrierCoe38 _ ((Eq05 m β hm hβ).symm ξ) n := by
  have hKeq : K05 B O hm hβ = fun x => cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)
      (KC05 B O hm ((Eq05 m β hm hβ).symm x)) := funext (K05_eq B O hm hβ)
  have h1 : HasFDerivAt (K05 B O hm hβ)
      ((cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)).comp
        ((fderiv ℝ (KC05 B O hm) ((Eq05 m β hm hβ).symm x)).comp
          (Eq05 m β hm hβ).symm.toLinearIsometry.toContinuousLinearMap)) x := by
    rw [hKeq]
    exact (cmOf05 m β hm hβ (m - 1 + 1) (le_pred_add_one05 m hm)).hasFDerivAt.comp x
      ((differentiableAt_KC05 B O hm _).hasFDerivAt.comp x
        (Eq05 m β hm hβ).symm.toLinearIsometry.toContinuousLinearMap.hasFDerivAt)
  have h3 : fderiv ℝ (K05 B O hm hβ) x = _ := h1.fderiv
  rw [h3]
  have := incl_fderiv_KC05 B O hm ((Eq05 m β hm hβ).symm x) ((Eq05 m β hm hβ).symm ξ)
  have h2 := congrArg (fun w => carrierCoe38 _ w n) this
  simp only [carrierCoe38_incl38] at h2
  exact h2


end Deriv

/-- The inclusion `h^{m-1} → h⁰`. -/
def ι0_05 (m : ℕ) : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) →L[ℝ] SobolevCarrier38 ((0 : ℕ) : ℝ) :=
  carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (m - 1)) : ((0 : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ))

/-- The inclusion `h^{m-1} → h¹`. -/
def ι1_05 (m : ℕ) (hm : 2 ≤ m) :
    SobolevCarrier38 ((m - 1 : ℕ) : ℝ) →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierIncl38 (Nat.cast_le.2 (one_le_pred05 hm) : ((1 : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ))

theorem carrierCoe_ι0_05 (m : ℕ) (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) (n : ℤ) :
    carrierCoe38 _ (ι0_05 m y) n = carrierCoe38 _ y n := by
  unfold ι0_05; rw [carrierCoe38_incl38]

theorem carrierCoe_ι1_05 (m : ℕ) (hm : 2 ≤ m) (y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) (n : ℤ) :
    carrierCoe38 _ (ι1_05 m hm y) n = carrierCoe38 _ y n := by
  unfold ι1_05; rw [carrierCoe38_incl38]

section Head

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) (N : ℕ)

/-- The carrier element of a head vector. -/
def yHead05 (v : (S05 m β hm hβ).head N) : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) :=
  (Eq05 m β hm hβ).symm ((S05 m β hm hβ).headToE N v)

theorem coe_yHead05 (v : (S05 m β hm hβ).head N) (n : ℤ) :
    carrierCoe38 _ (yHead05 hm hβ N v) n = (S05 m β hm hβ).hcoord (v : (S05 m β hm hβ).H) n :=
  hcoord_incl_eq05 hm hβ (v : (S05 m β hm hβ).H) n

theorem coe_yHead05_zero (v : (S05 m β hm hβ).head N) (n : ℤ) (hn : n ∉ symmetricModes N) :
    carrierCoe38 _ (yHead05 hm hβ N v) n = 0 := by
  rw [coe_yHead05]; exact v.2 n hn

theorem ι0_yHead_mem_V (v : (S05 m β hm hβ).head N) :
    ι0_05 m (yHead05 hm hβ N v) ∈ (cp38 N).V := by
  rw [(cp38 N).mem_V_iff, cp38_P]
  apply carrierExt38
  funext n
  rw [carrierCoe38_projC38]
  split_ifs with hn
  · rfl
  · rw [carrierCoe_ι0_05, coe_yHead05_zero hm hβ N v n hn]

/-- `φ : P_N H → V_N = P_N h⁰`, the coordinate identity. -/
def phi05 : (S05 m β hm hβ).head N →ₗ[ℝ] (cp38 N).V :=
  LinearMap.codRestrict (cp38 N).V
    (((ι0_05 m).comp ((Eq05 m β hm hβ).symm.toLinearIsometry.toContinuousLinearMap.comp
      ((S05 m β hm hβ).headToE N))) : (S05 m β hm hβ).head N →ₗ[ℝ] SobolevCarrier38 ((0 : ℕ) : ℝ))
    (fun v => ι0_yHead_mem_V hm hβ N v)

theorem coe_phi05 (v : (S05 m β hm hβ).head N) :
    ((phi05 hm hβ N v : (cp38 N).V) : SobolevCarrier38 ((0 : ℕ) : ℝ)) =
      ι0_05 m (yHead05 hm hβ N v) := rfl

theorem carrierCoe_phi05 (v : (S05 m β hm hβ).head N) (n : ℤ) :
    carrierCoe38 _ ((phi05 hm hβ N v : (cp38 N).V) : SobolevCarrier38 ((0 : ℕ) : ℝ)) n =
      (S05 m β hm hβ).hcoord (v : (S05 m β hm hβ).H) n := by
  rw [coe_phi05, carrierCoe_ι0_05, coe_yHead05]

theorem phi05_bijective : Function.Bijective (phi05 hm hβ N) := by
  constructor
  · intro v w h
    apply Subtype.ext
    apply (S05 m β hm hβ).hcoord_ext
    intro n
    have := congrArg (fun u : (cp38 N).V => carrierCoe38 _ (u : SobolevCarrier38 ((0 : ℕ) : ℝ)) n) h
    simpa only [carrierCoe_phi05] using this
  · intro u
    have hu : ∀ n ∉ symmetricModes N, carrierCoe38 _ (u : SobolevCarrier38 ((0 : ℕ) : ℝ)) n = 0 := by
      intro n hn
      have h := ((cp38 N).mem_V_iff _).1 u.2
      rw [cp38_P] at h
      have := congrArg (fun w => carrierCoe38 _ w n) h
      simp only [carrierCoe38_projC38] at this
      simp only [hn, ↓reduceIte] at this
      exact this.symm
    have hfin : {n : ℤ | carrierCoe38 _ (u : SobolevCarrier38 ((0 : ℕ) : ℝ)) n ≠ 0}.Finite :=
      (symmetricModes N).finite_toSet.subset fun n hn => by
        by_contra h; exact hn (hu n h)
    refine ⟨⟨(S05 m β hm hβ).hOfFinSeq _ hfin, fun n hn => ?_⟩, ?_⟩
    · exact hu n hn
    · apply Subtype.ext
      apply carrierExt38
      funext n
      rw [carrierCoe_phi05]
      rfl


/-- Coordinates of the derivative of `ψ_N = P_N T P_N` on the head. -/
theorem hcoord_fderiv_psi05 (v w : (S05 m β hm hβ).head N) (n : ℤ) :
    (S05 m β hm hβ).hcoord
      (((fderiv ℝ (fun w : (S05 m β hm hβ).head N =>
          w + (S05 m β hm hβ).truncField (K05 B O hm hβ) N w) v) w :
          (S05 m β hm hβ).head N) : (S05 m β hm hβ).H) n =
      if n ∈ symmetricModes N then
        carrierCoe38 ((0 : ℕ) : ℝ) (fderiv ℝ (B.TC 0) (ι0_05 m (yHead05 hm hβ N v))
          (ι0_05 m (yHead05 hm hβ N w))) n else 0 := by
  have hK2 : ContDiff ℝ 2 (K05 B O hm hβ) := (analytic_K05 B O hm hβ).contDiff
  have hg := ((S05 m β hm hβ).contDiff_truncField (K05 B O hm hβ) hK2 N).differentiable
    (by norm_num) v
  have hψ : HasFDerivAt (fun w : (S05 m β hm hβ).head N =>
      w + (S05 m β hm hβ).truncField (K05 B O hm hβ) N w)
      (ContinuousLinearMap.id ℝ _ + fderiv ℝ ((S05 m β hm hβ).truncField (K05 B O hm hβ) N) v) v :=
    (hasFDerivAt_id v).add hg.hasFDerivAt
  have h3 : fderiv ℝ (fun w : (S05 m β hm hβ).head N =>
      w + (S05 m β hm hβ).truncField (K05 B O hm hβ) N w) v = _ := hψ.fderiv
  rw [h3, (S05 m β hm hβ).fderiv_truncField (K05 B O hm hβ) hK2 N v]
  show (S05 m β hm hβ).hcoord ((w : (S05 m β hm hβ).H) +
      (((S05 m β hm hβ).cmTrunc N (fderiv ℝ (K05 B O hm hβ) ((S05 m β hm hβ).headToE N v)
        ((S05 m β hm hβ).headToE N w)) : (S05 m β hm hβ).head N) : (S05 m β hm hβ).H)) n = _
  rw [(S05 m β hm hβ).hcoord_add, (S05 m β hm hβ).hcoord_cmTrunc]
  by_cases hn : n ∈ symmetricModes N
  · simp only [hn, ↓reduceIte]
    rw [hcoord_fderiv_K05 B O hm hβ]
    have hc := B.fderiv_TC_compat_coe 0 (m - 1) (Nat.zero_le _) (yHead05 hm hβ N v)
      (yHead05 hm hβ N w)
    have hw : carrierCoe38 _ ((Eq05 m β hm hβ).symm ((S05 m β hm hβ).headToE N w)) n =
        (S05 m β hm hβ).hcoord (w : (S05 m β hm hβ).H) n := coe_yHead05 hm hβ N w n
    rw [hw]
    show _ + (carrierCoe38 _ (fderiv ℝ (B.TC (m - 1)) (yHead05 hm hβ N v) (yHead05 hm hβ N w)) n -
      _) = carrierCoe38 _ (fderiv ℝ (B.TC 0) (ι0_05 m (yHead05 hm hβ N v))
        (ι0_05 m (yHead05 hm hβ N w))) n
    unfold ι0_05
    rw [hc]
    ring
  · simp only [hn, ↓reduceIte]
    rw [w.2 n hn]; ring


theorem baseN_yHead05 (v : (S05 m β hm hβ).head N) :
    baseN38 (ι1_05 m hm (yHead05 hm hβ N v)) N = ι0_05 m (yHead05 hm hβ N v) := by
  apply carrierExt38
  funext n
  unfold baseN38 i10_38
  rw [carrierCoe38_incl38, carrierCoe38_projC38, carrierCoe_ι1_05, carrierCoe_ι0_05]
  split_ifs with hn
  · rfl
  · exact (coe_yHead05_zero hm hβ N v n hn).symm

/-- **F05.05 (bridge).** `det ψ_N'(v) = det L_N` (F01's `detLN` at `x = ι y`, `y = 𝓕`-side carrier
element of the head vector `v`). -/
theorem det_fderiv_psi05 (v : (S05 m β hm hβ).head N) :
    (fderiv ℝ (fun w : (S05 m β hm hβ).head N =>
        w + (S05 m β hm hβ).truncField (K05 B O hm hβ) N w) v).det =
      B.detLN (ι1_05 m hm (yHead05 hm hβ N v)) N := by
  set f := fderiv ℝ (fun w : (S05 m β hm hβ).head N =>
        w + (S05 m β hm hβ).truncField (K05 B O hm hβ) N w) v with hf
  set e := LinearEquiv.ofBijective (phi05 hm hβ N) (phi05_bijective hm hβ N) with he
  have key : ∀ w, e (f w) = B.LNmap (ι1_05 m hm (yHead05 hm hβ N v)) N (e w) := by
    intro w
    apply Subtype.ext
    apply carrierExt38
    funext n
    have h1 : carrierCoe38 _ ((e (f w) : (cp38 N).V) : SobolevCarrier38 ((0 : ℕ) : ℝ)) n =
        (S05 m β hm hβ).hcoord ((f w : (S05 m β hm hβ).head N) : (S05 m β hm hβ).H) n :=
      carrierCoe_phi05 hm hβ N (f w) n
    rw [h1, hf, hcoord_fderiv_psi05 B O hm hβ N v w n]
    have h2 : ((B.LNmap (ι1_05 m hm (yHead05 hm hβ N v)) N (e w) : (cp38 N).V) :
        SobolevCarrier38 ((0 : ℕ) : ℝ)) =
        projC38 _ N (B.LxN (ι1_05 m hm (yHead05 hm hβ N v)) N ((e w : (cp38 N).V) :
          SobolevCarrier38 ((0 : ℕ) : ℝ))) := by
      have hP := ((cp38 N).mem_V_iff _).1 (e w).2
      show (cp38 N).Lt (B.LxN _ N) _ = _
      rw [CplxProj38.Lt_apply]
      have hP' : (cp38 N).P ((cp38 N).V.subtype (e w)) = ((e w : (cp38 N).V) :
          SobolevCarrier38 ((0 : ℕ) : ℝ)) := hP
      rw [hP']
      rfl
    rw [h2, carrierCoe38_projC38]
    have h3 : ((e w : (cp38 N).V) : SobolevCarrier38 ((0 : ℕ) : ℝ)) =
        ι0_05 m (yHead05 hm hβ N w) := rfl
    have h4 : B.LxN (ι1_05 m hm (yHead05 hm hβ N v)) N = fderiv ℝ (B.TC 0)
        (ι0_05 m (yHead05 hm hβ N v)) := by
      unfold BirkhoffInput38.LxN BirkhoffInput38.Lop
      rw [baseN_yHead05]
    rw [h3, h4]
  have hconj : (e : (S05 m β hm hβ).head N →ₗ[ℝ] (cp38 N).V) ∘ₗ (f : (S05 m β hm hβ).head N →ₗ[ℝ]
      (S05 m β hm hβ).head N) ∘ₗ (e.symm : (cp38 N).V →ₗ[ℝ] (S05 m β hm hβ).head N) =
      B.LNmap (ι1_05 m hm (yHead05 hm hβ N v)) N := by
    apply LinearMap.ext
    intro u
    have := key (e.symm u)
    simpa using this
  have hd := LinearMap.det_conj (f : (S05 m β hm hβ).head N →ₗ[ℝ] (S05 m β hm hβ).head N) e
  rw [hconj] at hd
  exact hd.symm

end Head


theorem detLN_eq_of_baseN (B : BirkhoffInput38) (x x' : H1_38) (N : ℕ)
    (h : baseN38 x N = baseN38 x' N) : B.detLN x N = B.detLN x' N := by
  have hLx : B.LxN x N = B.LxN x' N := by
    unfold BirkhoffInput38.LxN BirkhoffInput38.Lop
    rw [h]
  have hL : B.LNmap x N = B.LNmap x' N := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    show (cp38 N).Lt (B.LxN x N) u = (cp38 N).Lt (B.LxN x' N) u
    rw [hLx]
  unfold BirkhoffInput38.detLN
  rw [hL]

section Tendsto2

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B)
  {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- **F05.05.** `|det ψ_N'(x_N)| → 1` for every sample with realization `R z` (F01). -/
theorem tendsto_det05 (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, (S05 m β hm hβ).coord n ((S05 m β hm hβ).R z) = z n) :
    Tendsto (fun N : ℕ => |(fderiv ℝ (fun w : (S05 m β hm hβ).head N =>
        w + (S05 m β hm hβ).truncField (K05 B O hm hβ) N w)
        ((S05 m β hm hβ).headPt N z)).det|) atTop (𝓝 1) := by
  set y := (Eq05 m β hm hβ).symm ((S05 m β hm hβ).R z) with hy
  have hyc : ∀ n, carrierCoe38 _ y n = z n := fun n => by
    have := coord_Eq05 m β hm hβ y n
    rw [hy, LinearIsometryEquiv.apply_symm_apply] at this
    rw [← this, hz n]
  have hsq := B.tendsto_sq_detLN O (ι1_05 m hm y)
  have h1 : ∀ N : ℕ, B.detLN (ι1_05 m hm (yHead05 hm hβ N ((S05 m β hm hβ).headPt N z))) N =
      B.detLN (ι1_05 m hm y) N := by
    intro N
    apply detLN_eq_of_baseN
    rw [baseN_yHead05]
    apply carrierExt38
    funext n
    unfold baseN38 i10_38
    simp only [carrierCoe_ι0_05, carrierCoe38_incl38, carrierCoe38_projC38, carrierCoe_ι1_05,
      coe_yHead05, (S05 m β hm hβ).hcoord_headPt, hyc]
  have h2 := (Real.continuous_sqrt.tendsto 1).comp hsq
  rw [Real.sqrt_one] at h2
  refine h2.congr (fun N => ?_)
  simp only [Function.comp, Real.sqrt_sq_eq_abs, abs_abs]
  rw [det_fderiv_psi05 B O hm hβ N, h1]

end Tendsto2

end NlsGge.Birkhoff
