import Mathlib
import QuantumNLS.RB01Bridge
import QuantumNLS.RootDiscriminantL1

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-22: the boundary determinant criterion (source
`collective_actions.tex:375`: "For real fields the boundary determinant criterion and self-adjointness identify these
zeros with the eigenvalues of the rank-two restriction").

For any potential `u ∈ L²(0, L)` (interval model of DEF-049), any parity `σ = ±1` and any `λ ∈ ℂ`:
`λ` is an eigenvalue of the actual operator `𝓛_u` on `D_σ` (graph `LocalSpectral.LuGraph`) iff
`tr M_L(λ) = 2σ`, where `M_x(λ) = L1SpatialTransfer.transfer (balCoef κ u λ) x` is the actual DEF-013/DEF-014
fundamental matrix (`det M = 1`, `RootDiscriminantL1.det_transfer`).
* `lop_inv`: `𝓛`-eigen equation at a point ⇔ the balanced spatial equation `g' = A_λ g` (`2iJ` is invertible);
* `sol_eq_transfer`: an `H¹` solution of `g' = A g` a.e. is `g(x) = M_x g(0)` on `[0, L]` (uniqueness for the actual
  Volterra equation, `L1SpatialTransfer.eq_zero_of_integral`, applied to the column matrix of `g`);
* **`eigen_iff_trace`** (interval model) and **`eigen_iff_disc`** (physical carrier: `u = circleRep v`,
  `L2SpatialTransfer.discriminant κ v λ = 2σ`). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Interval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

local instance instPMRB01Det : TopologicalSpace.PseudoMetrizableSpace QuantumNLS.SpatialTransfer.Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance instENRB01Det : ENormedAddMonoid QuantumNLS.SpatialTransfer.Mat2 :=
  NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RB01Det

open QuantumNLS.LocalSpectral (E2 H2 μI vec2 lopPt Jm LuGraph IsH1Rep lopPt_of_spatial coef_mulVec)
open QuantumNLS.SpatialTransfer (Mat2 balCoef coef)
open QuantumNLS.L1SpatialTransfer (transfer transfer_integral_eq eq_zero_of_integral continuousOn_transfer)

/-! ## Pointwise algebra -/

theorem lop_inv (κ : ℝ) (w z : ℂ) (d g : E2) (h : lopPt κ w d g = z • g) :
    d 0 = -(Complex.I * z) / 2 * g 0 + (Real.sqrt κ : ℂ) * conj w * g 1 ∧
    d 1 = (Real.sqrt κ : ℂ) * w * g 0 + Complex.I * z / 2 * g 1 := by
  have h0 := congrArg (fun v : E2 => v 0) h
  have h1 := congrArg (fun v : E2 => v 1) h
  simp only [lopPt, Jm, vec2, PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul] at h0 h1
  have hI := Complex.I_sq
  constructor
  · linear_combination (-(Complex.I) / 2) * h0 + (d 0 - (Real.sqrt κ : ℂ) * conj w * g 1) * hI
  · linear_combination (Complex.I / 2) * h1 + (d 1 - (Real.sqrt κ : ℂ) * w * g 0) * hI

/-- `A *ᵥ v` as an `E2` vector. -/
def mv (M : Mat2) (v : E2) : E2 := WithLp.toLp 2 (M.mulVec (WithLp.ofLp v))

theorem mv_apply (M : Mat2) (v : E2) (i : Fin 2) : mv M v i = (M.mulVec (WithLp.ofLp v)) i := rfl

theorem balCoef_mv (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) (v : E2) :
    mv (balCoef κ u z x) v 0 = -(Complex.I * z) / 2 * v 0 + (Real.sqrt κ : ℂ) * conj (u x) * v 1 ∧
    mv (balCoef κ u z x) v 1 = (Real.sqrt κ : ℂ) * u x * v 0 + Complex.I * z / 2 * v 1 := by
  have he : WithLp.ofLp v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  have hc := coef_mulVec κ u z (v 0) (v 1) x
  rw [mv_apply, mv_apply, he, hc]
  exact ⟨rfl, rfl⟩

theorem lop_mv (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) (v : E2) :
    lopPt κ (u x) (mv (balCoef κ u z x) v) v = z • v := by
  have hv : v = vec2 (v 0) (v 1) := by
    ext i; fin_cases i <;> rfl
  obtain ⟨h0, h1⟩ := balCoef_mv κ u z x v
  conv_rhs => rw [hv]
  conv_lhs => rw [show v = vec2 (v 0) (v 1) from hv]
  rw [show mv (balCoef κ u z x) (vec2 (v 0) (v 1)) = vec2 (mv (balCoef κ u z x) v 0) (mv (balCoef κ u z x) v 1) by
    rw [← hv]; ext i; fin_cases i <;> rfl]
  exact lopPt_of_spatial κ z (u x) (v 0) (v 1) _ _ h0 h1

theorem lop_eq_mv (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) (d v : E2) (h : lopPt κ (u x) d v = z • v) :
    d = mv (balCoef κ u z x) v := by
  obtain ⟨h0, h1⟩ := lop_inv κ (u x) z d v h
  obtain ⟨e0, e1⟩ := balCoef_mv κ u z x v
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; rw [h0, e0]
  · simp only [Fin.mk_one, Fin.isValue]; rw [h1, e1]

/-! ## Column matrices -/

/-- The column matrix `[v, v]` (both columns equal to `v`). -/
def colL : E2 →L[ℂ] Mat2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Matrix.of fun i _ => v i
      map_add' := fun v w => by ext i j; simp
      map_smul' := fun c v => by ext i j; simp }

theorem colL_apply (v : E2) (i j : Fin 2) : colL v i j = v i := rfl

theorem colL_mv (M : Mat2) (v : E2) : colL (mv M v) = M * colL v := by
  ext i j
  simp only [colL_apply, mv_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- `M ↦ M *ᵥ c` as a bounded linear map `Mat2 → E2`. -/
def evL (c : Fin 2 → ℂ) : Mat2 →L[ℂ] E2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => WithLp.toLp 2 (M.mulVec c)
      map_add' := fun M N => by rw [Matrix.add_mulVec, WithLp.toLp_add]
      map_smul' := fun a M => by rw [Matrix.smul_mulVec, WithLp.toLp_smul]; rfl }

theorem evL_apply (c : Fin 2 → ℂ) (M : Mat2) : evL c M = WithLp.toLp 2 (M.mulVec c) := rfl

/-! ## Uniqueness: solutions are `M_x g(0)` -/

variable {L : ℝ}

theorem sol_eq_transfer (hL : 0 ≤ L) {A : ℝ → Mat2} (hA : IntervalIntegrable A volume 0 L)
    {g h : ℝ → E2} (hh : IntervalIntegrable h volume 0 L)
    (hg : ∀ x ∈ Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s)
    (hae : ∀ᵐ s ∂volume, s ∈ Ioc 0 L → h s = mv (A s) (g s)) :
    ∀ x ∈ Icc 0 L, g x = mv (transfer A x) (g 0) := by
  -- continuity of g on [0, L]
  have hgc : ContinuousOn g (Icc 0 L) := by
    have hc := intervalIntegral.continuousOn_primitive_interval ((intervalIntegrable_iff' (by finiteness)).mp hh)
    rw [uIcc_of_le hL] at hc
    exact (continuousOn_const.add hc).congr fun x hx => hg x hx
  set G : ℝ → Mat2 := fun x => colL (g x) with hG
  set T : ℝ → Mat2 := transfer A with hT
  have hTc : ContinuousOn T (Icc 0 L) := continuousOn_transfer hL hA
  have hGc : ContinuousOn G (Icc 0 L) := colL.continuous.comp_continuousOn hgc
  have hAG : IntervalIntegrable (fun s => A s * G s) volume 0 L :=
    hA.mul_continuousOn (by rwa [uIcc_of_le hL])
  have hAT : IntervalIntegrable (fun s => A s * T s) volume 0 L :=
    hA.mul_continuousOn (by rwa [uIcc_of_le hL])
  set R : Mat2 →L[ℂ] Mat2 := (ContinuousLinearMap.mul ℂ Mat2).flip (G 0) with hR
  have key : ∀ x ∈ Icc 0 L, G x - T x * G 0 = ∫ s in (0 : ℝ)..x, A s * (G s - T s * G 0) := by
    intro x hx
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc 0 L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
    have hhx := hh.mono_set hsub
    have hAGx := hAG.mono_set hsub
    have hATx := hAT.mono_set hsub
    have e1 : G x = G 0 + ∫ s in (0 : ℝ)..x, A s * G s := by
      have h1 : G x = colL (g 0) + colL (∫ s in (0 : ℝ)..x, h s) := by
        simp only [hG]; rw [hg x hx, map_add]
      have hc : ∫ s in (0 : ℝ)..x, colL (h s) = colL (∫ s in (0 : ℝ)..x, h s) :=
        colL.intervalIntegral_comp_comm hhx
      rw [h1, ← hc]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with s hs hsI
      rw [uIoc_of_le hx.1] at hsI
      rw [hs ⟨hsI.1, hsI.2.trans hx.2⟩, colL_mv]
    have e2 : T x = 1 + ∫ s in (0 : ℝ)..x, A s * T s := transfer_integral_eq hL hA hx
    have e3 : (∫ s in (0 : ℝ)..x, A s * T s) * G 0 = ∫ s in (0 : ℝ)..x, A s * T s * G 0 := by
      have := R.intervalIntegral_comp_comm hATx
      simpa [hR] using this.symm
    have hATG : IntervalIntegrable (fun s => A s * T s * G 0) volume 0 x := hATx.mul_const (G 0)
    rw [e1, e2, add_mul, one_mul, e3, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hAGx hATG]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [mul_sub, mul_assoc]
  have hz := eq_zero_of_integral hL hA (f := fun x => G x - T x * G 0) (hGc.sub (hTc.mul continuousOn_const)) key
  intro x hx
  have h0 := hz x hx
  have hcol : G x = T x * G 0 := sub_eq_zero.1 h0
  ext i
  have := congrFun (congrFun hcol i) 0
  simp only [hG, colL_apply] at this
  rw [this, mv_apply]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, colL_apply]

/-! ## The criterion -/

theorem det_sub_smul (M : Mat2) (c : ℂ) : (M - c • 1).det = M.det - c * M.trace + c ^ 2 := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_mul, mul_one, mul_zero, sub_zero]
  ring

theorem sigma_sq (σ : ℤˣ) : (((σ : ℤ) : ℂ)) ^ 2 = 1 := by
  rcases Int.units_eq_one_or σ with h | h <;> simp [h]

theorem interval_of_memLp {E : Type*} [NormedAddCommGroup E] {u : ℝ → E} (hL : 0 ≤ L)
    (hu : MemLp u 2 (μI L)) : IntervalIntegrable u volume 0 L := by
  have h1 : MemLp u 1 (μI L) := hu.mono_exponent (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
  exact memLp_one_iff_integrable.1 h1

theorem norm_mv_le (κ : ℝ) (u : ℝ → ℂ) (lam : ℂ) (x : ℝ) (v : E2) :
    ‖mv (balCoef κ u lam x) v‖ ≤ 2 * (‖lam‖ + Real.sqrt κ * ‖u x‖) * ‖v‖ := by
  obtain ⟨h0, h1⟩ := balCoef_mv κ u lam x v
  have hv0 : ‖v 0‖ ≤ ‖v‖ := PiLp.norm_apply_le v 0
  have hv1 : ‖v 1‖ ≤ ‖v‖ := PiLp.norm_apply_le v 1
  set K := ‖lam‖ + Real.sqrt κ * ‖u x‖ with hK
  have hk : 0 ≤ Real.sqrt κ * ‖u x‖ := by positivity
  have hsk : ‖(Real.sqrt κ : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hI : ‖Complex.I * lam / 2‖ ≤ ‖lam‖ := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_two]; linarith [norm_nonneg lam]
  have hI' : ‖-(Complex.I * lam) / 2‖ ≤ ‖lam‖ := by rw [neg_div, norm_neg]; exact hI
  have c0 : ‖mv (balCoef κ u lam x) v 0‖ ≤ K * ‖v‖ := by
    rw [h0]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, hsk, Complex.norm_conj]
    have := mul_le_mul hI' hv0 (norm_nonneg _) (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left hv1 hk
    nlinarith
  have c1 : ‖mv (balCoef κ u lam x) v 1‖ ≤ K * ‖v‖ := by
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, hsk]
    have := mul_le_mul hI hv1 (norm_nonneg _) (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left hv0 hk
    nlinarith
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hK0 : 0 ≤ K * ‖v‖ := by positivity
  rw [Real.sqrt_le_left]
  · have e0 := mul_le_mul c0 c0 (norm_nonneg _) hK0
    have e1 := mul_le_mul c1 c1 (norm_nonneg _) hK0
    nlinarith
  · positivity

/-- **Boundary determinant criterion** (interval model). -/
theorem eigen_iff_trace (hL : 0 < L) (κ : ℝ) {u : ℝ → ℂ} (hu : MemLp u 2 (μI L)) (σ : ℤˣ) (lam : ℂ) :
    (∃ f : H2 L, f ≠ 0 ∧ (f, lam • f) ∈ LuGraph L κ u σ) ↔
      Matrix.trace (transfer (balCoef κ u lam) L) = 2 * ((σ : ℤ) : ℂ) := by
  have hu1 := interval_of_memLp hL.le hu
  have hA := QuantumNLS.RootDiscriminantL1.intervalIntegrable_balCoef hu1 κ lam
  have hdet : (transfer (balCoef κ u lam) L).det = 1 :=
    QuantumNLS.RootDiscriminantL1.det_transfer hL.le hu1 κ lam ⟨hL.le, le_rfl⟩
  have hs2 := sigma_sq σ
  set s : ℂ := ((σ : ℤ) : ℂ) with hsdef
  set T : ℝ → Mat2 := transfer (balCoef κ u lam) with hTdef
  have hT0 : T 0 = 1 := by
    have := transfer_integral_eq hL.le hA (x := 0) ⟨le_rfl, hL.le⟩
    rw [intervalIntegral.integral_same, add_zero] at this
    exact this
  have hμ : μI L ≠ 0 := by
    unfold μI
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioc, sub_zero, ENNReal.ofReal_eq_zero, not_le]
    exact hL
  constructor
  · rintro ⟨f, hf0, g, h, ⟨hfg, hh2, hgint⟩, hbd, hae⟩
    have hsm : ((lam • f : H2 L) : ℝ → E2) =ᵐ[μI L] fun x => lam • g x := by
      filter_upwards [Lp.coeFn_smul lam f, hfg] with x h1 h2
      rw [h1, Pi.smul_apply, h2]
    have hae' : ∀ᵐ x ∂(μI L), h x = mv (balCoef κ u lam x) (g x) := by
      filter_upwards [hsm, hae] with x h1 h2
      exact lop_eq_mv κ u lam x (h x) (g x) (by rw [← h2, h1])
    have hae'' : ∀ᵐ x ∂volume, x ∈ Ioc 0 L → h x = mv (balCoef κ u lam x) (g x) := by
      have := hae'
      unfold μI at this
      exact (ae_restrict_iff' measurableSet_Ioc).1 this
    have hh1 : IntervalIntegrable h volume 0 L := interval_of_memLp hL.le hh2
    have hsol := sol_eq_transfer hL.le hA hh1 hgint hae''
    have hg0 : g 0 ≠ 0 := by
      intro h0
      apply hf0
      rw [Lp.eq_zero_iff_ae_eq_zero]
      have hz : ∀ᵐ x ∂(μI L), g x = 0 := by
        unfold μI
        rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall fun x hx => ?_
        rw [hsol x ⟨hx.1.le, hx.2⟩, h0]
        ext i
        simp [mv_apply, Matrix.mulVec]
      filter_upwards [hfg, hz] with x h1 h2
      rw [h1, h2]
      rfl
    have hLs := hsol L ⟨hL.le, le_rfl⟩
    rw [hbd] at hLs
    have heig : (T L - s • 1).mulVec (WithLp.ofLp (g 0)) = 0 := by
      have h1 := congrArg WithLp.ofLp hLs
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      change WithLp.ofLp (s • g 0) = (T L).mulVec (WithLp.ofLp (g 0)) at h1
      rw [← h1]
      simp
    have hne : WithLp.ofLp (g 0) ≠ 0 := fun h0 => hg0 (by
      have := congrArg (WithLp.toLp 2) h0
      simpa using this)
    have hdet0 : (T L - s • 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, heig⟩
    rw [det_sub_smul, hdet] at hdet0
    linear_combination (-s) * hdet0 + (-(Matrix.trace (T L) - s)) * hs2
  · intro htr
    have hdet0 : (T L - s • 1).det = 0 := by
      rw [det_sub_smul, hdet]
      change 1 - s * Matrix.trace (T L) + s ^ 2 = 0
      rw [htr]
      linear_combination (-1 : ℂ) * hs2
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
    have hTc : ContinuousOn T (Icc 0 L) := continuousOn_transfer hL.le hA
    set gf : ℝ → E2 := fun x => evL c (T x) with hgf
    set hf : ℝ → E2 := fun x => mv (balCoef κ u lam x) (gf x) with hhf
    have hgc : ContinuousOn gf (Icc 0 L) := (evL c).continuous.comp_continuousOn hTc
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
    have hgm : AEStronglyMeasurable gf (μI L) := by
      unfold μI
      exact (hgc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    have hgb : ∀ᵐ x ∂(μI L), ‖gf x‖ ≤ C := by
      unfold μI
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun x hx => hC x ⟨hx.1.le, hx.2⟩
    have hgL : MemLp gf 2 (μI L) := MemLp.of_bound hgm C hgb
    have hAm : AEStronglyMeasurable (balCoef κ u lam) (μI L) := hA.1.aestronglyMeasurable
    have hmvc : Continuous (Function.uncurry mv) := by
      unfold Function.uncurry mv
      fun_prop
    have hhm : AEStronglyMeasurable hf (μI L) := hmvc.comp_aestronglyMeasurable₂ hAm hgm
    have hdom : MemLp (fun x => 2 * C * (‖lam‖ + Real.sqrt κ * ‖u x‖)) 2 (μI L) :=
      ((memLp_const (‖lam‖)).add (hu.norm.const_mul (Real.sqrt κ))).const_mul (2 * C)
    have hhL : MemLp hf 2 (μI L) := by
      refine hdom.of_le hhm ?_
      filter_upwards [hgb] with x hx
      have h1 := norm_mv_le κ u lam x (gf x)
      have hp : 0 ≤ ‖lam‖ + Real.sqrt κ * ‖u x‖ := by positivity
      rw [Real.norm_eq_abs]
      calc ‖hf x‖ ≤ 2 * (‖lam‖ + Real.sqrt κ * ‖u x‖) * ‖gf x‖ := h1
        _ ≤ 2 * C * (‖lam‖ + Real.sqrt κ * ‖u x‖) := by nlinarith [norm_nonneg (gf x)]
        _ ≤ |2 * C * (‖lam‖ + Real.sqrt κ * ‖u x‖)| := le_abs_self _
    -- the integral equation
    have hint : ∀ x ∈ Icc 0 L, gf x = gf 0 + ∫ t in (0 : ℝ)..x, hf t := by
      intro x hx
      have hsub : uIcc (0 : ℝ) x ⊆ uIcc 0 L := by
        rw [uIcc_of_le hx.1, uIcc_of_le hL.le]; exact Icc_subset_Icc_right hx.2
      have hATx : IntervalIntegrable (fun t => balCoef κ u lam t * T t) volume 0 x :=
        (hA.mul_continuousOn (by rwa [uIcc_of_le hL.le])).mono_set hsub
      have hc1 : ∫ t in (0 : ℝ)..x, evL c (balCoef κ u lam t * T t) =
          evL c (∫ t in (0 : ℝ)..x, balCoef κ u lam t * T t) := (evL c).intervalIntegral_comp_comm hATx
      have hev : ∀ t, evL c (balCoef κ u lam t * T t) = hf t := by
        intro t
        simp only [hhf, hgf, evL_apply, mv, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]
      have e2 : T x = 1 + ∫ t in (0 : ℝ)..x, balCoef κ u lam t * T t := transfer_integral_eq hL.le hA hx
      simp only [hgf]
      rw [e2, map_add, ← hc1, hT0]
      congr 1
      exact intervalIntegral.integral_congr fun t _ => hev t
    have hgf0 : gf 0 = WithLp.toLp 2 c := by
      simp only [hgf, evL_apply, hT0, Matrix.one_mulVec]
    have hMc : (T L).mulVec c = s • c := by
      have := hc
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    refine ⟨hgL.toLp gf, ?_, gf, hf, ⟨hgL.coeFn_toLp, hhL, hint⟩, ?_, ?_⟩
    · intro hF
      rw [Lp.eq_zero_iff_ae_eq_zero] at hF
      have hg0ae : gf =ᵐ[μI L] 0 := hgL.coeFn_toLp.symm.trans hF
      have hh0ae : ∀ᵐ t ∂volume, t ∈ Ioc 0 L → hf t = 0 := by
        have : ∀ᵐ t ∂(μI L), hf t = 0 := by
          filter_upwards [hg0ae] with t ht
          simp only [hhf, ht, Pi.zero_apply]
          ext i
          simp [mv_apply, Matrix.mulVec]
        unfold μI at this
        exact (ae_restrict_iff' measurableSet_Ioc).1 this
      have hconst : ∀ x ∈ Ioc 0 L, gf x = gf 0 := by
        intro x hx
        rw [hint x ⟨hx.1.le, hx.2⟩]
        have : ∫ t in (0 : ℝ)..x, hf t = ∫ t in (0 : ℝ)..x, (0 : E2) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards [hh0ae] with t ht htI
          rw [uIoc_of_le hx.1.le] at htI
          exact ht ⟨htI.1, htI.2.trans hx.2⟩
        rw [this, intervalIntegral.integral_zero, add_zero]
      have hz : ∀ᵐ x ∂(μI L), gf 0 = 0 := by
        have hin : ∀ᵐ x ∂(μI L), x ∈ Ioc 0 L := by
          unfold μI
          exact ae_restrict_mem measurableSet_Ioc
        filter_upwards [hg0ae, hin] with x h1 h2
        rw [← hconst x h2]
        exact h1
      have : (ae (μI L)).NeBot := ae_neBot.2 hμ
      obtain ⟨x, hx⟩ := hz.exists
      apply hc0
      have := congrArg WithLp.ofLp hx
      rw [hgf0] at this
      simpa using this
    · show gf L = s • gf 0
      simp only [hgf, evL_apply, hMc, hT0, Matrix.one_mulVec, WithLp.toLp_smul]
    · show ((lam • hgL.toLp gf : H2 L) : ℝ → E2) =ᵐ[μI L] fun x => lopPt κ (u x) (hf x) (gf x)
      filter_upwards [Lp.coeFn_smul lam (hgL.toLp gf), hgL.coeFn_toLp] with x h1 h2
      rw [h1, Pi.smul_apply, h2, hhf]
      exact (lop_mv κ u lam x (gf x)).symm

/-- **Boundary determinant criterion on the physical carrier**: for `v ∈ L²(𝕋_L)`, `λ` is an eigenvalue of `𝓛_v` on
`D_σ` iff `Δ_v(λ) = 2σ` (`L2SpatialTransfer.discriminant`, DEF-014). -/
theorem eigen_iff_disc [Fact (0 < L)] (κ : ℝ) (v : QuantumNLS.PhysicalTensor.L2T L) (σ : ℤˣ) (lam : ℂ) :
    (∃ f : H2 L, f ≠ 0 ∧ (f, lam • f) ∈ LuGraph L κ (QuantumNLS.LocalSpectral.circleRep v) σ) ↔
      QuantumNLS.L2SpatialTransfer.discriminant κ v lam = 2 * ((σ : ℤ) : ℂ) := by
  have hL : 0 < L := Fact.out
  have hu : MemLp (QuantumNLS.LocalSpectral.circleRep v) 2 (μI L) :=
    (Lp.memLp (QuantumNLS.Local002Bridge.toInterval L v)).ae_eq (QuantumNLS.Local002Bridge.toInterval_coe L v)
  rw [eigen_iff_trace hL κ hu σ lam]
  rfl

end QuantumNLS.RB01Det

#print axioms QuantumNLS.RB01Det.sol_eq_transfer
#print axioms QuantumNLS.RB01Det.eigen_iff_trace
#print axioms QuantumNLS.RB01Det.eigen_iff_disc
