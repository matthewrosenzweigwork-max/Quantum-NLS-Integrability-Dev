import QuantumNLS.Prop020Link
import QuantumNLS.Prop026Uniform
import QuantumNLS.Prop010ContourBindingR11

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O3e:
the eigenvalue of the combined leading operator `C_{0,N}(t,θ)` (eq:MP-C0) on the actual Bethe vectors.

Source (mixed_propagation.tex:300-345): `C_{0,N}(t,θ) = −(2πκ)⁻¹ Re(∮_{Γ_a} p_t f_z(S_N) dz + Σ_n θ_n ∮_{Γ_n} f_z(S_N) dz)`;
"These inequalities are obtained by summing the corresponding uniform eigenvalue inequalities".

The PROP-026 operator (`Prop026Mixed.mixedGap`, accepted) is `C0op (nu (6 + nf)) (S_N ∘ z_θ) u_θ g_θ` over the parameter space of
`P = Fin.append (rectPieces a h ω) Pf`.  For the fixed family `Pf = rectFamily xm xp hf θ` (the literal six pieces of
`∂([x₋,x₊]×[−h_f,h_f])` with constant weight `θ_i`, accepted `Prop026Uniform.rectFamily`):

* `int_re`: the scalar integrand `θ ↦ Re(u_θ g_θ(λ_θ))` is `ν`-integrable on any family (the operator-family integrability of the
  accepted `Prop020Link.C0_eig`, copied, composed with the bounded functional `X ↦ ⟪v, X v⟫`);
* `integral_nu_split`: `∫ f dν = Σ_i ∫_0^1 f(i,·)` for integrable `f`;
* `pieces_sum_gen`, `theta_integral_rectGen`: the six pieces of `MPFixedContour.rectGen` sum to the rectangle integral
  `LabelExactPeriod.rectIntegral` (the `rectGen` analogue of the accepted `Prop020Contour.pieces_sum`/`theta_integral_rect`);
* `fixed_part`: on the fixed contours, when the roots avoid `Γ_i` and `|s_N − s| < min(r_i, rad/2)` there (chart agreement
  `fz = λ = log a_N = localLog = f_i`), the fixed-family part of the eigenvalue is `Σ_i θ_i c^{(0)}_i(m)` with the accepted
  PROP-010 eigenvalue `Prop010ContourBindingR11.c0` (the same `c0` as in the frozen O3c `count_event`);
* **`mixed_eig`**: `C0op(P) Ψ_m = (∫_{ν_6} Re(u_θ g_θ(λ_θ)) + Σ_i θ_i c^{(0)}_i(m)) Ψ_m` (window part over `nu 6` exactly in the
  form consumed by the accepted `Prop020Link.C0_identify`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop025OEigen

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.Prop017Quantum (qAct)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.LabelExactPeriod (rectIntegral)
open QuantumNLS.Prop018Phase (lam logaNf_eq_lam)
open QuantumNLS.Prop019Deviation (eigen_eq_sNf)
open QuantumNLS.Prop020Contour (piece_h piece_v integral_unitInterval)
open QuantumNLS.Prop020Link (fz fz_eq_lam)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ affinePiece continuous_zθ continuous_uθ)
open QuantumNLS.MPFamily (BgFam gθ good)
open QuantumNLS.MPChartSmooth (gfun rad)
open QuantumNLS.MPOps (C0op)
open QuantumNLS.TensorCarrier (SymSector)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.MPFixedContour (rectGen rectGen_mem_Gam rectGen_im_ne)
open QuantumNLS.Prop026Uniform (rectFamily)
open QuantumNLS.Prop010ContourBindingR11 (Extension localLog c0)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. `g_θ` depends on `θ` only through `z_θ` -/

open Classical in
/-- The chart extension at a contour point `z` (`0` on the real axis), so that `g_θ = gz (z_θ)`. -/
def gz {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (B : BgFam Z d₀ s₁ a₀ c₁) (z : ℂ) : ℂ → ℂ :=
  if z.im ≠ 0 then gfun (rad d₀ s₁ a₀) (B.c0 z) (B.D z) (B.s z) (B.A z) else fun _ => 0

theorem gθ_eq_gz {m : ℕ} {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁)
    (θ : ThetaSpace m) : gθ P B θ = gz B (zθ P θ) := by
  unfold gθ gz good
  split_ifs <;> rfl

/-- With the pinned background fields, `gz` is `fz` off the real axis. -/
theorem gz_eq_fz {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (B : BgFam Z d₀ s₁ a₀ c₁) {G : ℂ → ℂ}
    (hc0 : B.c0 = fun z => Complex.I * κ * G z) (hD : B.D = Df L κ G) (hs : B.s = sf L κ G)
    (hA : B.A = Af κ G) {z : ℂ} (hz : z.im ≠ 0) (w : ℂ) :
    gz B z w = fz L κ G (rad d₀ s₁ a₀) z w := by
  unfold gz fz
  split_ifs
  rw [hc0, hD, hs, hA]

/-! ### 2. Integrability of the scalar integrand -/

section IntRe

open QuantumNLS.MPChartBounds QuantumNLS.MPChartDeriv QuantumNLS.MPFamily QuantumNLS.MPFamilyMeas QuantumNLS.MPOps
  QuantumNLS.MixedQuadratures QuantumNLS.FunctionalLinearization QuantumNLS.MPLinearization

/-- **Integrability of `θ ↦ Re(u_θ g_θ(λ_θ))`** for a unit joint eigenvector: the operator-family integrability of the
accepted `Prop020Link.C0_eig` (copied verbatim), composed with the bounded functional `X ↦ ⟪v, X v⟫`. -/
theorem int_re (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) {m : ℕ} {Z : Set ℂ}
    {d₀ s₁ a₀ c₁ h : ℝ} (hc1 : 0 ≤ c₁) (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁)
    (hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (P i).γ τ ∈ Z) (hIm : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((P i).γ τ).im| ≤ h)
    {v : SymSector ℂ (L2T L) N} (hv1 : ‖v‖ = 1) (lam : ThetaSpace m → ℂ)
    (hv : ∀ θ, normalizedTransfer L κ N (zθ P θ) v = lam θ • v) :
    Integrable (fun θ => (uθ κ P θ * gθ P B θ (lam θ)).re) (nu m) := by
  classical
  have hz : Continuous (zθ P) := continuous_zθ P
  have hzh : ∀ θ : ThetaSpace m, |(zθ P θ).im| ≤ h := fun θ => hIm θ.1 θ.2 θ.2.2
  have hS : ∀ θ : ThetaSpace m, IsStarNormal (normalizedTransfer L κ N (zθ P θ)) :=
    fun θ => SN_isStarNormal L κ hκ N hN (zθ P θ)
  have hR : ∀ θ : ThetaSpace m, ‖normalizedTransfer L κ N (zθ P θ)‖ ≤ Rbd L κ h :=
    fun θ => norm_normalizedTransfer_le L κ N (zθ P θ) h (hzh θ)
  obtain ⟨U₁, hU₁⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_uθ κ P).continuousOn
  set U₀ : ℝ := max U₁ 0 with hU₀def
  have hU₀' : ∀ θ, ‖uθ κ P θ‖ ≤ U₀ := fun θ => (hU₁ θ (mem_univ _)).trans (le_max_left _ _)
  have hgc : ∀ θ, Continuous (gθ P B θ) := fun θ => (contDiff_gθ P B hZ θ).continuous
  have hgb : ∀ θ w, ‖gθ P B θ w‖ ≤ c₁ + 1 := norm_gθ_le P B hZ hc1
  have hBm : ∀ j, AEStronglyMeasurable (fun θ => quadHom (normalizedTransfer L κ N (zθ P θ)) (hS θ)
      (Rbd L κ h) (hR θ) (coordC (d := 2) (K := Kdisc (Rbd L κ h)) j)) (nu m) :=
    fun j => PhiFam_hB hκ hN (nu m) (zθ P) hz (Rbd L κ h) hR j
  have hF1 : AEStronglyMeasurable
      (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF (uθ κ P θ) (gθ P B θ))) (nu m) :=
    aesm_resKd κ P B hZ (Rbd L κ h)
  have hF2 : AEStronglyMeasurable
      (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))) (nu m) := by
    have := aesm_resKd κ (twist P) B (fun i τ hτ => hZ i τ hτ) (Rbd L κ h)
    have e : (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))) =
        fun θ => resKd (Kdisc (Rbd L κ h)) (Fθ κ (twist P) B θ) := by
      funext θ; unfold Fθ; rw [uθ_twist, gθ_twist]
    rw [e]; exact this
  have hC1' : ∀ θ, ‖resKd (Kdisc (Rbd L κ h)) (quadF (uθ κ P θ) (gθ P B θ))‖ ≤ U₀ * (c₁ + 1) := fun θ =>
    (norm_resKd_Fθ_le hc1 (uθ κ P θ) (Rbd L κ h) (gθ P B θ) (hgc θ) (hgb θ)).trans
      (mul_le_mul_of_nonneg_right (hU₀' θ) (by linarith))
  have hC2' : ∀ θ, ‖resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))‖ ≤ U₀ * (c₁ + 1) :=
    fun θ => (norm_resKd_Fθ_le hc1 ((-Complex.I) * uθ κ P θ) (Rbd L κ h) (gθ P B θ) (hgc θ) (hgb θ)).trans
      (by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact mul_le_mul_of_nonneg_right (hU₀' θ) (by linarith))
  have hint := QuantumNLS.Prop020Link.int_cfc_gen (nu m) (Rbd L κ h) _ hS hR _ _ hgc hBm hF1 hF2 hC1' hC2'
  -- the bounded functional `X ↦ ⟪v, X v⟫`
  set Λ : (SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) →L[ℂ] ℂ :=
    (innerSL ℂ v).comp (ContinuousLinearMap.apply ℂ (SymSector ℂ (L2T L) N) v) with hΛ
  have hv0 : v ≠ 0 := by intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1
  have hcomp' : Integrable (fun θ => uθ κ P θ * gθ P B θ (lam θ)) (nu m) := by
    refine (Λ.integrable_comp hint).congr (Eventually.of_forall fun θ => ?_)
    have he := QuantumNLS.Prop020Diag.cfc_eigen (hS θ) (hv θ) hv0 (gθ P B θ) (hgc θ).continuousOn
    simp only [hΛ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    rw [smul_apply, he, smul_smul, innerSL_apply_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hv1]
    simp
  exact hcomp'.re

end IntRe

/-! ### 3. Splitting the parameter integral -/

theorem integral_nu_split {m : ℕ} {f : ThetaSpace m → ℝ} (hf : Integrable f (nu m)) :
    ∫ θ, f θ ∂(nu m) = ∑ i : Fin m, ∫ τ : unitInterval, f (i, τ) := by
  unfold nu at hf ⊢
  rw [integral_prod _ hf, integral_count]

theorem zθ_left {m₁ m₂ : ℕ} (W : Fin m₁ → Piece) (F : Fin m₂ → Piece) (i : Fin m₁) (τ : unitInterval) :
    zθ (Fin.append W F) (Fin.castAdd m₂ i, τ) = zθ W (i, τ) := by
  simp [zθ]

theorem zθ_right {m₁ m₂ : ℕ} (W : Fin m₁ → Piece) (F : Fin m₂ → Piece) (j : Fin m₂) (τ : unitInterval) :
    zθ (Fin.append W F) (Fin.natAdd m₁ j, τ) = zθ F (j, τ) := by
  simp [zθ]

theorem uθ_left (κ : ℝ) {m₁ m₂ : ℕ} (W : Fin m₁ → Piece) (F : Fin m₂ → Piece) (i : Fin m₁) (τ : unitInterval) :
    uθ κ (Fin.append W F) (Fin.castAdd m₂ i, τ) = uθ κ W (i, τ) := by
  simp [uθ, zθ]

theorem uθ_right (κ : ℝ) {m₁ m₂ : ℕ} (W : Fin m₁ → Piece) (F : Fin m₂ → Piece) (j : Fin m₂) (τ : unitInterval) :
    uθ κ (Fin.append W F) (Fin.natAdd m₁ j, τ) = uθ κ F (j, τ) := by
  simp [uθ, zθ]

/-! ### 4. The six pieces of `rectGen` and the rectangle integral -/

theorem rectGen_ω (xm xp h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) : (rectGen xm xp h ω hω i).ω = ω := by
  fin_cases i <;> rfl

set_option linter.unusedTactic false in
/-- The six piece integrals of `rectGen` sum to the rectangle integral over `∂([x₋,x₊]×[−h,h])`. -/
theorem pieces_sum_gen {xm xp h : ℝ} (hlt : xm < xp) (hh : 0 < h) (ω : ℂ → ℂ) (hω : Continuous ω) (Φ : ℂ → ℂ)
    (hΦ : Continuous Φ) :
    ∑ i : Fin 6, ∫ τ in (0:ℝ)..1, Φ ((rectGen xm xp h ω hω i).γ τ) * (rectGen xm xp h ω hω i).γ' τ =
      rectIntegral Φ xm xp h := by
  have hc1 : (xp - xm) ≠ 0 := by intro h0; linarith
  have hc2 : (-(xp - xm)) ≠ 0 := by intro h0; linarith
  have hh0 : h ≠ 0 := hh.ne'
  have hnh : (-h) ≠ 0 := neg_ne_zero.2 hh0
  have hv : ∀ x0 : ℝ, ∀ c d : ℝ, IntervalIntegrable (fun y : ℝ => Φ (x0 + y * Complex.I)) volume c d := fun x0 c d =>
    (hΦ.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
  rw [Fin.sum_univ_six]
  change (∫ τ in (0:ℝ)..1, Φ (((xm : ℂ) - h * Complex.I) + (τ : ℂ) * (((xp : ℂ) - h * Complex.I) -
        ((xm : ℂ) - h * Complex.I))) * (((xp : ℂ) - h * Complex.I) - ((xm : ℂ) - h * Complex.I))) +
    (∫ τ in (0:ℝ)..1, Φ (((xp : ℂ) - h * Complex.I) + (τ : ℂ) * ((xp : ℂ) - ((xp : ℂ) - h * Complex.I))) *
        ((xp : ℂ) - ((xp : ℂ) - h * Complex.I))) +
    (∫ τ in (0:ℝ)..1, Φ ((xp : ℂ) + (τ : ℂ) * (((xp : ℂ) + h * Complex.I) - (xp : ℂ))) *
        (((xp : ℂ) + h * Complex.I) - (xp : ℂ))) +
    (∫ τ in (0:ℝ)..1, Φ (((xp : ℂ) + h * Complex.I) + (τ : ℂ) * (((xm : ℂ) + h * Complex.I) -
        ((xp : ℂ) + h * Complex.I))) * (((xm : ℂ) + h * Complex.I) - ((xp : ℂ) + h * Complex.I))) +
    (∫ τ in (0:ℝ)..1, Φ (((xm : ℂ) + h * Complex.I) + (τ : ℂ) * ((xm : ℂ) - ((xm : ℂ) + h * Complex.I))) *
        ((xm : ℂ) - ((xm : ℂ) + h * Complex.I))) +
    (∫ τ in (0:ℝ)..1, Φ ((xm : ℂ) + (τ : ℂ) * (((xm : ℂ) - h * Complex.I) - (xm : ℂ))) *
        (((xm : ℂ) - h * Complex.I) - (xm : ℂ))) = _
  rw [piece_h Φ _ _ (xp - xm) xm (-h) hc1 (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ h (-h) xp hh0 (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ h 0 xp hh0 (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_h Φ _ _ (-(xp - xm)) xp h hc2 (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ (-h) h xm hnh (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ (-h) 0 xm hnh (fun τ => by push_cast; ring) (by push_cast; ring)]
  unfold rectIntegral
  have e1 : xp - xm + xm = xp := by ring
  have e2 : h + -h = (0:ℝ) := by ring
  have e3 : -(xp - xm) + xp = xm := by ring
  have e4 : -h + h = (0:ℝ) := by ring
  rw [e1, e2, e3, e4, add_zero, add_zero,
    ← intervalIntegral.integral_add_adjacent_intervals (hv xp (-h) 0) (hv xp 0 h),
    ← intervalIntegral.integral_add_adjacent_intervals (hv xm (-h) 0) (hv xm 0 h),
    intervalIntegral.integral_symm xm xp,
    intervalIntegral.integral_symm 0 h, intervalIntegral.integral_symm (-h) 0]
  simp only [smul_eq_mul]
  ring

/-- **The parametrized fixed contour integral** (constant weight `c`): `Σ_k ∫_0^1 u_θ Φ(z_θ) = −(2πκ)⁻¹ c ∮ Φ dz`. -/
theorem theta_integral_rectGen {xm xp h : ℝ} (hlt : xm < xp) (hh : 0 < h) (κ : ℝ) (c : ℂ) (Φ : ℂ → ℂ)
    (hΦ : Continuous Φ) :
    ∑ k : Fin 6, ∫ τ : unitInterval, uθ κ (rectGen xm xp h (fun _ => c) continuous_const) (k, τ) *
        Φ (zθ (rectGen xm xp h (fun _ => c) continuous_const) (k, τ)) =
      -((((2 * Real.pi * κ)⁻¹ : ℝ)) : ℂ) * c * rectIntegral Φ xm xp h := by
  have hpiece : ∀ k : Fin 6, ∫ τ : unitInterval, uθ κ (rectGen xm xp h (fun _ => c) continuous_const) (k, τ) *
        Φ (zθ (rectGen xm xp h (fun _ => c) continuous_const) (k, τ)) =
      -((((2 * Real.pi * κ)⁻¹ : ℝ)) : ℂ) * c *
        ∫ τ in (0:ℝ)..1, Φ ((rectGen xm xp h (fun _ => c) continuous_const k).γ τ) *
          (rectGen xm xp h (fun _ => c) continuous_const k).γ' τ := by
    intro k
    rw [← intervalIntegral.integral_const_mul, ← integral_unitInterval]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [uθ, zθ, rectGen_ω]
    ring
  simp_rw [hpiece]
  rw [← Finset.mul_sum, pieces_sum_gen hlt hh _ continuous_const Φ hΦ]

/-! ### 5. The fixed-family part of the eigenvalue -/

/-- On a fixed contour, under root avoidance and `|s_N − s| < min(r_i, rad/2)`, `gz(z, λ_z) = f_i(z, λ_z)` (chart agreement
`fz = λ = log a_N = localLog = f_i`) off the real axis. -/
theorem gz_eq_ext (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ}
    (B : BgFam Z d₀ s₁ a₀ c₁) {G : ℂ → ℂ}
    (hc0 : B.c0 = fun z => Complex.I * κ * G z) (hD : B.D = Df L κ G) (hs : B.s = sf L κ G)
    (hA : B.A = Af κ G) (hrr : 0 < rad d₀ s₁ a₀) (f : Extension (ℂ × ℂ)) (rf : ℝ) {z : ℂ}
    (hfa : ∀ w, ‖w - sf L κ G z‖ < rf → f.value (z, w) = localLog L κ G z w)
    (hroot : ∀ j, z ≠ (qAct L κ N m j : ℂ))
    (hdev1 : ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ G z‖ < rf)
    (hdev2 : ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ G z‖ ≤ rad d₀ s₁ a₀ / 2) (hz : z.im ≠ 0) :
    gz B z (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m z) =
      f.value (z, QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m z) := by
  rw [eigen_eq_sNf hκ hN m z hroot, gz_eq_fz B hc0 hD hs hA hz, fz_eq_lam hrr hdev2,
    ← logaNf_eq_lam, hfa _ hdev1]
  rfl

/-- **The fixed-family part**: `Σ_j ∫_0^1 Re(u_θ g_θ(λ_θ)) = Σ_i θ_i c^{(0)}_i(m)`. -/
theorem fixed_part (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ}
    (B : BgFam Z d₀ s₁ a₀ c₁) {G : ℂ → ℂ}
    (hc0 : B.c0 = fun z => Complex.I * κ * G z) (hD : B.D = Df L κ G) (hs : B.s = sf L κ G)
    (hA : B.A = Af κ G) (hrr : 0 < rad d₀ s₁ a₀)
    {r : ℕ} (xm xp hf θf : Fin r → ℝ) (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i)
    (f : Fin r → Extension (ℂ × ℂ)) (rf : Fin r → ℝ)
    (hfa : ∀ i, ∀ z ∈ Gam (xm i) (xp i) (hf i), ∀ w, ‖w - sf L κ G z‖ < rf i →
      (f i).value (z, w) = localLog L κ G z w)
    (hroot : ∀ i, ∀ z ∈ Gam (xm i) (xp i) (hf i), ∀ j, z ≠ (qAct L κ N m j : ℂ))
    (hdev : ∀ i, ∀ z ∈ Gam (xm i) (xp i) (hf i),
      ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ G z‖ < rf i ∧
      ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ G z‖ ≤ rad d₀ s₁ a₀ / 2) :
    ∑ j : Fin (r * 6), ∫ τ : unitInterval, (uθ κ (rectFamily xm xp hf θf) (j, τ) *
        gz B (zθ (rectFamily xm xp hf θf) (j, τ))
          (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ (rectFamily xm xp hf θf) (j, τ)))).re =
      ∑ i, θf i * c0 L hκ hN (f i) (xm i) (xp i) (hf i) m := by
  -- reindex `Fin (r*6) ≃ Fin r × Fin 6`
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  set Pi : Fin 6 → Piece := rectGen (xm i) (xp i) (hf i) (fun _ => ((θf i : ℝ) : ℂ)) continuous_const with hPi
  have hfam : ∀ k : Fin 6, rectFamily xm xp hf θf (finProdFinEquiv (i, k)) = Pi k := by
    intro k
    simp only [rectFamily, Equiv.symm_apply_apply, hPi]
  set Fi : ℂ → ℂ := fun z => (f i).value (z, QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m z) with hFi
  have hFic : Continuous Fi := by
    have h1 : Continuous fun z : ℂ => (z, QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m z) :=
      continuous_id.prodMk (QuantumNLS.NormalityBridge.eigen_differentiable (L := L) κ hκ hN m).continuous
    exact (f i).lipschitz.continuous.comp h1
  have hpiece : ∀ k : Fin 6, ∫ τ : unitInterval, (uθ κ (rectFamily xm xp hf θf) (finProdFinEquiv (i, k), τ) *
        gz B (zθ (rectFamily xm xp hf θf) (finProdFinEquiv (i, k), τ))
          (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m
            (zθ (rectFamily xm xp hf θf) (finProdFinEquiv (i, k), τ)))).re =
      (∫ τ : unitInterval, uθ κ Pi (k, τ) * Fi (zθ Pi (k, τ))).re := by
    intro k
    have hcont : Continuous fun τ : unitInterval => uθ κ Pi (k, τ) * Fi (zθ Pi (k, τ)) :=
      ((continuous_uθ κ Pi).comp (Continuous.prodMk_right k)).mul
        (hFic.comp ((continuous_zθ Pi).comp (Continuous.prodMk_right k)))
    have hint : Integrable (fun τ : unitInterval => uθ κ Pi (k, τ) * Fi (zθ Pi (k, τ))) :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hre : (∫ τ : unitInterval, uθ κ Pi (k, τ) * Fi (zθ Pi (k, τ))).re =
        ∫ τ : unitInterval, (uθ κ Pi (k, τ) * Fi (zθ Pi (k, τ))).re := by
      have := Complex.reCLM.integral_comp_comm hint
      simpa only [Complex.reCLM_apply] using this.symm
    rw [hre]
    have hae : ∀ᵐ τ : unitInterval ∂volume, (τ : ℝ) ∈ Ioo (0 : ℝ) 1 := by
      have h0 := QuantumNLS.Prop020Link.vol01
      rw [ae_iff]
      refine measure_mono_null ?_ h0
      intro τ hτ
      simp only [Set.mem_ofPred_eq, Set.mem_Ioo, not_and_or, not_lt] at hτ ⊢
      rcases hτ with h1 | h1
      · exact Or.inl (le_antisymm h1 τ.2.1)
      · exact Or.inr (le_antisymm τ.2.2 h1)
    refine integral_congr_ae ?_
    filter_upwards [hae] with τ hτ
    have hz' : zθ (rectFamily xm xp hf θf) (finProdFinEquiv (i, k), τ) = zθ Pi (k, τ) := by
      simp only [zθ, hfam]
    have hu' : uθ κ (rectFamily xm xp hf θf) (finProdFinEquiv (i, k), τ) = uθ κ Pi (k, τ) := by
      simp only [uθ, zθ, hfam]
    rw [hz', hu']
    have hmem : zθ Pi (k, τ) ∈ Gam (xm i) (xp i) (hf i) :=
      rectGen_mem_Gam _ _ _ _ _ (hlt i).le (hfpos i).le k ⟨τ.2.1, τ.2.2⟩
    have him : (zθ Pi (k, τ)).im ≠ 0 := rectGen_im_ne _ _ _ _ _ (hfpos i) k hτ
    have hd := hdev i _ hmem
    rw [gz_eq_ext hκ hN m B hc0 hD hs hA hrr (f i) (rf i) (hfa i _ hmem) (hroot i _ hmem) hd.1 hd.2 him]
  simp_rw [hpiece]
  rw [← Complex.re_sum, theta_integral_rectGen (hlt i) (hfpos i) κ _ Fi hFic]
  unfold c0
  have hev : (fun z => (f i).value (z, QuantumNLS.Prop010ContourBindingR11.ev L hκ hN z m)) = Fi := rfl
  rw [hev, show -((((2 * Real.pi * κ)⁻¹ : ℝ)) : ℂ) * ((θf i : ℝ) : ℂ) * rectIntegral Fi (xm i) (xp i) (hf i) =
      (((-(2 * Real.pi * κ)⁻¹ * θf i : ℝ)) : ℂ) * rectIntegral Fi (xm i) (xp i) (hf i) by push_cast; ring,
    Complex.re_ofReal_mul]
  ring

/-! ### 6. The eigenvalue of the combined operator -/

/-- **The combined `C₀` eigenvalue** on an actual Bethe vector `Ψ_m`: window part (over `nu 6`, the form of the accepted
`Prop020Link.C0_identify`) plus `Σ_i θ_i c^{(0)}_i(m)`. -/
theorem mixed_eig (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (m : MArr N) {Z : Set ℂ} {d₀ s₁ a₀ c₁ hb : ℝ} (hc1 : 0 ≤ c₁)
    (B : BgFam Z d₀ s₁ a₀ c₁) {G : ℂ → ℂ}
    (hc0 : B.c0 = fun z => Complex.I * κ * G z) (hD : B.D = Df L κ G) (hs : B.s = sf L κ G)
    (hA : B.A = Af κ G) (hrr : 0 < rad d₀ s₁ a₀)
    (W : Fin 6 → Piece) {r : ℕ} (xm xp hf θf : Fin r → ℝ) (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i)
    (hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (Fin.append W (rectFamily xm xp hf θf) i).γ τ ∈ Z)
    (hIm : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((Fin.append W (rectFamily xm xp hf θf) i).γ τ).im| ≤ hb)
    (f : Fin r → Extension (ℂ × ℂ)) (rf : Fin r → ℝ)
    (hfa : ∀ i, ∀ z ∈ Gam (xm i) (xp i) (hf i), ∀ w, ‖w - sf L κ G z‖ < rf i →
      (f i).value (z, w) = localLog L κ G z w)
    (hroot : ∀ i, ∀ z ∈ Gam (xm i) (xp i) (hf i), ∀ j, z ≠ (qAct L κ N m j : ℂ))
    (hdev : ∀ i, ∀ z ∈ Gam (xm i) (xp i) (hf i),
      ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ G z‖ < rf i ∧
      ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ G z‖ ≤ rad d₀ s₁ a₀ / 2) :
    C0op (nu (6 + r * 6)) (fun θ => normalizedTransfer L κ N (zθ (Fin.append W (rectFamily xm xp hf θf)) θ))
        (uθ κ (Fin.append W (rectFamily xm xp hf θf))) (gθ (Fin.append W (rectFamily xm xp hf θf)) B)
        (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m) =
      (((∫ θ, (uθ κ W θ * gθ W B θ (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ W θ))).re ∂(nu 6)) +
          ∑ i, θf i * c0 L hκ hN (f i) (xm i) (xp i) (hf i) m : ℝ) : ℂ) •
        QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m := by
  set P := Fin.append W (rectFamily xm xp hf θf) with hP
  set v := QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m with hvdef
  have hv1 : ‖v‖ = 1 := (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ).orthonormal.1 m
  have hv0 : v ≠ 0 := by intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1
  have hvP : ∀ θ, normalizedTransfer L κ N (zθ P θ) v =
      QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ P θ) • v :=
    fun θ => QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis hκ hN _ m
  have hvW : ∀ θ, normalizedTransfer L κ N (zθ W θ) v =
      QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ W θ) • v :=
    fun θ => QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis hκ hN _ m
  have hZW : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (W i).γ τ ∈ Z := fun i τ hτ => by
    have := hZ (Fin.castAdd (r * 6) i) τ hτ
    rwa [hP, Fin.append_left] at this
  have hImW : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((W i).γ τ).im| ≤ hb := fun i τ hτ => by
    have := hIm (Fin.castAdd (r * 6) i) τ hτ
    rwa [hP, Fin.append_left] at this
  rw [QuantumNLS.Prop020Link.C0_eig L hκ hN hc1 P B hZ hIm hv0 _ hvP]
  congr 2
  have iP := int_re hκ hN hc1 P B hZ hIm hv1 _ hvP
  have iW := int_re hκ hN hc1 W B hZW hImW hv1 _ hvW
  have hfix : (∑ j : Fin (r * 6), ∫ τ : unitInterval, (uθ κ P (Fin.natAdd 6 j, τ) *
      gθ P B (Fin.natAdd 6 j, τ) (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m
        (zθ P (Fin.natAdd 6 j, τ)))).re) = ∑ i, θf i * c0 L hκ hN (f i) (xm i) (xp i) (hf i) m := by
    rw [← fixed_part hκ hN m B hc0 hD hs hA hrr xm xp hf θf hlt hfpos f rf hfa hroot hdev]
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [hP, gθ_eq_gz, uθ_right, zθ_right]
  have hwin : (∑ i : Fin 6, ∫ τ : unitInterval, (uθ κ P (Fin.castAdd (r * 6) i, τ) *
      gθ P B (Fin.castAdd (r * 6) i, τ) (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m
        (zθ P (Fin.castAdd (r * 6) i, τ)))).re) = ∑ i : Fin 6, ∫ τ : unitInterval, (uθ κ W (i, τ) *
      gθ W B (i, τ) (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ W (i, τ)))).re := by
    refine Finset.sum_congr rfl fun i _ => integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [hP, gθ_eq_gz, uθ_left, zθ_left]
  rw [integral_nu_split iP, integral_nu_split iW, Fin.sum_univ_add, hwin, hfix]

end QuantumNLS.Prop025OEigen

#print axioms QuantumNLS.Prop025OEigen.int_re
#print axioms QuantumNLS.Prop025OEigen.pieces_sum_gen
#print axioms QuantumNLS.Prop025OEigen.theta_integral_rectGen
#print axioms QuantumNLS.Prop025OEigen.fixed_part
#print axioms QuantumNLS.Prop025OEigen.mixed_eig

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OEigen." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OEigen aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
