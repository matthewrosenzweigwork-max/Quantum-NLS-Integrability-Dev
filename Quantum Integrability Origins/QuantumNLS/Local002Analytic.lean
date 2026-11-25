import Mathlib
import QuantumNLS.Local002Hyp

/-! LOCAL-002 `lem:reset-analytic-projections`, stage C: real-analyticity of `u ↦ P_n(u)`.

The multiplication operators `T_z(u) = V_u R_{0,n}(z)` (`IsMulOp`) depend real-linearly and boundedly
on `u ∈ L²(0,L)` and Lipschitz-continuously on `z ∈ Γ_n`, so `u ↦ T(u)` is a bounded real-linear map
into the Banach algebra `C(Γ_n, B(H))`.  The perturbed resolvent on `Γ_n` is `R_0 (1 - T(u))^{-1}`
there (Neumann resolvent of stage A), and `P_n(u) = J(R_0 (1 - T(u))^{-1})` with `J` the bounded
contour-integral functional.  `Ring.inverse` is analytic at units. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002
open QuantumNLS.LocalSpectral

variable {L κ : ℝ}

/-- `T φ = V_u (R φ)` almost everywhere. -/
def IsMulOp (κ : ℝ) (R : H2 L →L[ℂ] H2 L) (u : ℝ → ℂ) (T : H2 L →L[ℂ] H2 L) : Prop :=
  ∀ φ : H2 L, (T φ : ℝ → E2) =ᵐ[μI L] fun x => Vpt κ (u x) ((R φ : ℝ → E2) x)

lemma IsMulOp.unique {R : H2 L →L[ℂ] H2 L} {u : ℝ → ℂ} {T T' : H2 L →L[ℂ] H2 L}
    (h : IsMulOp κ R u T) (h' : IsMulOp κ R u T') : T = T' := by
  ext1 φ
  apply Lp.ext
  filter_upwards [h φ, h' φ] with x a b
  rw [a, b]

lemma Vpt_sub (κ : ℝ) (w : ℂ) (g g' : E2) : Vpt κ w (g - g') = Vpt κ w g - Vpt κ w g' := by
  ext i; fin_cases i <;> simp [Vpt, lopPt, Jm, vec2] <;> ring

lemma Vpt_add_pot (κ : ℝ) (w w' : ℂ) (g : E2) : Vpt κ (w + w') g = Vpt κ w g + Vpt κ w' g := by
  ext i; fin_cases i <;> simp [Vpt, lopPt, Jm, vec2] <;> ring

lemma Vpt_real_smul_pot (κ : ℝ) (a : ℝ) (w : ℂ) (g : E2) :
    Vpt κ ((a : ℂ) * w) g = (a : ℂ) • Vpt κ w g := by
  ext i; fin_cases i <;> simp [Vpt, lopPt, Jm, vec2] <;> ring

lemma IsMulOp.add {R : H2 L →L[ℂ] H2 L} {u u' : Lp ℂ 2 (μI L)} {T T' : H2 L →L[ℂ] H2 L}
    (h : IsMulOp κ R (u : ℝ → ℂ) T) (h' : IsMulOp κ R (u' : ℝ → ℂ) T') :
    IsMulOp κ R ((u + u' : Lp ℂ 2 (μI L)) : ℝ → ℂ) (T + T') := by
  intro φ
  filter_upwards [h φ, h' φ, Lp.coeFn_add (T φ) (T' φ), Lp.coeFn_add u u'] with x a b c d
  show ((T φ + T' φ : H2 L) : ℝ → E2) x = _
  rw [c, Pi.add_apply, a, b, d, Pi.add_apply, Vpt_add_pot]

lemma IsMulOp.real_smul {R : H2 L →L[ℂ] H2 L} {u : Lp ℂ 2 (μI L)} {T : H2 L →L[ℂ] H2 L}
    (h : IsMulOp κ R (u : ℝ → ℂ) T) (a : ℝ) :
    IsMulOp κ R ((a • u : Lp ℂ 2 (μI L)) : ℝ → ℂ) ((a : ℂ) • T) := by
  intro φ
  filter_upwards [h φ, Lp.coeFn_smul (a : ℂ) (T φ), Lp.coeFn_smul a u] with x a1 a2 a3
  show ((a : ℂ) • T φ : H2 L) x = _
  rw [a2, Pi.smul_apply, a1, a3, Pi.smul_apply, Complex.real_smul, Vpt_real_smul_pot]

/-- The canonical multiplication operator (junk `0` if none exists). -/
def Mop (κ : ℝ) (R : H2 L →L[ℂ] H2 L) (u : Lp ℂ 2 (μI L)) : H2 L →L[ℂ] H2 L := by
  classical
  exact if h : ∃ T, IsMulOp κ R (u : ℝ → ℂ) T then h.choose else 0

lemma Mop_spec {R : H2 L →L[ℂ] H2 L} {u : Lp ℂ 2 (μI L)} (h : ∃ T, IsMulOp κ R (u : ℝ → ℂ) T) :
    IsMulOp κ R (u : ℝ → ℂ) (Mop κ R u) := by
  classical
  unfold Mop
  rw [dif_pos h]
  exact h.choose_spec

lemma Mop_eq {R : H2 L →L[ℂ] H2 L} {u : Lp ℂ 2 (μI L)} {T : H2 L →L[ℂ] H2 L}
    (h : IsMulOp κ R (u : ℝ → ℂ) T) : Mop κ R u = T :=
  (Mop_spec ⟨T, h⟩).unique h

lemma mulop_sub {u : ℝ → ℂ} {σ : ℤˣ} {z w : ℂ} {Rz Rw Tz Tw : H2 L →L[ℂ] H2 L}
    (hz : IsResolvent L κ (fun _ => 0) σ z Rz) (hw : IsResolvent L κ (fun _ => 0) σ w Rw)
    (hTz : IsMulOp κ Rz u Tz) (hTw : IsMulOp κ Rw u Tw) :
    Tz - Tw = (w - z) • (Tz * Rw) := by
  ext1 φ
  apply Lp.ext
  have hid : Rz φ - Rw φ = (w - z) • Rz (Rw φ) := by
    have := congrArg (fun A : H2 L →L[ℂ] H2 L => A φ) (resolvent_identity hz hw)
    simpa using this
  filter_upwards [Lp.coeFn_sub (Tz φ) (Tw φ), hTz φ, hTw φ, Lp.coeFn_smul (w - z) (Tz (Rw φ)),
    hTz (Rw φ), Lp.coeFn_sub (Rz φ) (Rw φ), Lp.coeFn_smul (w - z) (Rz (Rw φ))] with x a1 a2 a3 a4 a5 a6 a7
  have a8 : ((Rz φ : ℝ → E2) x - (Rw φ : ℝ → E2) x) = (w - z) • (Rz (Rw φ) : ℝ → E2) x := by
    rw [← Pi.sub_apply, ← a6, hid, a7]; rfl
  show ((Tz φ - Tw φ : H2 L) : ℝ → E2) x = ((w - z) • Tz (Rw φ) : H2 L) x
  rw [a1, Pi.sub_apply, a2, a3, a4, Pi.smul_apply, a5, ← Vpt_sub, a8, Vpt_smul]

lemma Mop_add {R : H2 L →L[ℂ] H2 L} {u u' : Lp ℂ 2 (μI L)}
    (h : ∃ T, IsMulOp κ R (u : ℝ → ℂ) T) (h' : ∃ T, IsMulOp κ R (u' : ℝ → ℂ) T) :
    Mop κ R (u + u') = Mop κ R u + Mop κ R u' :=
  Mop_eq (IsMulOp.add (Mop_spec h) (Mop_spec h'))

lemma Mop_real_smul {R : H2 L →L[ℂ] H2 L} {u : Lp ℂ 2 (μI L)}
    (h : ∃ T, IsMulOp κ R (u : ℝ → ℂ) T) (a : ℝ) :
    Mop κ R (a • u) = a • Mop κ R u := by
  rw [Mop_eq ((Mop_spec h).real_smul a)]
  apply ContinuousLinearMap.ext
  intro φ
  exact Complex.coe_smul _ _

/-- Generic assembly of a bounded real-linear map into `C(Γ, B(H))`. -/
lemma asmb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (c : ℂ) (r : ℝ) (F : E → C(sphere c r, H →L[ℂ] H)) (K0 : ℝ)
    (hadd : ∀ u u', F (u + u') = F u + F u')
    (hsmul : ∀ (a : ℝ) u, F (a • u) = a • F u)
    (hFn : ∀ u, ‖F u‖ ≤ K0 * ‖u‖) :
    ∀ u0, AnalyticAt ℝ F u0 := by
  let f : E →ₗ[ℝ] C(sphere c r, H →L[ℂ] H) := { toFun := F, map_add' := hadd, map_smul' := hsmul }
  let 𝕋 : E →L[ℝ] C(sphere c r, H →L[ℂ] H) := LinearMap.mkContinuous f K0 hFn
  have : F = ⇑𝕋 := rfl
  intro u0
  rw [this]
  exact 𝕋.analyticAt u0

lemma lip_of_mop {c : ℂ} {r : ℝ} (Rf : ℂ → H2 L →L[ℂ] H2 L) {M : ℝ} (hM : 0 ≤ M)
    (hlip : ∀ z ∈ sphere c r, ∀ w ∈ sphere c r, ∀ (u : Lp ℂ 2 (μI L)) (Tz Tw : H2 L →L[ℂ] H2 L),
      IsMulOp κ (Rf z) (u : ℝ → ℂ) Tz → IsMulOp κ (Rf w) (u : ℝ → ℂ) Tw →
        ‖Tz - Tw‖ ≤ M * ‖u‖ * ‖z - w‖)
    (hex : ∀ z ∈ sphere c r, ∀ u : Lp ℂ 2 (μI L), ∃ T, IsMulOp κ (Rf z) (u : ℝ → ℂ) T)
    (u : Lp ℂ 2 (μI L)) : Continuous fun z : sphere c r => Mop κ (Rf z) u := by
  have hl : LipschitzWith (Real.toNNReal (M * ‖u‖)) (fun z : sphere c r => Mop κ (Rf z) u) := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    rw [Real.coe_toNNReal _ (mul_nonneg hM (norm_nonneg _))]
    exact hlip z z.2 w w.2 u _ _ (Mop_spec (hex z z.2 u)) (Mop_spec (hex w w.2 u))
  exact hl.continuous

/-- The bounded real-linear map `u ↦ (z ↦ V_u R_0(z)) ∈ C(Γ, B(H))`. -/
lemma exists_Tmap {c : ℂ} {r : ℝ} (Rf : ℂ → H2 L →L[ℂ] H2 L) {K0 M : ℝ} (hK0 : 0 ≤ K0) (hM : 0 ≤ M)
    (hex : ∀ z ∈ sphere c r, ∀ u : Lp ℂ 2 (μI L), ∃ T, IsMulOp κ (Rf z) (u : ℝ → ℂ) T ∧
      ‖T‖ ≤ K0 * ‖u‖)
    (hlip : ∀ z ∈ sphere c r, ∀ w ∈ sphere c r, ∀ (u : Lp ℂ 2 (μI L)) (Tz Tw : H2 L →L[ℂ] H2 L),
      IsMulOp κ (Rf z) (u : ℝ → ℂ) Tz → IsMulOp κ (Rf w) (u : ℝ → ℂ) Tw →
        ‖Tz - Tw‖ ≤ M * ‖u‖ * ‖z - w‖) :
    ∃ G : Lp ℂ 2 (μI L) → C(sphere c r, H2 L →L[ℂ] H2 L),
      (∀ (u : Lp ℂ 2 (μI L)) (z : sphere c r), G u z = Mop κ (Rf z) u) ∧
        (∀ u, ‖G u‖ ≤ K0 * ‖u‖) ∧ ∀ u0, AnalyticAt ℝ G u0 := by
  have hex' : ∀ z ∈ sphere c r, ∀ u : Lp ℂ 2 (μI L), ∃ T, IsMulOp κ (Rf z) (u : ℝ → ℂ) T :=
    fun z hz u => (hex z hz u).elim fun T hT => ⟨T, hT.1⟩
  have hnorm : ∀ (u : Lp ℂ 2 (μI L)) (z : sphere c r), ‖Mop κ (Rf z) u‖ ≤ K0 * ‖u‖ := fun u z => by
    obtain ⟨T, hT, hn⟩ := hex z z.2 u
    rw [Mop_eq hT]; exact hn
  let F : Lp ℂ 2 (μI L) → C(sphere c r, H2 L →L[ℂ] H2 L) := fun u =>
    ⟨fun z => Mop κ (Rf z) u, lip_of_mop Rf hM hlip hex' u⟩
  have hadd : ∀ u u', F (u + u') = F u + F u' := fun u u' => by
    ext z : 1
    exact Mop_add (hex' z z.2 u) (hex' z z.2 u')
  have hsmul : ∀ (a : ℝ) u, F (a • u) = a • F u := fun a u => by
    ext z : 1
    exact Mop_real_smul (hex' z z.2 u) a
  have hFn : ∀ u, ‖F u‖ ≤ K0 * ‖u‖ := fun u =>
    (ContinuousMap.norm_le _ (mul_nonneg hK0 (norm_nonneg _))).2 fun z => hnorm u z
  exact ⟨F, fun u z => rfl, hFn, asmb c r F K0 hadd hsmul hFn⟩

/-! ### The contour functional -/

/-- Extension by zero of a continuous function on the circle. -/
def extC {c : ℂ} {r : ℝ} (F : C(sphere c r, H2 L →L[ℂ] H2 L)) : ℂ → H2 L →L[ℂ] H2 L := by
  classical
  exact fun z => if h : z ∈ sphere c r then F ⟨z, h⟩ else 0

lemma extC_apply {c : ℂ} {r : ℝ} (F : C(sphere c r, H2 L →L[ℂ] H2 L)) {z : ℂ}
    (h : z ∈ sphere c r) : extC F z = F ⟨z, h⟩ := by
  classical
  unfold extC
  rw [dif_pos h]

lemma extC_apply_neg {c : ℂ} {r : ℝ} (F : C(sphere c r, H2 L →L[ℂ] H2 L)) {z : ℂ}
    (h : z ∉ sphere c r) : extC F z = 0 := by
  classical
  unfold extC
  rw [dif_neg h]

lemma continuousOn_extC {c : ℂ} {r : ℝ} (F : C(sphere c r, H2 L →L[ℂ] H2 L)) :
    ContinuousOn (extC F) (sphere c r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (sphere c r).domRestrict (extC F) = F := by
    funext z; exact extC_apply F z.2
  rw [this]; exact F.continuous

lemma extC_add {c : ℂ} {r : ℝ} (F G : C(sphere c r, H2 L →L[ℂ] H2 L)) :
    extC (F + G) = fun z => extC F z + extC G z := by
  classical
  funext z
  by_cases h : z ∈ sphere c r
  · rw [extC_apply _ h, extC_apply _ h, extC_apply _ h]; rfl
  · rw [extC_apply_neg _ h, extC_apply_neg _ h, extC_apply_neg _ h]; exact (add_zero 0).symm

lemma extC_smul {c : ℂ} {r : ℝ} (a : ℂ) (F : C(sphere c r, H2 L →L[ℂ] H2 L)) :
    extC (a • F) = fun z => a • extC F z := by
  classical
  funext z
  by_cases h : z ∈ sphere c r
  · rw [extC_apply _ h, extC_apply _ h]; rfl
  · rw [extC_apply_neg _ h, extC_apply_neg _ h]; exact ContinuousLinearMap.ext fun x => by simp

/-- `(2πi)⁻¹ ∮_{|z-c|=r} F(z) dz`. -/
def Jfun (c : ℂ) (r : ℝ) (F : C(sphere c r, H2 L →L[ℂ] H2 L)) : H2 L →L[ℂ] H2 L :=
  ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ z in C(c, r), extC F z

lemma exists_J {c : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ J : C(sphere c r, H2 L →L[ℂ] H2 L) →L[ℂ] (H2 L →L[ℂ] H2 L), ∀ F, J F = Jfun c r F := by
  have hint : ∀ F : C(sphere c r, H2 L →L[ℂ] H2 L), CircleIntegrable (extC F) c r :=
    fun F => (continuousOn_extC F).circleIntegrable hr.le
  let f : C(sphere c r, H2 L →L[ℂ] H2 L) →ₗ[ℂ] (H2 L →L[ℂ] H2 L) :=
    { toFun := Jfun c r
      map_add' := fun F G => by
        unfold Jfun
        rw [extC_add, circleIntegral.integral_add (hint F) (hint G), smul_add]
      map_smul' := fun a F => by
        unfold Jfun
        rw [extC_smul, circleIntegral.integral_smul]
        rw [smul_comm]; rfl }
  have hb : ∀ F : C(sphere c r, H2 L →L[ℂ] H2 L), ‖f F‖ ≤ r * ‖F‖ := fun F => by
    have := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (c := c) (R := r)
      (C := ‖F‖) (f := extC F) hr.le (fun z hz => by
        rw [extC_apply F hz]; exact F.norm_coe_le_norm _)
    exact this
  exact ⟨{ toLinearMap := f, cont := AddMonoidHomClass.continuous_of_bound f r hb }, fun F => rfl⟩

/-! ### Real-analyticity of `u ↦ P_n(u)` -/

theorem proj_analytic (hyp : FreeResolventHyp L κ) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) {ρ : ℝ} (hρ : 2 * Real.sqrt κ * Cconst L r * ρ ≤ 1) :
    AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => perturbedProj L κ (u : ℝ → ℂ) n r) (ball 0 ρ) := by
  classical
  set c : ℂ := (pm L n : ℂ) with hc
  set K0 : ℝ := 2 * Real.sqrt κ * Cconst L r with hK0def
  have hK0 : 0 ≤ K0 := by
    have := Cconst_nonneg L r
    positivity
  let Rf : ℂ → H2 L →L[ℂ] H2 L := fun z =>
    QuantumNLS.LocalSpectral.resolvent L κ (fun _ => 0) (parity n) z
  have hsph : ∀ z ∈ sphere c r, ‖z - (pm L n : ℂ)‖ = r := fun z hz => by
    simpa [hc, mem_sphere_iff_norm] using hz
  have hfree : ∀ z ∈ sphere c r, IsResolvent L κ (fun _ => 0) (parity n) z (Rf z) ∧
      ‖Rf z‖ ≤ 1 / r := fun z hz => by
    obtain ⟨R0, h0, hR⟩ := hyp.res r n z hr hr2 (hsph z hz)
    have : Rf z = R0 := resolvent_eq h0
    rw [this]; exact ⟨h0, hR⟩
  have hex : ∀ z ∈ sphere c r, ∀ u : Lp ℂ 2 (μI L), ∃ T, IsMulOp κ (Rf z) (u : ℝ → ℂ) T ∧
      ‖T‖ ≤ K0 * ‖u‖ := fun z hz u => by
    obtain ⟨T, hTn, hTa⟩ := exists_T (κ := κ) (Rf z) (u : ℝ → ℂ) (mul_nonneg hK0 (norm_nonneg _))
      (fun φ => by
        obtain ⟨hm, hb⟩ := hyp.pot r n z (Rf z) hr hr2 (hsph z hz) (hfree z hz).1 u φ
        exact ⟨hm, by rw [hK0def]; exact hb⟩)
    exact ⟨T, hTa, hTn⟩
  have hM : 0 ≤ K0 / r := div_nonneg hK0 hr.le
  have hlip : ∀ z ∈ sphere c r, ∀ w ∈ sphere c r, ∀ (u : Lp ℂ 2 (μI L)) (Tz Tw : H2 L →L[ℂ] H2 L),
      IsMulOp κ (Rf z) (u : ℝ → ℂ) Tz → IsMulOp κ (Rf w) (u : ℝ → ℂ) Tw →
        ‖Tz - Tw‖ ≤ K0 / r * ‖u‖ * ‖z - w‖ := fun z hz w hw u Tz Tw hTz hTw => by
    obtain ⟨T', hT', hn⟩ := hex z hz u
    have hTzT : Tz = T' := hTz.unique hT'
    rw [mulop_sub (hfree z hz).1 (hfree w hw).1 hTz hTw, norm_smul]
    have h1 : ‖Tz * Rf w‖ ≤ K0 * ‖u‖ * (1 / r) :=
      (norm_mul_le _ _).trans (mul_le_mul (hTzT ▸ hn) (hfree w hw).2 (norm_nonneg _)
        (mul_nonneg hK0 (norm_nonneg _)))
    calc ‖w - z‖ * ‖Tz * Rf w‖ ≤ ‖w - z‖ * (K0 * ‖u‖ * (1 / r)) := by gcongr
      _ = K0 / r * ‖u‖ * ‖z - w‖ := by rw [norm_sub_rev]; ring
  obtain ⟨G, hG, hGn, hGa⟩ := exists_Tmap Rf hK0 hM hex hlip
  have hcontRf : ContinuousOn Rf (sphere c r) :=
    continuousOn_resolvent _ (M := 1 / r) (by positivity)
      (fun z hz => ⟨Rf z, (hfree z hz).1, (hfree z hz).2⟩)
  let F0 : C(sphere c r, H2 L →L[ℂ] H2 L) := ⟨fun z => Rf z, hcontRf.restrict⟩
  obtain ⟨Jℂ, hJ⟩ := exists_J (L := L) (c := c) hr
  let J := Jℂ.restrictScalars ℝ
  have hunit : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ‖G u‖ < 1 := fun u hu => by
    have hu' : ‖u‖ < ρ := by simpa using hu
    calc ‖G u‖ ≤ K0 * ‖u‖ := hGn u
      _ < 1 := by
        rcases hK0.eq_or_lt with h | h
        · rw [← h]; norm_num
        · calc K0 * ‖u‖ < K0 * ρ := by gcongr
            _ ≤ 1 := hρ
  have hana : AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => J (F0 * Ring.inverse (1 - G u)))
      (ball 0 ρ) := by
    intro u0 hu0
    have h1 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => (1 : C(sphere c r, H2 L →L[ℂ] H2 L)) - G u) u0 :=
      analyticAt_const.sub (hGa u0)
    have h2 : AnalyticAt ℝ (Ring.inverse : C(sphere c r, H2 L →L[ℂ] H2 L) → _)
        (1 - G u0) := by
      have := analyticAt_inverse (𝕜 := ℝ) (Units.oneSub (G u0) (hunit u0 hu0))
      rwa [Units.val_oneSub] at this
    have h3 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => Ring.inverse (1 - G u)) u0 :=
      AnalyticAt.comp (f := fun u : Lp ℂ 2 (μI L) => (1 : C(sphere c r, H2 L →L[ℂ] H2 L)) - G u)
        (x := u0) h2 h1
    have h4 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => F0 * Ring.inverse (1 - G u)) u0 :=
      AnalyticAt.mul (𝕜 := ℝ) (A := C(sphere c r, H2 L →L[ℂ] H2 L)) analyticAt_const h3
    exact (J.analyticAt _).comp h4
  refine hana.congr isOpen_ball fun u hu => ?_
  have hu' : ‖G u‖ < 1 := hunit u hu
  have hinv : Ring.inverse (1 - G u) = ↑(Units.oneSub (G u) hu')⁻¹ := by
    have := Ring.inverse_unit (M₀ := C(sphere c r, H2 L →L[ℂ] H2 L)) (Units.oneSub (G u) hu')
    rwa [Units.val_oneSub] at this
  have hpt : ∀ z ∈ sphere c r, QuantumNLS.LocalSpectral.resolvent L κ (u : ℝ → ℂ) (parity n) z =
      extC (F0 * Ring.inverse (1 - G u)) z := by
    intro z hz
    let zz : sphere c r := ⟨z, hz⟩
    have hT : IsMulOp κ (Rf z) (u : ℝ → ℂ) (G u zz) := by
      rw [hG u zz]
      obtain ⟨T, hT, -⟩ := hex z hz u
      exact Mop_spec ⟨T, hT⟩
    have hTn : ‖G u zz‖ < 1 := lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (G u) zz) hu'
    obtain ⟨S, R, h1, h2, hR, hRes, -, -⟩ := resolvent_of_neumann (hfree z hz).1 hT hTn
    rw [resolvent_eq hRes, extC_apply _ hz, hinv]
    have hV : ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz) = S := by
      have e := congrArg (fun K : C(sphere c r, H2 L →L[ℂ] H2 L) => K zz)
        (Units.inv_mul (Units.oneSub (G u) hu'))
      simp only [Units.val_oneSub, ContinuousMap.mul_apply, ContinuousMap.one_apply,
        ContinuousMap.sub_apply] at e
      calc ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz)
          = (↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz *
              ((1 - G u zz) * S) := by rw [h1, mul_one]
        _ = ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz *
              (1 - G u zz)) * S := (mul_assoc _ _ _).symm
        _ = S := by rw [e, one_mul]
    rw [ContinuousMap.mul_apply, hV, hR]
    rfl
  symm
  unfold perturbedProj rieszProj
  have hcen : QuantumNLS.LocalSpectral.center L n = c := rfl
  rw [hcen, circleIntegral.integral_congr hr.le (fun z hz => hpt z hz)]
  exact (hJ _).symm

end QuantumNLS.Local002
#print axioms QuantumNLS.Local002.proj_analytic
