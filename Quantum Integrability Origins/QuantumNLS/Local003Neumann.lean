import Mathlib
import QuantumNLS.Local003Isometry
import QuantumNLS.Local003Odd

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage H2a: the Neumann package.

Source (end of the proof): "the Neumann and inverse-square-root series are bounded on a common complex ball".  This module sets
up the Banach algebra `𝒜 = C(Γ_n, B(H_σ))` (continuous operator-valued functions on the contour), the bounded real-linear map
`G : L² →L[ℝ] 𝒜`, `G(u)(z) = V_u R_0(z)` (built exactly as in `Local002Analytic.proj_analytic`, but as a continuous linear map), and
the free resolvent `F0 ∈ 𝒜`.  For `‖G u‖ < 1`, the perturbed resolvent on the contour is the Neumann series
`F0 · (1 - G u)⁻¹` (`neumann_pack`).  Then
* `Pn F0 X = (2πi)⁻¹∮ (F0 (1-X)⁻¹)`, `Dn F0 X = (2πi)⁻¹∮ (z-p_n)(F0(1-X)⁻¹)` are ℂ-linear images of the algebra element, with
  `‖Jfun F‖ ≤ r ‖F‖`;
* `Bn X = S Fm(P D P) S` with `S = (E* P E)^{-1/2}`, which equals the actual reduced map minus `p_n` when `X = G u` and
  `P = P*` (`bridge`). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Neumann
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Rank
  QuantumNLS.Local002Free QuantumNLS.Local003Hermitian QuantumNLS.Local003Proj QuantumNLS.Local003Range
  QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry QuantumNLS.Local003InvSqrt
  QuantumNLS.LocalSpectral.Round27

variable {L κ r : ℝ}

/-- The Banach algebra of continuous operator-valued functions on the contour. -/
abbrev Alg (L : ℝ) (c : ℂ) (r : ℝ) := C(sphere c r, H2 L →L[ℂ] H2 L)

lemma Jfun_norm_le {c : ℂ} (hr : 0 < r) (F : Alg L c r) : ‖Jfun c r F‖ ≤ r * ‖F‖ := by
  have := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (c := c) (R := r)
    (C := ‖F‖) (f := extC F) hr.le (fun z hz => by
      rw [extC_apply F hz]; exact F.norm_coe_le_norm _)
  exact this

/-- `Jfun` as a continuous complex-linear map. -/
def Jclm (L : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) : Alg L c r →L[ℂ] (H2 L →L[ℂ] H2 L) :=
  (exists_J (L := L) (c := c) hr).choose

lemma Jclm_apply (c : ℂ) (hr : 0 < r) (F : Alg L c r) : Jclm L c hr F = Jfun c r F :=
  (exists_J (L := L) (c := c) hr).choose_spec F

lemma mkCLM {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : E → Y) (K0 : ℝ) (hadd : ∀ u u', F (u + u') = F u + F u') (hsmul : ∀ (a : ℝ) u, F (a • u) = a • F u)
    (hFn : ∀ u, ‖F u‖ ≤ K0 * ‖u‖) : ∃ G : E →L[ℝ] Y, ∀ u, G u = F u :=
  ⟨LinearMap.mkContinuous { toFun := F, map_add' := hadd, map_smul' := hsmul } K0 hFn, fun _ => rfl⟩

/-- Bounded real-linear multiplication package: as `exists_Tmap` but returning a continuous linear map. -/
lemma exists_Gclm {c : ℂ} {r : ℝ} (Rf : ℂ → H2 L →L[ℂ] H2 L) {K0 M : ℝ} (hK0 : 0 ≤ K0) (hM : 0 ≤ M)
    (hex : ∀ z ∈ sphere c r, ∀ u : Lp ℂ 2 (μI L), ∃ T, IsMulOp κ (Rf z) (u : ℝ → ℂ) T ∧
      ‖T‖ ≤ K0 * ‖u‖)
    (hlip : ∀ z ∈ sphere c r, ∀ w ∈ sphere c r, ∀ (u : Lp ℂ 2 (μI L)) (Tz Tw : H2 L →L[ℂ] H2 L),
      IsMulOp κ (Rf z) (u : ℝ → ℂ) Tz → IsMulOp κ (Rf w) (u : ℝ → ℂ) Tw →
        ‖Tz - Tw‖ ≤ M * ‖u‖ * ‖z - w‖) :
    ∃ G : Lp ℂ 2 (μI L) →L[ℝ] C(sphere c r, H2 L →L[ℂ] H2 L),
      (∀ (u : Lp ℂ 2 (μI L)) (z : sphere c r), G u z = Mop κ (Rf z) u) ∧
        (∀ u, ‖G u‖ ≤ K0 * ‖u‖) := by
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
  obtain ⟨G, hGF⟩ := mkCLM F K0 hadd hsmul hFn
  exact ⟨G, fun u z => by rw [hGF]; rfl, fun u => by rw [hGF]; exact hFn u⟩

/-- **The Neumann package** for the contour `Γ_n`. -/
theorem neumann_pack (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) :
    ∃ (F0 : Alg L (center L n) r) (G : Lp ℂ 2 (μI L) →L[ℝ] Alg L (center L n) r),
      (∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz) ∧
      ‖F0‖ ≤ 1 / r ∧
      (∀ u, ‖G u‖ ≤ 2 * Real.sqrt κ * Cconst L r * ‖u‖) ∧
      (∀ (u : Lp ℂ 2 (μI L)) (zz : sphere (center L n) r),
        IsMulOp κ (resolvent L κ (fun _ => 0) (parity n) zz) (u : ℝ → ℂ) (G u zz)) ∧
      (∀ u : Lp ℂ 2 (μI L), ‖G u‖ < 1 → ∀ z (hz : z ∈ sphere (center L n) r),
        resolvent L κ (u : ℝ → ℂ) (parity n) z = extC (F0 * Ring.inverse (1 - G u)) z) := by
  classical
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  set K0 : ℝ := 2 * Real.sqrt κ * Cconst L r with hK0def
  have hK0 : 0 ≤ K0 := by
    have := Cconst_nonneg L r
    positivity
  let Rf : ℂ → H2 L →L[ℂ] H2 L := fun z =>
    QuantumNLS.LocalSpectral.resolvent L κ (fun _ => 0) (parity n) z
  have hsph : ∀ z ∈ sphere (center L n) r, ‖z - (pm L n : ℂ)‖ = r := fun z hz => by
    exact mem_sphere_iff_norm.mp hz
  have hfree : ∀ z ∈ sphere (center L n) r, IsResolvent L κ (fun _ => 0) (parity n) z (Rf z) ∧
      ‖Rf z‖ ≤ 1 / r := fun z hz => by
    obtain ⟨R0, h0, hR⟩ := hyp.res r n z hr hr2 (hsph z hz)
    have : Rf z = R0 := resolvent_eq h0
    rw [this]; exact ⟨h0, hR⟩
  have hex : ∀ z ∈ sphere (center L n) r, ∀ u : Lp ℂ 2 (μI L), ∃ T, IsMulOp κ (Rf z) (u : ℝ → ℂ) T ∧
      ‖T‖ ≤ K0 * ‖u‖ := fun z hz u => by
    obtain ⟨T, hTn, hTa⟩ := exists_T (κ := κ) (Rf z) (u : ℝ → ℂ) (mul_nonneg hK0 (norm_nonneg _))
      (fun φ => by
        obtain ⟨hm, hb⟩ := hyp.pot r n z (Rf z) hr hr2 (hsph z hz) (hfree z hz).1 u φ
        exact ⟨hm, by rw [hK0def]; exact hb⟩)
    exact ⟨T, hTa, hTn⟩
  have hM : 0 ≤ K0 / r := div_nonneg hK0 hr.le
  have hlip : ∀ z ∈ sphere (center L n) r, ∀ w ∈ sphere (center L n) r, ∀ (u : Lp ℂ 2 (μI L)) (Tz Tw : H2 L →L[ℂ] H2 L),
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
  obtain ⟨G, hG, hGn⟩ := exists_Gclm (κ := κ) Rf hK0 hM hex hlip
  have hcontRf : ContinuousOn Rf (sphere (center L n) r) :=
    continuousOn_resolvent _ (M := 1 / r) (by positivity)
      (fun z hz => ⟨Rf z, (hfree z hz).1, (hfree z hz).2⟩)
  let F0 : C(sphere (center L n) r, H2 L →L[ℂ] H2 L) := ⟨fun z => Rf z, hcontRf.restrict⟩
  refine ⟨F0, G, fun zz => rfl, ?_, hGn, ?_, ?_⟩
  · refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => (hfree z z.2).2
  · intro u zz
    rw [hG u zz]
    obtain ⟨T, hT, -⟩ := hex zz zz.2 u
    exact Mop_spec ⟨T, hT⟩
  · intro u hu' z hz
    have hinv : Ring.inverse (1 - G u) =
        ↑(Units.oneSub (G u) hu')⁻¹ := by
      have := Ring.inverse_unit (M₀ := C(sphere (center L n) r, H2 L →L[ℂ] H2 L)) (Units.oneSub (G u) hu')
      rwa [Units.val_oneSub] at this
    let zz : sphere (center L n) r := ⟨z, hz⟩
    have hT : IsMulOp κ (Rf z) (u : ℝ → ℂ) (G u zz) := by
      rw [hG u zz]
      obtain ⟨T, hT, -⟩ := hex z hz u
      exact Mop_spec ⟨T, hT⟩
    have hTn : ‖G u zz‖ < 1 := lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (G u) zz) hu'
    obtain ⟨S, R, h1, h2, hR, hRes, -, -⟩ := resolvent_of_neumann (hfree z hz).1 hT hTn
    rw [resolvent_eq hRes, extC_apply _ hz, hinv]
    have hV : ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere (center L n) r, H2 L →L[ℂ] H2 L)) zz) = S := by
      have e := congrArg (fun K : C(sphere (center L n) r, H2 L →L[ℂ] H2 L) => K zz)
        (Units.inv_mul (Units.oneSub (G u) hu'))
      simp only [Units.val_oneSub, ContinuousMap.mul_apply, ContinuousMap.one_apply,
        ContinuousMap.sub_apply] at e
      calc ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere (center L n) r, H2 L →L[ℂ] H2 L)) zz)
          = (↑(Units.oneSub (G u) hu')⁻¹ : C(sphere (center L n) r, H2 L →L[ℂ] H2 L)) zz *
              ((1 - G u zz) * S) := by rw [h1, mul_one]
        _ = ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere (center L n) r, H2 L →L[ℂ] H2 L)) zz *
              (1 - G u zz)) * S := (mul_assoc _ _ _).symm
        _ = S := by rw [e, one_mul]
    rw [ContinuousMap.mul_apply, hV, hR]
    rfl

end QuantumNLS.Local003Neumann
#print axioms QuantumNLS.Local003Neumann.neumann_pack
