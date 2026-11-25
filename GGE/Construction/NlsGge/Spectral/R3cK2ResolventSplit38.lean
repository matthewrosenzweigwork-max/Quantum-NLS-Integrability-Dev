import NlsGge.Spectral.R3cResolventCore38
import NlsGge.Spectral.R3cResolventL2_38
import NlsGge.Spectral.R3cPlaneSobolev38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # R3c piece P6a: three-piece resolvent splittings and the transfers (★), (★★)

With `U = planeReal N z`, `U₁`, `U₂` the plane of the first and second derivative, `Ū = star ∘ U`:
`R Ū = Ū/(2η) - Ū'/(4η²) + R(Ū'')/(4η²)` and `Rt U = U/(2η) + U'/(4η²) + Rt(U'')/(4η²)`.
The transfers move the order-two derivative `U''` across a resolvent. -/

/-! ## Splittings -/

theorem resolv_split3_r3c {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    resolv38 η (fun y => star (planeReal N z y)) x =
      star (planeReal N z x) / (2 * η)
        - star (planeReal N (derivativePlane N z) x) / (4 * η ^ 2)
      + resolv38 η (fun y => star (planeReal N (derivativePlane N (derivativePlane N z)) y)) x
        / (4 * η ^ 2) := by
  have h0 := (perC1_plane38 N z).star
  have h1 := (perC1_plane38 N (derivativePlane N z)).star
  rw [resolv38_expand38 hη h0 x, resolv38_expand38 hη h1 x]
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  field_simp
  ring

theorem resolvT_split3_r3c {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    resolvT38 η (planeReal N z) x =
      planeReal N z x / (2 * η) + planeReal N (derivativePlane N z) x / (4 * η ^ 2)
      + resolvT38 η (planeReal N (derivativePlane N (derivativePlane N z))) x / (4 * η ^ 2) := by
  have h0 := perC1_plane38 N z
  have h1 := perC1_plane38 N (derivativePlane N z)
  rw [resolvT38_expand38 hη h0 x, resolvT38_expand38 hη h1 x]
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  field_simp
  ring

/-! ## Generic transfers -/

/-- Transfer of a derivative from the left factor of the pairing, across `Rt`, onto the right factor
`F`, whose derivative is bounded in sup norm. -/
theorem transfer_gen_A38 {η : ℝ} (hη : 0 < η) {V F F' : ℝ → ℂ} (hV : Continuous V)
    (hVp : Function.Periodic V 1) (hF : PerC1_38 F F') {M : ℝ} (hM : ∀ x, ‖F' x‖ ≤ M) :
    ‖pair38 (resolvT38 η V) F - pair38 V F / (2 * (η : ℂ))‖ ≤
      M * Real.sqrt (l2sq38 V) / (4 * η ^ 2) := by
  have h1 : pair38 (resolvT38 η V) F = pair38 V (resolv38 η F) :=
    (pair38_resolv_transpose hη hV hF.cont hVp hF.per).symm
  have hRF' := (perC1_resolv38 hη hF).cont'
  have hRF := (perC1_resolv38 hη hF).cont
  have h2 : pair38 V (resolv38 η F) =
      pair38 V F / (2 * (η : ℂ)) - pair38 V (resolv38 η F') / (2 * (η : ℂ)) := by
    unfold pair38
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div,
      ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [resolv38_expand38 hη hF x]
      ring
    · exact ((hV.mul hF.cont).div_const _).intervalIntegrable 0 1
    · exact ((hV.mul hRF').div_const _).intervalIntegrable 0 1
  have h3 : pair38 V (resolv38 η F') = pair38 (resolv38 η F') V := by
    unfold pair38
    exact intervalIntegral.integral_congr (fun x _ => mul_comm _ _)
  have hb : ‖pair38 (resolv38 η F') V‖ ≤ M / (2 * η) * Real.sqrt (l2sq38 V) :=
    norm_pair38_le_sup hRF' hV (fun x => resolv38_bound hη hF.cont' hM x)
  have hn : ‖(2 * (η : ℂ))‖ = 2 * η := by
    rw [norm_mul]; simp [abs_of_pos hη]
  have e : pair38 (resolvT38 η V) F - pair38 V F / (2 * (η : ℂ)) =
      -(pair38 V (resolv38 η F') / (2 * (η : ℂ))) := by
    rw [h1, h2]; ring
  rw [e, norm_neg, norm_div, hn, h3]
  have h2η : 0 < 2 * η := by positivity
  calc ‖pair38 (resolv38 η F') V‖ / (2 * η)
      ≤ (M / (2 * η) * Real.sqrt (l2sq38 V)) / (2 * η) :=
        div_le_div_of_nonneg_right hb h2η.le
    _ = M * Real.sqrt (l2sq38 V) / (4 * η ^ 2) := by
        field_simp
        ring

/-- Transfer of a derivative from the left factor `W` of the pairing across `R` onto the right
factor `W`, whose derivative is bounded in sup norm. -/
theorem transfer_gen_B38 {η : ℝ} (hη : 0 < η) {W W' G : ℝ → ℂ} (hW : PerC1_38 W W')
    (hG : Continuous G) (hGp : Function.Periodic G 1) {M : ℝ} (hM : ∀ x, ‖W' x‖ ≤ M) :
    ‖pair38 W (resolv38 η G) - pair38 W G / (2 * (η : ℂ))‖ ≤
      M * Real.sqrt (l2sq38 G) / (4 * η ^ 2) := by
  have h1 : pair38 W (resolv38 η G) = pair38 (resolvT38 η W) G :=
    pair38_resolv_transpose hη hW.cont hG hW.per hGp
  have hRW' := (perC1_resolvT38 hη hW).cont'
  have hRW := (perC1_resolvT38 hη hW).cont
  have h2 : pair38 (resolvT38 η W) G =
      pair38 W G / (2 * (η : ℂ)) + pair38 (resolvT38 η W') G / (2 * (η : ℂ)) := by
    unfold pair38
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div,
      ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [resolvT38_expand38 hη hW x]
      ring
    · exact ((hW.cont.mul hG).div_const _).intervalIntegrable 0 1
    · exact ((hRW'.mul hG).div_const _).intervalIntegrable 0 1
  have hb : ‖pair38 (resolvT38 η W') G‖ ≤ M / (2 * η) * Real.sqrt (l2sq38 G) :=
    norm_pair38_le_sup hRW' hG (fun x => resolvT38_bound hη hW.cont' hM x)
  have hn : ‖(2 * (η : ℂ))‖ = 2 * η := by
    rw [norm_mul]; simp [abs_of_pos hη]
  have e : pair38 W (resolv38 η G) - pair38 W G / (2 * (η : ℂ)) =
      pair38 (resolvT38 η W') G / (2 * (η : ℂ)) := by
    rw [h1, h2]; ring
  rw [e, norm_div, hn]
  have h2η : 0 < 2 * η := by positivity
  calc ‖pair38 (resolvT38 η W') G‖ / (2 * η)
      ≤ (M / (2 * η) * Real.sqrt (l2sq38 G)) / (2 * η) :=
        div_le_div_of_nonneg_right hb h2η.le
    _ = M * Real.sqrt (l2sq38 G) / (4 * η ^ 2) := by
        field_simp
        ring

/-! ## Plane bounds under `S 2 ≤ B²` -/

theorem plane_bds_r3c (B : ℝ) (N : ℕ) (z : FourierPlane N)
    (hS : ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 ≤ B ^ 2) :
    (∀ x, ‖planeReal N z x‖ ≤ Real.sqrt bracketSumE02_38 * |B|) ∧
    (∀ x, ‖planeReal N (derivativePlane N z) x‖ ≤ 2 * Real.pi * (Real.sqrt bracketSumE02_38 * |B|)) ∧
    l2sq38 (planeReal N (derivativePlane N (derivativePlane N z))) ≤
      ((2 * Real.pi) ^ 2 * |B|) ^ 2 := by
  have hS1 : ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 ≤ B ^ 2 :=
    (plane_S_mono_r3c N z (by norm_num : 1 ≤ 2)).trans hS
  have hs1 := Real.sqrt_le_sqrt hS1
  have hs2 := Real.sqrt_le_sqrt hS
  rw [Real.sqrt_sq_eq_abs] at hs1 hs2
  have hK : 0 ≤ Real.sqrt bracketSumE02_38 := Real.sqrt_nonneg _
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · exact (plane_sup_le_r3c N z x).trans (mul_le_mul_of_nonneg_left hs1 hK)
  · refine (plane_deriv_sup_le_r3c N z x).trans ?_
    calc 2 * Real.pi * Real.sqrt bracketSumE02_38 * _
        ≤ 2 * Real.pi * Real.sqrt bracketSumE02_38 * |B| :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = _ := by ring
  · have h := plane_l2_le_r3c N z 2
    show (∫ x in (0:ℝ)..1, ‖planeReal N (derivativePlane N (derivativePlane N z)) x‖ ^ 2) ≤ _
    refine h.trans ?_
    calc (2 * Real.pi) ^ (2 * 2) * _ ≤ (2 * Real.pi) ^ (2 * 2) * B ^ 2 :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by rw [mul_pow ((2 * Real.pi) ^ 2) |B|, sq_abs]; ring

/-! ## Algebra -/

theorem norm_sq_cast_eq_mul_star38 (w : ℂ) : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * star w := by
  have := Complex.mul_conj' w
  rw [← this]
  rfl

theorem bound_F38 (u v : ℂ) {a b : ℝ} (hu : ‖u‖ ≤ a) (hv : ‖v‖ ≤ b) :
    ‖v * star u ^ 2 + u * (2 * star u * star v)‖ ≤ 3 * a ^ 2 * b := by
  have ha : 0 ≤ a := (norm_nonneg u).trans hu
  have hb : 0 ≤ b := (norm_nonneg v).trans hv
  have h1 : ‖v * star u ^ 2 + u * (2 * star u * star v)‖ ≤ ‖v‖ * ‖u‖ ^ 2 + ‖u‖ * (2 * ‖u‖ * ‖v‖) := by
    refine (norm_add_le _ _).trans ?_
    simp [norm_pow]
  have h2 : ‖v‖ * ‖u‖ ^ 2 ≤ b * a ^ 2 := by gcongr
  have h3 : ‖u‖ * (2 * ‖u‖ * ‖v‖) ≤ a * (2 * a * b) := by gcongr
  nlinarith

theorem bound_W38 (u v : ℂ) {a b : ℝ} (hu : ‖u‖ ≤ a) (hv : ‖v‖ ≤ b) :
    ‖(v * star u + u * star v) * u + u * star u * v‖ ≤ 3 * a ^ 2 * b := by
  have ha : 0 ≤ a := (norm_nonneg u).trans hu
  have hb : 0 ≤ b := (norm_nonneg v).trans hv
  have e1 : ‖(v * star u + u * star v) * u‖ ≤ (‖v‖ * ‖u‖ + ‖u‖ * ‖v‖) * ‖u‖ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    simp
  have e2 : ‖u * star u * v‖ = ‖u‖ * ‖u‖ * ‖v‖ := by simp
  have h1 := (norm_add_le ((v * star u + u * star v) * u) (u * star u * v))
  have h2 : (‖v‖ * ‖u‖ + ‖u‖ * ‖v‖) * ‖u‖ ≤ (b * a + a * b) * a := by gcongr
  have h3 : ‖u‖ * ‖u‖ * ‖v‖ ≤ a * a * b := by gcongr
  nlinarith

/-! ## The transfers -/

/-- (★) -/
theorem transfer_star_r3c (B : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 ≤ B ^ 2 →
    ∀ η : ℝ, 1 ≤ η →
    ‖pair38 (resolvT38 η (planeReal N (derivativePlane N (derivativePlane N z))))
        (fun x => planeReal N z x * star (planeReal N z x) ^ 2) -
      (∫ x in (0:ℝ)..1, planeReal N (derivativePlane N (derivativePlane N z)) x *
          (planeReal N z x * star (planeReal N z x) ^ 2)) / (2 * η)‖ ≤ C / η ^ 2 := by
  set a : ℝ := Real.sqrt bracketSumE02_38 * |B| with ha
  set b : ℝ := 2 * Real.pi * a with hb
  set s : ℝ := (2 * Real.pi) ^ 2 * |B| with hs
  have ha0 : 0 ≤ a := by positivity
  have hs0 : 0 ≤ s := by positivity
  refine ⟨3 * a ^ 2 * b * s / 4, by positivity, fun N z hS η hη => ?_⟩
  have hη0 : 0 < η := by linarith
  obtain ⟨hU, hU1, hU2⟩ := plane_bds_r3c B N z hS
  have hP := perC1_plane38 N z
  have hP1 := perC1_plane38 N (derivativePlane N z)
  have hF := hP.mul hP.star.pow_two
  have hM : ∀ x, ‖planeReal N (derivativePlane N z) x * star (planeReal N z x) ^ 2 +
      planeReal N z x * (2 * star (planeReal N z x) * star (planeReal N (derivativePlane N z) x))‖
        ≤ 3 * a ^ 2 * b := fun x => bound_F38 _ _ (hU x) (hU1 x)
  have h := transfer_gen_A38 hη0 hP1.cont' hP1.per' hF hM
  have hsq : Real.sqrt (l2sq38 (planeReal N (derivativePlane N (derivativePlane N z)))) ≤ s := by
    have := Real.sqrt_le_sqrt hU2
    rwa [Real.sqrt_sq hs0] at this
  have hM0 : 0 ≤ 3 * a ^ 2 * b := by positivity
  refine h.trans ?_
  have hη2 : 0 < η ^ 2 := by positivity
  calc 3 * a ^ 2 * b * Real.sqrt (l2sq38 (planeReal N (derivativePlane N (derivativePlane N z))))
        / (4 * η ^ 2) ≤ 3 * a ^ 2 * b * s / (4 * η ^ 2) := by gcongr
    _ = 3 * a ^ 2 * b * s / 4 / η ^ 2 := by field_simp

/-- (★★) -/
theorem transfer_starstar_r3c (B : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 ≤ B ^ 2 →
    ∀ η : ℝ, 1 ≤ η →
    ‖pair38 (fun x => ‖planeReal N z x‖ ^ 2 * planeReal N z x)
        (resolv38 η (fun y => star (planeReal N (derivativePlane N (derivativePlane N z)) y))) -
      (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * planeReal N z x *
          star (planeReal N (derivativePlane N (derivativePlane N z)) x)) / (2 * η)‖
        ≤ C / η ^ 2 := by
  set a : ℝ := Real.sqrt bracketSumE02_38 * |B| with ha
  set b : ℝ := 2 * Real.pi * a with hb
  set s : ℝ := (2 * Real.pi) ^ 2 * |B| with hs
  have ha0 : 0 ≤ a := by positivity
  have hs0 : 0 ≤ s := by positivity
  refine ⟨3 * a ^ 2 * b * s / 4, by positivity, fun N z hS η hη => ?_⟩
  have hη0 : 0 < η := by linarith
  obtain ⟨hU, hU1, hU2⟩ := plane_bds_r3c B N z hS
  have hP := perC1_plane38 N z
  have hP1 := perC1_plane38 N (derivativePlane N z)
  have hG := hP1.star
  have hW := (hP.mul hP.star).mul hP
  have hM : ∀ x, ‖(planeReal N (derivativePlane N z) x * star (planeReal N z x) +
      planeReal N z x * star (planeReal N (derivativePlane N z) x)) * planeReal N z x +
      planeReal N z x * star (planeReal N z x) * planeReal N (derivativePlane N z) x‖
        ≤ 3 * a ^ 2 * b := fun x => bound_W38 _ _ (hU x) (hU1 x)
  have h := transfer_gen_B38 hη0 hW hG.cont' hG.per' hM
  have hfun : (fun x => ‖planeReal N z x‖ ^ 2 * planeReal N z x) =
      fun y => planeReal N z y * star (planeReal N z y) * planeReal N z y := by
    funext x
    rw [norm_sq_cast_eq_mul_star38]
  have hsq : Real.sqrt (l2sq38 (fun y => star (planeReal N (derivativePlane N
      (derivativePlane N z)) y))) ≤ s := by
    rw [l2sq38_star]
    have := Real.sqrt_le_sqrt hU2
    rwa [Real.sqrt_sq hs0] at this
  have hM0 : 0 ≤ 3 * a ^ 2 * b := by positivity
  rw [hfun]
  have h' : ‖pair38 (fun y => planeReal N z y * star (planeReal N z y) * planeReal N z y)
        (resolv38 η (fun y => star (planeReal N (derivativePlane N (derivativePlane N z)) y))) -
      (∫ x in (0:ℝ)..1, planeReal N z x * star (planeReal N z x) * planeReal N z x *
          star (planeReal N (derivativePlane N (derivativePlane N z)) x)) / (2 * η)‖
        ≤ 3 * a ^ 2 * b * Real.sqrt (l2sq38 (fun y => star (planeReal N (derivativePlane N
      (derivativePlane N z)) y))) / (4 * η ^ 2) := h
  have hint : (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * planeReal N z x *
          star (planeReal N (derivativePlane N (derivativePlane N z)) x)) =
      ∫ x in (0:ℝ)..1, planeReal N z x * star (planeReal N z x) * planeReal N z x *
          star (planeReal N (derivativePlane N (derivativePlane N z)) x) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [norm_sq_cast_eq_mul_star38]
  rw [hint]
  refine h'.trans ?_
  have hη2 : 0 < η ^ 2 := by positivity
  calc 3 * a ^ 2 * b * Real.sqrt (l2sq38 (fun y => star (planeReal N (derivativePlane N
        (derivativePlane N z)) y))) / (4 * η ^ 2) ≤ 3 * a ^ 2 * b * s / (4 * η ^ 2) := by gcongr
    _ = 3 * a ^ 2 * b * s / 4 / η ^ 2 := by field_simp

end NlsGge.SpectralFoundations
end
