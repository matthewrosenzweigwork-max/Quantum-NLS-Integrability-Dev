import NlsGge.Spectral.R3cK2Quartic38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

theorem r3c_k2_quartic (B : ℝ) : ∃ η₀ C : ℝ, 0 < η₀ ∧ 0 ≤ C ∧ ∀ (N : ℕ) (z : FourierPlane N),
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 ≤ B ^ 2 →
    ∀ η : ℝ, η₀ ≤ η →
    ‖pair38 (planeReal N z) (resolv38 η (fun y => planeReal N z y *
        (resolv38 η (fun y => star (planeReal N z y)) y) ^ 2)) -
      ( (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4) / (8 * η ^ 3)
      + (∫ x in (0:ℝ)..1, planeReal N (derivativePlane N z) x * planeReal N z x *
          star (planeReal N z x) ^ 2) / (16 * η ^ 4)
      - (∫ x in (0:ℝ)..1, planeReal N z x ^ 2 * star (planeReal N z x) *
          star (planeReal N (derivativePlane N z) x)) / (8 * η ^ 4)
      + ((∫ x in (0:ℝ)..1, planeReal N (derivativePlane N (derivativePlane N z)) x *
            planeReal N z x * star (planeReal N z x) ^ 2)
          + (∫ x in (0:ℝ)..1, planeReal N z x ^ 2 * star (planeReal N (derivativePlane N z) x) ^ 2)
          + 2 * (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * planeReal N z x *
              star (planeReal N (derivativePlane N (derivativePlane N z)) x))) / (32 * η ^ 5)
      - (∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2)
          / (16 * η ^ 5) )‖ ≤ C / η ^ 6 := by
  obtain ⟨C1, hC1, hT1⟩ := transfer_star_r3c B
  obtain ⟨C2, hC2, hT2⟩ := transfer_starstar_r3c B
  obtain ⟨A0, hA0d⟩ : ∃ A0 : ℝ, A0 = Real.sqrt bracketSumE02_38 * |B| := ⟨_, rfl⟩
  obtain ⟨A1, hA1d⟩ : ∃ A1 : ℝ, A1 = 2 * Real.pi * A0 := ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = (2 * Real.pi) ^ 2 * |B| := ⟨_, rfl⟩
  have hA0 : 0 ≤ A0 := by rw [hA0d]; positivity
  have hA1 : 0 ≤ A1 := by rw [hA1d]; positivity
  have hs : 0 ≤ s := by rw [hsd]; positivity
  obtain ⟨Cr, hCr⟩ : ∃ Cr : ℝ, Cr = A0 * A1 ^ 3 + 3 * A0 * A1 * (2 * A0 + A1) * s
      + 2 * s ^ 2 * A0 * (A0 + A1) + A0 ^ 2 * s ^ 2 + 4 * C1 + 2 * (4 * C2) := ⟨_, rfl⟩
  have hCr0 : 0 ≤ Cr := by rw [hCr]; positivity
  refine ⟨1, Cr / 64, one_pos, by positivity, fun N z hS η hη => ?_⟩
  have hη0 : 0 < η := by linarith
  have hηc : (η : ℂ) ≠ 0 := by exact_mod_cast hη0.ne'
  obtain ⟨hUb, hU1b, hU2b⟩ := plane_bds_r3c B N z hS
  rw [← hA0d] at hUb
  rw [← hA0d, ← hA1d] at hU1b
  rw [← hsd] at hU2b
  have hP := perC1_plane38 N z
  have hP1 := perC1_plane38 N (derivativePlane N z)
  have hU2c := hP1.cont'
  have hU2p := hP1.per'
  have hU2s : Continuous (fun y => star (planeReal N (derivativePlane N (derivativePlane N z)) y)) :=
    continuous_star.comp hU2c
  have hU2sp : Function.Periodic
      (fun y => star (planeReal N (derivativePlane N (derivativePlane N z)) y)) 1 := fun y => by
    show star (planeReal N (derivativePlane N (derivativePlane N z)) (y + 1)) = _
    rw [hU2p y]
  have hTP := perC1_resolvT38_of_cont hη0 hU2c hU2p
  have hQP := perC1_resolv38_of_cont hη0 hU2s hU2sp
  have hGP := perC1_resolv38 hη0 hP.star
  have hg := hP.mul hGP.pow_two
  have hpair : pair38 (planeReal N z) (resolv38 η (fun y => planeReal N z y *
        (resolv38 η (fun y => star (planeReal N z y)) y) ^ 2)) =
      pair38 (resolvT38 η (planeReal N z)) (fun y => planeReal N z y *
        (resolv38 η (fun y => star (planeReal N z y)) y) ^ 2) :=
    pair38_resolv_transpose hη0 hP.cont hg.cont hP.per hg.per
  have hr0 : 0 < 1 / (2 * η) := by positivity
  have hr1 : 1 / (2 * η) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hsplit1 := resolvT_split3_r3c hη0 N z
  have hsplit2 := resolv_split3_r3c hη0 N z
  have hρ : ∀ x, resolvT38 η (planeReal N z) x = ((1 / (2 * η) : ℝ) : ℂ) * planeReal N z x
      + ((1 / (2 * η) : ℝ) : ℂ) ^ 2 * planeReal N (derivativePlane N z) x
      + ((1 / (2 * η) : ℝ) : ℂ) ^ 2 *
        resolvT38 η (planeReal N (derivativePlane N (derivativePlane N z))) x := fun x => by
    rw [hsplit1 x]; push_cast; field_simp; ring
  have hG : ∀ x, resolv38 η (fun y => star (planeReal N z y)) x =
      ((1 / (2 * η) : ℝ) : ℂ) * star (planeReal N z x)
      - ((1 / (2 * η) : ℝ) : ℂ) ^ 2 * star (planeReal N (derivativePlane N z) x)
      + ((1 / (2 * η) : ℝ) : ℂ) ^ 2 * resolv38 η (fun y => star (planeReal N
        (derivativePlane N (derivativePlane N z)) y)) x := fun x => by
    rw [hsplit2 x]; push_cast; field_simp; ring
  have hρb : ∀ x, ‖resolvT38 η (planeReal N z) x‖ ≤ 1 / (2 * η) * A0 := fun x => by
    have := resolvT38_bound hη0 hP.cont hUb x
    calc _ ≤ A0 / (2 * η) := this
      _ = 1 / (2 * η) * A0 := by ring
  have hTb : l2sq38 (resolvT38 η (planeReal N (derivativePlane N (derivativePlane N z)))) ≤
      (s * (1 / (2 * η))) ^ 2 :=
    (resolvT38_l2sq_le hη0 hU2c hU2p).trans (by
      calc _ ≤ s ^ 2 / (2 * η) ^ 2 := div_le_div_of_nonneg_right hU2b (by positivity)
        _ = _ := by field_simp)
  have hQb : l2sq38 (resolv38 η (fun y => star (planeReal N
      (derivativePlane N (derivativePlane N z)) y))) ≤ (s * (1 / (2 * η))) ^ 2 :=
    (resolv38_l2sq_le hη0 hU2s hU2sp).trans (by
      rw [l2sq38_star]
      calc _ ≤ s ^ 2 / (2 * η) ^ 2 := div_le_div_of_nonneg_right hU2b (by positivity)
        _ = _ := by field_simp)
  have hcast : ∀ w : ℂ, ((‖w‖ : ℝ) : ℂ) ^ 2 = w * star w := norm_sq_cast_eq_mul_star38
  have hK1 : ‖pair38 (resolvT38 η (planeReal N (derivativePlane N (derivativePlane N z))))
      (fun x => planeReal N z x * star (planeReal N z x) ^ 2) -
      ((1 / (2 * η) : ℝ) : ℂ) * (∫ x in (0:ℝ)..1,
        planeReal N (derivativePlane N (derivativePlane N z)) x * planeReal N z x *
          star (planeReal N z x) ^ 2)‖ ≤ 4 * C1 * (1 / (2 * η)) ^ 2 := by
    have h := hT1 N z hS η hη
    have e : ((1 / (2 * η) : ℝ) : ℂ) * (∫ x in (0:ℝ)..1,
        planeReal N (derivativePlane N (derivativePlane N z)) x * planeReal N z x *
          star (planeReal N z x) ^ 2) = (∫ x in (0:ℝ)..1,
        planeReal N (derivativePlane N (derivativePlane N z)) x *
          (planeReal N z x * star (planeReal N z x) ^ 2)) / (2 * η) := by
      rw [show (∫ x in (0:ℝ)..1, planeReal N (derivativePlane N (derivativePlane N z)) x *
          planeReal N z x * star (planeReal N z x) ^ 2) = ∫ x in (0:ℝ)..1,
          planeReal N (derivativePlane N (derivativePlane N z)) x *
          (planeReal N z x * star (planeReal N z x) ^ 2) from
        intervalIntegral.integral_congr (fun x _ => mul_assoc _ _ _)]
      push_cast; field_simp
    rw [e]
    refine h.trans (le_of_eq ?_)
    field_simp; ring
  have hK2 : ‖pair38 (fun x => planeReal N z x * star (planeReal N z x) * planeReal N z x)
      (resolv38 η (fun y => star (planeReal N (derivativePlane N (derivativePlane N z)) y))) -
      ((1 / (2 * η) : ℝ) : ℂ) * (∫ x in (0:ℝ)..1, planeReal N z x * star (planeReal N z x) *
        planeReal N z x * star (planeReal N (derivativePlane N (derivativePlane N z)) x))‖ ≤
      4 * C2 * (1 / (2 * η)) ^ 2 := by
    have h := hT2 N z hS η hη
    have hf : (fun x => ((‖planeReal N z x‖ : ℝ) : ℂ) ^ 2 * planeReal N z x) =
        fun x => planeReal N z x * star (planeReal N z x) * planeReal N z x :=
      funext fun x => by rw [hcast]
    have hi : (∫ x in (0:ℝ)..1, ((‖planeReal N z x‖ : ℝ) : ℂ) ^ 2 * planeReal N z x *
        star (planeReal N (derivativePlane N (derivativePlane N z)) x)) =
        ∫ x in (0:ℝ)..1, planeReal N z x * star (planeReal N z x) * planeReal N z x *
          star (planeReal N (derivativePlane N (derivativePlane N z)) x) :=
      intervalIntegral.integral_congr (fun x _ => by rw [hcast])
    rw [hf, hi] at h
    have e : ((1 / (2 * η) : ℝ) : ℂ) * (∫ x in (0:ℝ)..1, planeReal N z x * star (planeReal N z x) *
        planeReal N z x * star (planeReal N (derivativePlane N (derivativePlane N z)) x)) =
        (∫ x in (0:ℝ)..1, planeReal N z x * star (planeReal N z x) * planeReal N z x *
        star (planeReal N (derivativePlane N (derivativePlane N z)) x)) / (2 * η) := by
      push_cast; field_simp
    rw [e]
    refine h.trans (le_of_eq ?_)
    field_simp; ring
  have h := quartic_abs38 (r := 1 / (2 * η)) hr0 hr1 hA0 hA1 hs hP hP1 hTP.cont hQP.cont hρ hG
    hUb hU1b hρb hTb hQb hK1 hK2
  -- reconcile the cast forms of the statement with the abstract form
  have hI3 : ((∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4 : ℝ) : ℂ) =
      ∫ x in (0:ℝ)..1, (planeReal N z x * star (planeReal N z x)) ^ 2 := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [← hcast]; push_cast; ring
  have hI5 : ((∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 2 * ‖planeReal N (derivativePlane N z) x‖ ^ 2
      : ℝ) : ℂ) = ∫ x in (0:ℝ)..1, (planeReal N z x * star (planeReal N z x)) *
        (planeReal N (derivativePlane N z) x * star (planeReal N (derivativePlane N z) x)) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    push_cast; rw [hcast, hcast]
  have hI2 : (∫ x in (0:ℝ)..1, ((‖planeReal N z x‖ : ℝ) : ℂ) ^ 2 * planeReal N z x *
        star (planeReal N (derivativePlane N (derivativePlane N z)) x)) =
      ∫ x in (0:ℝ)..1, planeReal N z x * star (planeReal N z x) * planeReal N z x *
        star (planeReal N (derivativePlane N (derivativePlane N z)) x) :=
    intervalIntegral.integral_congr (fun x _ => by rw [hcast])
  refine (congrArg norm (?_ : _ = _)).trans_le (h.trans_eq ?_)
  · rw [hpair]
    congr 1
    rw [hI3, hI5, hI2]
    push_cast
    field_simp
    ring
  · rw [hCr]
    field_simp
    ring

end NlsGge.SpectralFoundations
