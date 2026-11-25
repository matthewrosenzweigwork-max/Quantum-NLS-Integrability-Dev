import Mathlib
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.ThirdConsultation.KST.KST047Host
import NlsGge.Atomic.KST.KST047
import NlsGge.Atomic.KST.KST048
import NlsGge.GK38.Lib.CircleArgument
import NlsGge.GK38.Lib.Rouche

                                                                                                        
                                                                                                    
                                                                                              
                                                                                                                 
                                                                                                 
                                                                                                      
                                                                                                        
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST004
open NlsGge.GK38

namespace NlsGge.ThirdConsultation.KST

/-- Auxiliary: points of the closed disc of radius `r/2` about `σ + ζ` (`‖ζ‖ = r`) lie within `3r/2` of `σ`. -/
theorem kst050_closed_norm (σ ζ z : ℂ) (r : ℝ) (hζ : ‖ζ‖ = r) (hr : 0 < r)
    (hz : z ∈ Metric.closedBall (σ + ζ) (r / 2)) :
    z ∈ Metric.ball σ (2 * r) ∧ ‖z - σ‖ ≤ 3 * r / 2 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 : ‖z - σ‖ ≤ ‖z - (σ + ζ)‖ + ‖ζ‖ := by
    calc ‖z - σ‖ = ‖(z - (σ + ζ)) + ζ‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖z - σ‖ ≤ 3 * r / 2 := by linarith
  refine ⟨?_, h2⟩
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

/-- Auxiliary: the distance estimate `‖g - h‖ ≤ (5/21)‖z - σ‖` for `g z = z - c0 - a z - u z`,
`h z = z - (σ + ζ)`. -/
theorem kst050_est (c0 σ ζ : ℂ) (r : ℝ) (a u : ℂ → ℂ)
    (hσ : σ = c0 + a σ) (huσ : u σ = ζ)
    (ha : ∀ z ∈ Metric.ball σ (2 * r), ‖a z - a σ‖ ≤ (1 / 21 : ℝ) * ‖z - σ‖)
    (hu : ∀ z ∈ Metric.ball σ (2 * r), ‖u z - u σ‖ ≤ (4 / 21 : ℝ) * ‖z - σ‖)
    (z : ℂ) (hz : z ∈ Metric.ball σ (2 * r)) :
    ‖(z - c0 - a z - u z) - (z - (σ + ζ))‖ ≤ (5 / 21 : ℝ) * ‖z - σ‖ := by
  have hc0 : c0 = σ - a σ := by linear_combination (-1 : ℂ) * hσ
  have e : (z - c0 - a z - u z) - (z - (σ + ζ)) = (a σ - a z) - (u z - u σ) := by
    rw [← huσ, hc0]; ring
  rw [e]
  calc ‖(a σ - a z) - (u z - u σ)‖ ≤ ‖a σ - a z‖ + ‖u z - u σ‖ := norm_sub_le _ _
    _ = ‖a z - a σ‖ + ‖u z - u σ‖ := by rw [norm_sub_rev]
    _ ≤ (1 / 21 : ℝ) * ‖z - σ‖ + (4 / 21 : ℝ) * ‖z - σ‖ := add_le_add (ha z hz) (hu z hz)
    _ = (5 / 21 : ℝ) * ‖z - σ‖ := by ring

/-- Auxiliary: far from `σ + ζ` the function `g` has no zero. -/
theorem kst050_nz (c0 σ ζ : ℂ) (r : ℝ) (a u : ℂ → ℂ)
    (hσ : σ = c0 + a σ) (huσ : u σ = ζ)
    (ha : ∀ z ∈ Metric.ball σ (2 * r), ‖a z - a σ‖ ≤ (1 / 21 : ℝ) * ‖z - σ‖)
    (hu : ∀ z ∈ Metric.ball σ (2 * r), ‖u z - u σ‖ ≤ (4 / 21 : ℝ) * ‖z - σ‖)
    (z : ℂ) (hz : z ∈ Metric.ball σ (2 * r)) (hz2 : ‖z - σ‖ ≤ 3 * r / 2)
    (hfar : 5 * r / 14 < ‖z - (σ + ζ)‖) :
    z - c0 - a z - u z ≠ 0 := by
  intro h0
  have := kst050_est c0 σ ζ r a u hσ huσ ha hu z hz
  rw [h0, zero_sub, norm_neg] at this
  linarith

/-- Auxiliary: a point of the ball of radius `r/2` about `σ + ζ` is far from `σ + ζ'` when `ζ' = -ζ`. -/
theorem kst050_far (σ ζ ζ' z : ℂ) (r : ℝ) (hζ : ‖ζ‖ = r) (hr : 0 < r) (hζ' : ζ' = -ζ)
    (hz : z ∈ Metric.ball (σ + ζ) (r / 2)) :
    5 * r / 14 < ‖z - (σ + ζ')‖ := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have e : (2 : ℂ) * ζ = (z - (σ + ζ')) - (z - (σ + ζ)) := by rw [hζ']; ring
  have h2 : ‖(2 : ℂ) * ζ‖ = 2 * r := by rw [norm_mul, hζ]; norm_num
  have h3 : ‖(2 : ℂ) * ζ‖ ≤ ‖z - (σ + ζ')‖ + ‖z - (σ + ζ)‖ := by
    rw [e]; exact norm_sub_le _ _
  linarith

/-- Auxiliary: one Rouché comparison in the disc of radius `r/2` about `σ + ζ`. -/
theorem kst050_side (c0 σ ζ : ℂ) (r : ℝ) (hr : 0 < r) (a u : ℂ → ℂ)
    (haA : AnalyticOnNhd ℂ a (Metric.ball σ (2 * r)))
    (huA : AnalyticOnNhd ℂ u (Metric.ball σ (2 * r)))
    (hσ : σ = c0 + a σ) (huσ : u σ = ζ) (hζ : ‖ζ‖ = r)
    (ha : ∀ z ∈ Metric.ball σ (2 * r), ‖a z - a σ‖ ≤ (1 / 21 : ℝ) * ‖z - σ‖)
    (hu : ∀ z ∈ Metric.ball σ (2 * r), ‖u z - u σ‖ ≤ (4 / 21 : ℝ) * ‖z - σ‖) :
    ∃ x : ℂ, Lib.zeroMultiset (fun z => z - c0 - a z - u z) (Metric.ball (σ + ζ) (r / 2)) = {x} ∧
      x ∈ Metric.ball (σ + ζ) (r / 2) ∧ AnalyticAt ℂ (fun z => z - c0 - a z - u z) x ∧
      analyticOrderNatAt (fun z => z - c0 - a z - u z) x = 1 := by
  classical
  have hR : 0 < r / 2 := by linarith
  have hGA : AnalyticOnNhd ℂ (fun z => z - c0 - a z - u z) (Metric.closedBall (σ + ζ) (r / 2)) := by
    intro z hz
    have hzD := (kst050_closed_norm σ ζ z r hζ hr hz).1
    exact ((analyticAt_id.sub analyticAt_const).sub (haA z hzD)).sub (huA z hzD)
  have hfA : AnalyticOnNhd ℂ (fun z : ℂ => z - (σ + ζ)) (Metric.closedBall (σ + ζ) (r / 2)) :=
    fun z _ => analyticAt_id.sub analyticAt_const
  have hroot : ∀ z ∈ Metric.sphere (σ + ζ) (r / 2),
      ‖(z - c0 - a z - u z) - (z - (σ + ζ))‖ < ‖z - (σ + ζ)‖ := by
    intro z hz
    obtain ⟨hzD, hzn⟩ := kst050_closed_norm σ ζ z r hζ hr (Metric.sphere_subset_closedBall hz)
    have h1 := kst050_est c0 σ ζ r a u hσ huσ ha hu z hzD
    have hfz : ‖z - (σ + ζ)‖ = r / 2 := by
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      exact hz
    rw [hfz]
    linarith
  have hcard := NlsGge.GK38.Lib.rouche_circle hR hfA hGA hroot
  have hrep := NlsGge.GK38.Lib.zeroMultiset_ball_eq_replicate hR hfA
    (fun z _ hne => sub_ne_zero.2 hne)
  have hord : analyticOrderNatAt (fun z : ℂ => z - (σ + ζ)) (σ + ζ) = 1 := by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_id_sub_const_self]
    rfl
  have hcard1 : Multiset.card (Lib.zeroMultiset (fun z => z - c0 - a z - u z)
      (Metric.ball (σ + ζ) (r / 2))) = 1 := by
    rw [hcard, hrep, Multiset.card_replicate, hord]
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.1 hcard1
  have hc := NlsGge.GK38.Lib.count_zeroMultiset_ball hGA x
  rw [hx, Multiset.count_singleton_self] at hc
  by_cases hxb : x ∈ Metric.ball (σ + ζ) (r / 2)
  · rw [if_pos hxb] at hc
    exact ⟨x, hx, hxb, hGA x (Metric.ball_subset_closedBall hxb), hc.symm⟩
  · rw [if_neg hxb] at hc
    exact absurd hc (by norm_num)

/-- Auxiliary: a simple zero of `P` where `Q` does not vanish is a simple zero of `P * Q`
(here phrased for a function `f` locally equal to `P * Q`). -/
theorem kst050_order_mul (f P Q : ℂ → ℂ) (x : ℂ) (hP : AnalyticAt ℂ P x) (hQ : AnalyticAt ℂ Q x)
    (hP1 : analyticOrderNatAt P x = 1) (hQ0 : Q x ≠ 0)
    (hf : f =ᶠ[nhds x] fun z => P z * Q z) :
    analyticOrderNatAt f x = 1 := by
  have hPt : analyticOrderAt P x ≠ ⊤ := by
    intro h
    simp [analyticOrderNatAt, h] at hP1
  have hQ' : analyticOrderAt Q x = 0 := hQ.analyticOrderAt_eq_zero.2 hQ0
  have hQt : analyticOrderAt Q x ≠ ⊤ := by rw [hQ']; exact ENat.zero_ne_top
  have hQn : analyticOrderNatAt Q x = 0 := by
    unfold analyticOrderNatAt
    rw [hQ']
    rfl
  have h1 : analyticOrderNatAt f x = analyticOrderNatAt (P * Q) x := by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hf]
    rfl
  rw [h1, analyticOrderNatAt_mul hP hQ hPt hQt, hP1, hQn]

theorem kst050 (n : ℤ) (a b c : ℂ → ℂ) (σ ξ : ℂ)
    (h : Balanced n a b c σ) (hξ : ξ^2 = b σ*c σ)
    (q : ℂ → ℂ)
    (hq : AnalyticOnNhd ℂ q (Metric.ball σ (2*rootRadius b c σ)))
    (hqσ : q σ = ξ)
    (hqsq : ∀ z ∈ Metric.ball σ (2*rootRadius b c σ), q z^2 = b z*c z)
    (hqderiv : ∀ z ∈ Metric.ball σ (2*rootRadius b c σ),
      ‖deriv q z‖ ≤ (4/21 : ℝ)) :
  ∃ xp xm : ℂ,
    Lib.zeroMultiset (fun z => z-center n-a z-q z)
      (Metric.ball (σ+ξ) (rootRadius b c σ/2)) = {xp} ∧
    Lib.zeroMultiset (fun z => z-center n-a z+q z)
      (Metric.ball (σ-ξ) (rootRadius b c σ/2)) = {xm} ∧
    Lib.zeroMultiset (determinant n a b c)
      (Metric.ball (center n) (Real.pi/3)) = {xp, xm} ∧
    rootRadius b c σ ≤ ‖xp-xm‖ ∧ ‖xp-xm‖ ≤ 3*rootRadius b c σ := by
  classical
  obtain ⟨hr0, -, -, -, -, hdisc⟩ := kst047 n a b c σ h
  have h48 := kst048 n a b c σ h
  have hSC := h.1
  obtain ⟨⟨ha, hb, hc, hbd⟩, hσeq, -, hbc, -, -⟩ := h
  set r := rootRadius b c σ with hr
  have hr2 : r ^ 2 = ‖b σ * c σ‖ := by rw [hr]; exact Real.sq_sqrt (norm_nonneg _)
  have hξn : ‖ξ‖ = r := by
    have h1 : ‖ξ‖ ^ 2 = r ^ 2 := by rw [← norm_pow, hξ, hr2]
    exact (sq_eq_sq₀ (norm_nonneg _) hr0.le).1 h1
  have hmξ : ‖-ξ‖ = r := by rw [norm_neg]; exact hξn
  have hDB : Metric.ball σ (2 * r) ⊆ Metric.ball (center n) (Real.pi / 3) :=
    Metric.ball_subset_closedBall.trans hdisc
  have hDstrip : ∀ z ∈ Metric.ball σ (2 * r), z ∈ spectralStrip n := fun z hz =>
    closedBall_subset_strip n (Metric.ball_subset_closedBall (hDB hz))
  have haD : AnalyticOnNhd ℂ a (Metric.ball σ (2 * r)) := ha.mono hDstrip
  have hσD : σ ∈ Metric.ball σ (2 * r) := Metric.mem_ball_self (by linarith)
  have hlipA : ∀ z ∈ Metric.ball σ (2 * r), ‖a z - a σ‖ ≤ (1 / 21 : ℝ) * ‖z - σ‖ := by
    intro z hz
    refine (convex_ball σ (2 * r)).norm_image_sub_le_of_norm_deriv_le (f := a) (C := 1 / 21) ?_ ?_ hσD hz
    · intro x hx
      exact (h48 x (Metric.ball_subset_closedBall hx)).1.differentiableAt
    · intro x hx
      exact (h48 x (Metric.ball_subset_closedBall hx)).2.2.2.1
  have hlipQ : ∀ z ∈ Metric.ball σ (2 * r), ‖q z - q σ‖ ≤ (4 / 21 : ℝ) * ‖z - σ‖ := by
    intro z hz
    refine (convex_ball σ (2 * r)).norm_image_sub_le_of_norm_deriv_le (f := q) (C := 4 / 21) ?_ ?_ hσD hz
    · intro x hx
      exact (hq x hx).differentiableAt
    · exact hqderiv
  have hlipmQ : ∀ z ∈ Metric.ball σ (2 * r), ‖(fun w => -q w) z - (fun w => -q w) σ‖ ≤
      (4 / 21 : ℝ) * ‖z - σ‖ := by
    intro z hz
    have := hlipQ z hz
    simp only [neg_sub_neg]
    rwa [norm_sub_rev]
  have hmqA : AnalyticOnNhd ℂ (fun w => -q w) (Metric.ball σ (2 * r)) := fun z hz => (hq z hz).neg
  obtain ⟨xp, hxp, hxpb, hxpA, hxpo⟩ := kst050_side (center n) σ ξ r hr0 a q haD hq hσeq hqσ hξn hlipA hlipQ
  obtain ⟨xm', hxm', hxmb', hxmA', hxmo'⟩ := kst050_side (center n) σ (-ξ) r hr0 a (fun w => -q w)
    haD hmqA hσeq (by simp [hqσ]) hmξ hlipA hlipmQ
  set Gp : ℂ → ℂ := fun z => z - center n - a z - q z with hGp
  set Gm : ℂ → ℂ := fun z => z - center n - a z + q z with hGm
  have e1 : Gm = fun z => z - center n - a z - (fun w => -q w) z := by
    funext z
    simp only [hGm]
    ring
  have hxm : Lib.zeroMultiset Gm (Metric.ball (σ - ξ) (r / 2)) = {xm'} := by
    rw [e1, sub_eq_add_neg σ ξ]
    exact hxm'
  have hxmA : AnalyticAt ℂ Gm xm' := by rw [e1]; exact hxmA'
  have hxmo : analyticOrderNatAt Gm xm' = 1 := by rw [e1]; exact hxmo'
  obtain ⟨hxpD, hxpn⟩ := kst050_closed_norm σ ξ xp r hξn hr0 (Metric.ball_subset_closedBall hxpb)
  obtain ⟨hxmD, hxmn⟩ := kst050_closed_norm σ (-ξ) xm' r hmξ hr0 (Metric.ball_subset_closedBall hxmb')
  -- the other factor does not vanish at the root of one factor
  have hGm_xp : Gm xp ≠ 0 := by
    have := kst050_nz (center n) σ (-ξ) r a (fun w => -q w) hσeq (by simp [hqσ]) hlipA hlipmQ xp hxpD hxpn
      (kst050_far σ ξ (-ξ) xp r hξn hr0 rfl hxpb)
    intro h0
    apply this
    have h0' : xp - center n - a xp + q xp = 0 := h0
    show xp - center n - a xp - -q xp = 0
    linear_combination h0'
  have hGp_xm : Gp xm' ≠ 0 := by
    have := kst050_nz (center n) σ ξ r a q hσeq hqσ hlipA hlipQ xm' hxmD hxmn
      (kst050_far σ (-ξ) ξ xm' r hmξ hr0 (neg_neg ξ).symm hxmb')
    exact this
  have hGpA : ∀ z ∈ Metric.ball σ (2 * r), AnalyticAt ℂ Gp z := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).sub (haD z hz)).sub (hq z hz)
  have hGmA : ∀ z ∈ Metric.ball σ (2 * r), AnalyticAt ℂ Gm z := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).sub (haD z hz)).add (hq z hz)
  have hfact : ∀ z ∈ Metric.ball σ (2 * r), determinant n a b c z = Gp z * Gm z := by
    intro z hz
    simp only [determinant, hGp, hGm]
    rw [← hqsq z hz]
    ring
  -- the determinant has the two simple zeros xp, xm'
  have hdetA : AnalyticOnNhd ℂ (determinant n a b c)
      (Metric.closedBall (center n) (Real.pi / 3)) := by
    intro z hz
    have hz' := closedBall_subset_strip n hz
    exact (((analyticAt_id.sub analyticAt_const).sub (ha z hz')).pow 2).sub
      ((hb z hz').mul (hc z hz'))
  have hcard := (kst019 n a b c hSC).1
  set M := Lib.zeroMultiset (determinant n a b c) (Metric.ball (center n) (Real.pi / 3)) with hM
  have hcount : ∀ x ∈ Metric.ball (center n) (Real.pi / 3),
      M.count x = analyticOrderNatAt (determinant n a b c) x := by
    intro x hx
    rw [hM, NlsGge.GK38.Lib.count_zeroMultiset_ball hdetA x, if_pos hx]
  have hordp : analyticOrderNatAt (determinant n a b c) xp = 1 :=
    kst050_order_mul _ Gp Gm xp (hGpA xp hxpD) (hGmA xp hxpD) hxpo hGm_xp
      (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hxpD) (fun z hz => hfact z hz))
  have hordm : analyticOrderNatAt (determinant n a b c) xm' = 1 :=
    kst050_order_mul _ Gm Gp xm' hxmA (hGpA xm' hxmD) hxmo hGp_xm
      (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hxmD)
        (fun z hz => by rw [hfact z hz, mul_comm]))
  have hcp : M.count xp = 1 := by rw [hcount xp (hDB hxpD), hordp]
  have hcm : M.count xm' = 1 := by rw [hcount xm' (hDB hxmD), hordm]
  -- the gap
  have hxpd : ‖xp - (σ + ξ)‖ < r / 2 := by
    have := hxpb
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have hxmd : ‖xm' - (σ + -ξ)‖ < r / 2 := by
    have := hxmb'
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have h2ξ : ‖(2 : ℂ) * ξ‖ = 2 * r := by rw [norm_mul, hξn]; norm_num
  have hlow : r < ‖xp - xm'‖ := by
    have e : (2 : ℂ) * ξ = (xp - xm') - (xp - (σ + ξ)) + (xm' - (σ + -ξ)) := by ring
    have h3 : ‖(2 : ℂ) * ξ‖ ≤ ‖xp - xm'‖ + ‖xp - (σ + ξ)‖ + ‖xm' - (σ + -ξ)‖ := by
      rw [e]
      calc ‖(xp - xm') - (xp - (σ + ξ)) + (xm' - (σ + -ξ))‖
          ≤ ‖(xp - xm') - (xp - (σ + ξ))‖ + ‖xm' - (σ + -ξ)‖ := norm_add_le _ _
        _ ≤ (‖xp - xm'‖ + ‖xp - (σ + ξ)‖) + ‖xm' - (σ + -ξ)‖ := by
            gcongr; exact norm_sub_le _ _
    linarith
  have hup : ‖xp - xm'‖ ≤ 3 * r := by
    have e : xp - xm' = (2 : ℂ) * ξ + (xp - (σ + ξ)) - (xm' - (σ + -ξ)) := by ring
    rw [e]
    calc ‖(2 : ℂ) * ξ + (xp - (σ + ξ)) - (xm' - (σ + -ξ))‖
        ≤ ‖(2 : ℂ) * ξ + (xp - (σ + ξ))‖ + ‖xm' - (σ + -ξ)‖ := norm_sub_le _ _
      _ ≤ (‖(2 : ℂ) * ξ‖ + ‖xp - (σ + ξ)‖) + ‖xm' - (σ + -ξ)‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ 3 * r := by linarith
  have hne : xp ≠ xm' := by
    intro h0
    rw [h0, sub_self, norm_zero] at hlow
    linarith
  have hle : ({xp, xm'} : Multiset ℂ) ≤ M := by
    rw [Multiset.le_iff_count]
    intro y
    by_cases hy : y = xp
    · subst hy
      simp [Multiset.count_cons, Multiset.count_singleton, hne, hcp]
    · by_cases hy2 : y = xm'
      · subst hy2
        simp [Multiset.count_cons, Multiset.count_singleton, hne.symm, hcm]
      · simp [Multiset.count_cons, Multiset.count_singleton, hy, hy2]
  have heq : ({xp, xm'} : Multiset ℂ) = M :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcard]; simp)
  exact ⟨xp, xm', hxp, hxm, heq.symm, hlow.le, hup⟩

end NlsGge.ThirdConsultation.KST
end
