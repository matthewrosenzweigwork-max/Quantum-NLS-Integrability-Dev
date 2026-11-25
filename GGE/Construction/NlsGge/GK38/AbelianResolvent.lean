import NlsGge.GK38.AbelianJoukowskiActual
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The actual standard-root scalar cosine resolvent, by two ordinary Cauchy integrals.
UNCOMPILED prospective source; all parameter integrabilities precede identities. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

 theorem p2UnitCircle_cosine38 (θ : ℝ) :
    circleMap 0 1 θ+(circleMap 0 1 θ)⁻¹=2*(Real.cos θ:ℂ) := by
  simp only [circleMap,Complex.ofReal_one,one_mul,zero_add]
  rw [← Complex.exp_neg]
  have hn : -((θ:ℂ)*Complex.I)=(-(θ:ℂ))*Complex.I := by ring
  rw [hn,← Complex.two_cos,← Complex.ofReal_cos]

/-- Both actual poles are away from the circle before their integrals are evaluated. -/
theorem p2Joukowski_rational_integral38 (u R : ℂ) (hu : 1 < ‖u‖) (hR : R ≠ 0) :
    CircleIntegrable (fun v : ℂ => (v-u⁻¹)⁻¹) 0 1 ∧
    CircleIntegrable (fun v : ℂ => (v-u)⁻¹) 0 1 ∧
    circleIntegral (fun v : ℂ => (Complex.I/R)*((v-u⁻¹)⁻¹-(v-u)⁻¹)) 0 1 =
      -(2*(Real.pi:ℂ))/R := by
  have hp := p2Joukowski_poles38 hu
  have hni : u⁻¹ ∉ sphere (0:ℂ) 1 := by
    intro he
    have hl := mem_ball_zero_iff.mp hp.1
    exact (ne_of_lt hl) (mem_sphere_zero_iff_norm.mp he)
  have hno : u ∉ sphere (0:ℂ) 1 := by
    intro he
    exact hp.2.1 (sphere_subset_closedBall he)
  have hci : CircleIntegrable (fun v : ℂ => (v-u⁻¹)⁻¹) 0 1 := by
    simpa only [circleIntegrable_sub_inv_iff,abs_one,one_ne_zero,false_or] using hni
  have hco : CircleIntegrable (fun v : ℂ => (v-u)⁻¹) 0 1 := by
    simpa only [circleIntegrable_sub_inv_iff,abs_one,one_ne_zero,false_or] using hno
  have hao : AnalyticOnNhd ℂ (fun v : ℂ => (v-u)⁻¹) (closedBall 0 1) := by
    intro v hv
    apply (analyticAt_id.sub analyticAt_const).inv
    exact sub_ne_zero.mpr (by
      intro he
      change v=u at he
      apply hp.2.1
      simpa only [he] using hv)
  have heo : circleIntegral (fun v : ℂ => (v-u)⁻¹) 0 1=0 :=
    (hao.differentiableOn.diffContOnCl_ball (Subset.refl _)).circleIntegral_eq_zero (by norm_num)
  refine ⟨hci,hco,?_⟩
  rw [circleIntegral.integral_const_mul,circleIntegral.integral_sub hci hco,
    circleIntegral.integral_sub_inv_of_mem_ball hp.1,heo,sub_zero]
  field_simp [hR]
  simp [Complex.I_sq]

/-- The scalar resolvent identity includes repeated endpoints without dividing their gap. -/
theorem p2StdRoot_cosine_resolvent38 (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    IntervalIntegrable
      (fun θ : ℝ => 1/(z-(a+b)/2-((b-a)/2)*(Real.cos θ:ℂ))) volume 0 (2*Real.pi) ∧
    (∫ θ in (0:ℝ)..2*Real.pi,
      1/(z-(a+b)/2-((b-a)/2)*(Real.cos θ:ℂ))) =
      -(2*(Real.pi:ℂ))/stdRoot38 ((a+b)/2) ((b-a)^2) z := by
  let A : ℂ := z-(a+b)/2
  let d : ℂ := (b-a)/2
  let R : ℂ := stdRoot38 ((a+b)/2) ((b-a)^2) z
  have hR : R ≠ 0 := stdRoot_ne_zero38 a b z hz
  have hden : ∀ θ : ℝ, A-d*(Real.cos θ:ℂ) ≠ 0 := by
    intro θ he
    apply hz
    have hx := p2Cosine_mem_segment38 a b θ
    convert hx using 1
    dsimp [A,d] at he
    linear_combination he
  have hc : Continuous (fun θ : ℝ => 1/(A-d*(Real.cos θ:ℂ))) :=
    continuous_const.div
      (continuous_const.sub (continuous_const.mul
        (Complex.continuous_ofReal.comp Real.continuous_cos))) hden
  refine ⟨hc.intervalIntegrable _ _,?_⟩
  change (∫ θ in (0:ℝ)..2*Real.pi,1/(A-d*(Real.cos θ:ℂ)))=-(2*(Real.pi:ℂ))/R
  by_cases hab : a=b
  · subst b
    have hAz : A ≠ 0 := by simpa only [d,sub_self,zero_div,zero_mul,sub_zero] using hden 0
    have hAR : R=-A := by
      dsimp [R,A]
      rw [sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),stdRoot_degenerate38]
      ring
    simp only [d,sub_self,zero_div,zero_mul,sub_zero,intervalIntegral.integral_const,
      sub_zero,Complex.real_smul,hAR]
    push_cast
    field_simp [hAz]
  · obtain ⟨u,hu,hA,hr⟩ := p2StdRoot_joukowski38 a b z hab hz
    have hp := p2Joukowski_poles38 hu
    have hd : d ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) (by norm_num)
    have hs := p2Joukowski_rational_integral38 u R hu hR
    have he : (∫ θ in (0:ℝ)..2*Real.pi,1/(A-d*(Real.cos θ:ℂ))) =
        circleIntegral (fun v : ℂ => (Complex.I/R)*((v-u⁻¹)⁻¹-(v-u)⁻¹)) 0 1 := by
      simp only [circleIntegral,smul_eq_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      let v : ℂ := circleMap 0 1 θ
      have hv : v ≠ 0 := by
        intro hv
        have hn : ‖v‖=1 := by simp [v]
        rw [hv,norm_zero] at hn
        norm_num at hn
      have hvu : v-u ≠ 0 := by
        apply sub_ne_zero.mpr
        intro hvu
        have hn : ‖v‖=1 := by simp [v]
        rw [hvu] at hn
        linarith
      have hvui : v-u⁻¹ ≠ 0 := by
        apply sub_ne_zero.mpr
        intro hvu
        have hn : ‖v‖=1 := by simp [v]
        have hl := mem_ball_zero_iff.mp hp.1
        rw [hvu] at hn
        linarith
      have hvc : v+v⁻¹=2*(Real.cos θ:ℂ) := p2UnitCircle_cosine38 θ
      have hdn : A-(d/2)*(v+v⁻¹) ≠ 0 := by
        convert hden θ using 1
        rw [hvc]
        ring
      have hf := p2Joukowski_partial_fractions38 A R d u v hA hr hd hp.2.2 hR hv hvu hvui hdn
      change 1/(A-d*(Real.cos θ:ℂ)) = deriv (circleMap 0 1) θ *
        ((Complex.I/R)*((v-u⁻¹)⁻¹-(v-u)⁻¹))
      have hf' : (Complex.I/R)*((v-u⁻¹)⁻¹-(v-u)⁻¹) =
          1/(Complex.I*v*(A-(d/2)*(v+v⁻¹))) := by
        simpa only [one_div] using hf.symm
      have hcden : A-(d/2)*(v+v⁻¹)=A-d*(Real.cos θ:ℂ) := by rw [hvc]; ring
      rw [hf',deriv_circleMap]
      change 1/(A-d*(Real.cos θ:ℂ))=
        (v*Complex.I)*(1/(Complex.I*v*(A-(d/2)*(v+v⁻¹))))
      rw [hcden]
      field_simp [hv,hden θ,Complex.I_ne_zero]
    exact he.trans hs.2.2

#print axioms p2UnitCircle_cosine38
#print axioms p2Joukowski_rational_integral38
#print axioms p2StdRoot_cosine_resolvent38
end
end NlsGge.GK38
