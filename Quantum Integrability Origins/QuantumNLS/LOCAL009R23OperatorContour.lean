import QuantumNLS.LOCAL009R23PhysicalInverse

/-! The norm-valued rectangle integral and its action on each actual Bethe
vector. The integrand uses CFC and the total operator-norm derivative. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
open Complex Set Metric MeasureTheory Interval Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.LOCAL009R23OperatorContour
open QuantumNLS.LOCAL009R23PhysicalInverse QuantumNLS.LOCAL009R23DiagonalAnalytic
  QuantumNLS.LOCAL009R22LiteralScalar QuantumNLS.LOCAL009R22Geometry
  QuantumNLS.LOCAL009R22Ratio QuantumNLS.LOCAL009R22Integrand
  QuantumNLS.LOCAL009R22Derivative QuantumNLS.Ext025A7
  QuantumNLS.BetheLabels QuantumNLS.PeriodReconstruction

variable {L κ M ε : ℝ} [Fact (0 < L)] {N : ℕ}

def quotientOp (L κ M ε : ℝ) [Fact (0 < L)] (N : ℕ) (z : ℂ) : Sector L N →L[ℂ] Sector L N :=
  normalCalc (ratio κ L z) (inverseOp L κ M ε N z)

def integrand (L κ M ε : ℝ) [Fact (0 < L)] (N : ℕ) (z : ℂ) : Sector L N →L[ℂ] Sector L N :=
  inverseOp L κ M ε N z + ((κ^2*ε/2 : ℝ) : ℂ) •
    (quotientOp L κ M ε N z * deriv (inverseOp L κ M ε N) z)

def rectIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℂ → E) (a b h : ℝ) : E :=
  (∫ x in a..b, F (x + ((-h : ℝ) : ℂ)*I)) - (∫ x in a..b, F (x+h*I)) +
    I • (∫ y in (-h)..h, F (b+y*I)) - I • (∫ y in (-h)..h, F (a+y*I))

def approximation (L κ M ε : ℝ) [Fact (0 < L)] (n : ℤ) (N : ℕ) : Sector L N →L[ℂ] Sector L N :=
  (2*Real.pi*I)⁻¹ • rectIntegral (integrand L κ M ε N)
    (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operator_analytic {F : ℂ → H →L[ℂ] H} {U : Set ℂ} {z : ℂ}
    (hd : DifferentiableOn ℂ F U) (hz : U ∈ 𝓝 z) : AnalyticAt ℂ F z :=
  hd.analyticAt hz

theorem correction_continuous (F Q : ℂ → H →L[ℂ] H) (c : ℂ) {z : ℂ}
    (hF : ContinuousAt F z) (hQ : ContinuousAt Q z)
    (hD : ContinuousAt (deriv F) z) :
    ContinuousAt (fun w => F w + c • (Q w * deriv F w)) z :=
  hF.add ((hQ.mul hD).const_smul c)

theorem norm_eigen_le (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (a : ℂ)
    (i : ι) (he : A (b i) = a • b i) : ‖a‖ ≤ ‖A‖ := by
  have h := A.le_opNorm (b i)
  rw [he,norm_smul,b.orthonormal.1 i,mul_one,mul_one] at h
  exact h

/-- Bounded analytic diagonal families admit the prescribed CFC quotient in
operator norm. All helper hypotheses are discharged in quotient_spec below. -/
theorem quotient_lift (b : HilbertBasis ι ℂ H) (F : ℂ → H →L[ℂ] H)
    (t : ι → ℂ → ℂ) {κ L R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (_hR : 0 < R) (hr : κ*R ≤ 1/1000) (hU : IsOpen U)
    (hexp : ∀ w ∈ U, ‖Complex.exp (I*w*L)‖ ≤ 8)
    (hgap : ∀ w ∈ U, 1/2 ≤ ‖1-Complex.exp (I*w*L)‖)
    (he : ∀ w ∈ U, ∀ m, F w (b m) = t m w • b m)
    (hd : ∀ w ∈ U, DifferentiableAt ℂ F w)
    (hb : ∀ w ∈ U, ‖F w‖ ≤ R) {z : ℂ} (hz : z ∈ U) :
    (∀ m, normalCalc (ratio κ L z) (F z) (b m) = ratio κ L z (t m z) • b m) ∧
    ContinuousAt (fun w => normalCalc (ratio κ L w) (F w)) z := by
  have ht (m : ι) (w : ℂ) (hw : w ∈ U) : ‖t m w‖ ≤ R :=
    (norm_eigen_le b _ _ m (he w hw m)).trans (hb w hw)
  have hn (w : ℂ) (hw : w ∈ U) : IsStarNormal (F w) :=
    ⟨QuantumNLS.NormalityBridge.IsDiag.normal
      (fun m => ⟨t m w,he w hw m⟩ : QuantumNLS.NormalityBridge.IsDiag b (F w))⟩
  have hc (w : ℂ) (hw : w ∈ U) : ContinuousOn (ratio κ L w) (spectrum ℂ (F w)) := by
    intro v hv
    have hvbound : ‖v‖ ≤ R := by
      calc
        _ ≤ ‖F w‖*‖(1 : H →L[ℂ] H)‖ := spectrum.norm_le_norm_mul_of_mem hv
        _ ≤ ‖F w‖*1 := by
          gcongr
          exact ContinuousLinearMap.norm_id_le
        _ ≤ R := by simpa using hb w hw
    exact (ratio_hasDerivAt hκ hr (hexp w hw) (hgap w hw)
      (mem_closedBall_zero_iff.mpr hvbound)).continuousAt.continuousWithinAt
  have heigen (w : ℂ) (hw : w ∈ U) (m : ι) :
      normalCalc (ratio κ L w) (F w) (b m) = ratio κ L w (t m w) • b m :=
    QuantumNLS.Prop020Diag.cfc_eigen (hn w hw) (he w hw m)
      (b.orthonormal.ne_zero m) _ (hc w hw)
  have hta : ∀ m w, w ∈ U → AnalyticAt ℂ (t m) w := by
    intro m w hw
    have hdiff : DifferentiableOn ℂ F U := fun v hv => (hd v hv).differentiableWithinAt
    have ha := operator_analytic hdiff (hU.mem_nhds hw)
    let ev : (H →L[ℂ] H) →L[ℂ] ℂ :=
      (innerSL ℂ (b m)).comp (ContinuousLinearMap.apply ℂ H (b m))
    have h := (ev.analyticAt (F w)).comp ha
    have heq : (fun v => ev (F v)) =ᶠ[𝓝 w] t m := by
      filter_upwards [hU.mem_nhds hw] with v hv
      change ⟪b m,F v (b m)⟫_ℂ = t m v
      rw [he v hv m,inner_smul_right,inner_self_eq_one_of_norm_eq_one (b.orthonormal.1 m),mul_one]
    exact h.congr heq
  have hqa : ∀ m w, w ∈ U → AnalyticAt ℂ (fun v => ratio κ L v (t m v)) w := by
    intro m w hw
    have hden : spectralDerivative κ L w (t m w) ≠ 0 := norm_ne_zero_iff.mp (by
      have hlow := derivative_lower hκ hr (hexp w hw) (hgap w hw)
        (mem_closedBall_zero_iff.mpr (ht m w hw))
      linarith)
    have htm := hta m w hw
    have hf : AnalyticAt ℂ (fun v => spectralMap κ L v (t m v)) w := by
      unfold spectralMap
      fun_prop
    have hder : AnalyticAt ℂ (fun v => spectralDerivative κ L v (t m v)) w := by
      unfold spectralDerivative
      fun_prop
    exact hf.div hder hden
  have hbound : ∀ m w, w ∈ U → ‖ratio κ L w (t m w)‖ ≤ ratioBound κ R :=
    fun m w hw => ratio_norm_le hκ hr (hexp w hw) (hgap w hw)
      (mem_closedBall_zero_iff.mpr (ht m w hw))
  have hl := analytic_lift b (fun w => normalCalc (ratio κ L w) (F w))
    (fun m v => ratio κ L v (t m v)) hU
    (by unfold ratioBound; positivity) heigen hqa hbound hz
  exact ⟨heigen z hz,hl.1.continuousAt⟩

/-- CFC quotient agrees with f_z/f'_z at every basis entry and varies
continuously in operator norm. -/
theorem quotient_spec (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000)
    (hN : 0 < N) (hε : 0 < ε) (hεM : ε ≤ M) (hbudget : ε*N ≤ M)
    (n : ℤ) {z : ℂ} (hz : z ∈ band (momentum L n) (halfWidth L)) :
    (∀ m, quotientOp L κ M ε N z (basis hκ hε hN m) =
      ratio κ L z (inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m) z) • basis hκ hε hN m) ∧
    ContinuousAt (quotientOp L κ M ε N) z := by
  have hL : 0 < L := Fact.out
  let U := band (momentum L n) (halfWidth L)
  let t (m : MArr N) := inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m)
  have hR : 0 < radius L M := by unfold radius halfWidth; positivity
  have hr : κ*radius L M ≤ 1/1000 := by
    have hs := source_small hsmall
    calc
      κ*radius L M = 2*(κ*M/(halfWidth L/2)) := by unfold radius; ring
      _ ≤ 1/1000 := by linarith
  have hexp (w : ℂ) (hw : w ∈ U) := source_phase_bound (Fact.out : 0 < L) n hw
  have hgap (w : ℂ) (hw : w ∈ U) := source_gap_bound (Fact.out : 0 < L) n hw
  have hs (w : ℂ) (hw : w ∈ U) := inverseOp_spec hκ hM hsmall hN hε hεM hbudget n hw
  dsimp only [quotientOp]
  exact quotient_lift (basis hκ hε hN) (inverseOp L κ M ε N) t
    hκ hR hr (band_open _ _) hexp hgap
    (fun w hw => (hs w hw).1) (fun w hw => (hs w hw).2.1)
    (fun w hw => (hs w hw).2.2.2) hz


/-- Printed operator integrand, with all commuting factors and the full
operator derivative, acts by the frozen scalar integrand. -/
theorem integrand_spec (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000)
    (hN : 0 < N) (hε : 0 < ε) (hεM : ε ≤ M) (hbudget : ε*N ≤ M)
    (n : ℤ) {z : ℂ} (hz : z ∈ band (momentum L n) (halfWidth L)) :
    (∀ m, integrand L κ M ε N z (basis hκ hε hN m) =
      correctedIntegrand κ L M (halfWidth L/2) ε (arrRoots L (κ*ε) m) z • basis hκ hε hN m) ∧
    ContinuousAt (integrand L κ M ε N) z := by
  have hs := inverseOp_spec hκ hM hsmall hN hε hεM hbudget n hz
  have hq := quotient_spec hκ hM hsmall hN hε hεM hbudget n hz
  constructor
  · intro m
    simp [integrand,mul_apply_eq_comp,hs.1 m,hs.2.2.1 m,hq.1 m,
      map_smul,smul_smul,← add_smul,correctedIntegrand,radius,mul_comm,mul_left_comm]
  · have hd : DifferentiableOn ℂ (inverseOp L κ M ε N) (band (momentum L n) (halfWidth L)) :=
      fun w hw => (inverseOp_spec hκ hM hsmall hN hε hεM hbudget n hw).2.1.differentiableWithinAt
    have ha := operator_analytic hd ((band_open _ _).mem_nhds hz)
    exact correction_continuous (inverseOp L κ M ε N) (quotientOp L κ M ε N)
      ((κ^2*ε/2 : ℝ) : ℂ) hs.2.1.continuousAt hq.2 ha.deriv.continuousAt


/-- All factors in the printed correction commute in the physical sector. -/
theorem factors_commute (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000)
    (hN : 0 < N) (hε : 0 < ε) (hεM : ε ≤ M) (hbudget : ε*N ≤ M)
    (n : ℤ) {z : ℂ} (hz : z ∈ band (momentum L n) (halfWidth L)) :
    Commute (inverseOp L κ M ε N z) (quotientOp L κ M ε N z) ∧
    Commute (inverseOp L κ M ε N z) (deriv (inverseOp L κ M ε N) z) ∧
    Commute (quotientOp L κ M ε N z) (deriv (inverseOp L κ M ε N) z) := by
  have hs := inverseOp_spec hκ hM hsmall hN hε hεM hbudget n hz
  have hq := quotient_spec hκ hM hsmall hN hε hεM hbudget n hz
  have ht : QuantumNLS.NormalityBridge.IsDiag (basis hκ hε hN) (inverseOp L κ M ε N z) :=
    fun m => ⟨_,hs.1 m⟩
  have hq' : QuantumNLS.NormalityBridge.IsDiag (basis hκ hε hN) (quotientOp L κ M ε N z) :=
    fun m => ⟨_,hq.1 m⟩
  have hd : QuantumNLS.NormalityBridge.IsDiag (basis hκ hε hN) (deriv (inverseOp L κ M ε N) z) :=
    fun m => ⟨_,hs.2.2.1 m⟩
  exact ⟨ht.commute hq',ht.commute hd,hq'.commute hd⟩


theorem horizontal_mem {a b h x y : ℝ} (hx : x ∈ Icc a b) (hy : y = -h ∨ y = h) :
    (x : ℂ)+y*I ∈ Gam a b h := by
  left
  simpa using And.intro hx hy

theorem vertical_mem {a b h x y : ℝ} (hy : y ∈ Icc (-h) h) (hx : x = a ∨ x = b) :
    (x : ℂ)+y*I ∈ Gam a b h := by
  right
  simpa using And.intro hy hx

/-- Norm integrability is discharged from continuity on the contour; applying
an operator integral to a fixed eigenvector commutes with all four integrals. -/
theorem rectIntegral_eigen (F : ℂ → H →L[ℂ] H) (f : ℂ → ℂ) (v : H)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hF : ∀ z ∈ Gam a b h, ContinuousAt F z)
    (he : ∀ z ∈ Gam a b h, F z v = f z • v) :
    rectIntegral F a b h v = QuantumNLS.LabelExactPeriod.rectIntegral f a b h • v := by
  have hhor (y : ℝ) (hy : y = -h ∨ y = h) :
      IntervalIntegrable (fun x : ℝ => F (x+y*I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ((hF _ (horizontal_mem hx hy)).comp (f := fun u : ℝ => (u : ℂ)+y*I) (x := x)
      (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ)+y*I) x)).continuousWithinAt
  have hver (x : ℝ) (hx : x = a ∨ x = b) :
      IntervalIntegrable (fun y : ℝ => F (x+y*I)) volume (-h) h := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le (by linarith : -h ≤ h)] at hy
    exact ((hF _ (vertical_mem hy hx)).comp (f := fun u : ℝ => (x : ℂ)+u*I) (x := y)
      (by fun_prop : ContinuousAt (fun y : ℝ => (x : ℂ)+y*I) y)).continuousWithinAt
  have ehor (y : ℝ) (hy : y = -h ∨ y = h) :
      (∫ x in a..b, F (x+y*I)) v = (∫ x in a..b, f (x+y*I)) • v := by
    rw [ContinuousLinearMap.intervalIntegral_apply (hhor y hy)]
    rw [intervalIntegral.integral_congr (fun x hx => he _ (horizontal_mem
      (by simpa [uIcc_of_le hab] using hx) hy))]
    exact intervalIntegral.integral_smul_const _ _
  have ever (x : ℝ) (hx : x = a ∨ x = b) :
      (∫ y in (-h)..h, F (x+y*I)) v = (∫ y in (-h)..h, f (x+y*I)) • v := by
    rw [ContinuousLinearMap.intervalIntegral_apply (hver x hx)]
    rw [intervalIntegral.integral_congr (fun y hy => he _ (vertical_mem
      (by simpa [uIcc_of_le (by linarith : -h ≤ h)] using hy) hx))]
    exact intervalIntegral.integral_smul_const _ _
  simp only [rectIntegral,QuantumNLS.LabelExactPeriod.rectIntegral,sub_apply,add_apply,smul_apply]
  rw [ehor (-h) (Or.inl rfl),ehor h (Or.inr rfl),ever b (Or.inr rfl),ever a (Or.inl rfl)]
  simp only [sub_smul,add_smul,smul_smul,smul_eq_mul]

/-- The literal printed operator contour integral equals the frozen scalar
contour expression on every actual Bethe vector. -/
theorem approximation_eigen (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000)
    (hN : 0 < N) (hε : 0 < ε) (hεM : ε ≤ M) (hbudget : ε*N ≤ M)
    (n : ℤ) (m : MArr N) :
    approximation L κ M ε n N (basis hκ hε hN m) =
      scalarA κ L M ε n (arrRoots L (κ*ε) m) • basis hκ hε hN m := by
  have hL : 0 < L := Fact.out
  have ha : 0 < halfWidth L := by unfold halfWidth; positivity
  have hb {z : ℂ} (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
      z ∈ band (momentum L n) (halfWidth L) :=
    contour_ball_subset_band ha hz (mem_closedBall_self (by positivity))
  unfold approximation
  rw [smul_apply,rectIntegral_eigen _ _ (basis hκ hε hN m) (by linarith) ha.le
    (fun z hz => (integrand_spec hκ hM hsmall hN hε hεM hbudget n (hb hz)).2)
    (fun z hz => (integrand_spec hκ hM hsmall hN hε hεM hbudget n (hb hz)).1 m),smul_smul]
  rfl

end QuantumNLS.LOCAL009R23OperatorContour
