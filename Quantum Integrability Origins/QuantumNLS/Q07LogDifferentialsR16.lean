import QuantumNLS.RootMassInvolutionBatchR9
import QuantumNLS.RootProductSymbolAnalytic

/-! Exact logarithm differential identities derived from the normalized
multiplier equation, then bound to the actual full-mass Cauchy branch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter Topology
namespace QuantumNLS.Q07LogDifferentialsR16

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def first (f : E → ℂ) (u v : E) : ℂ := fderiv ℝ f u v

def second (f : E → ℂ) (u v w : E) : ℂ :=
  fderiv ℝ (fun x => first f x v) u w

def symbol (e : ℂ) (ell : E → ℂ) (u : E) : ℂ :=
  Complex.exp (ell u) + e*Complex.exp (-ell u)

def difference (e : ℂ) (ell : E → ℂ) (u : E) : ℂ :=
  Complex.exp (ell u) - e*Complex.exp (-ell u)

theorem symbol_first (e : ℂ) {ell : E → ℂ} {u : E}
    (hell : DifferentiableAt ℝ ell u) (v : E) :
    first (symbol e ell) u v = difference e ell u * first ell u v := by
  have hh := hell.hasFDerivAt.cexp.add ((hell.hasFDerivAt.neg.cexp).const_mul e)
  have hv := DFunLike.congr_fun hh.fderiv v
  change first (symbol e ell) u v = Complex.exp (ell u)*first ell u v +
    e*(Complex.exp (-ell u)*(-first ell u v)) at hv
  rw [hv]
  unfold difference
  ring

theorem difference_first (e : ℂ) {ell : E → ℂ} {u : E}
    (hell : DifferentiableAt ℝ ell u) (v : E) :
    first (difference e ell) u v = symbol e ell u * first ell u v := by
  have hh := hell.hasFDerivAt.cexp.sub ((hell.hasFDerivAt.neg.cexp).const_mul e)
  have hv := DFunLike.congr_fun hh.fderiv v
  change first (difference e ell) u v = Complex.exp (ell u)*first ell u v -
    e*(Complex.exp (-ell u)*(-first ell u v)) at hv
  rw [hv]
  unfold symbol
  ring

/-- The second derivative is obtained by differentiating the first identity;
no formula for either differential is an input. -/
theorem symbol_second (e : ℂ) {ell : E → ℂ} {u : E}
    (hell : ContDiffAt ℝ 2 ell u) (v w : E) :
    second (symbol e ell) u v w =
      symbol e ell u * first ell u w * first ell u v + difference e ell u * second ell u v w := by
  have hd : DifferentiableAt ℝ ell u := hell.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (difference e ell) u :=
    hd.cexp.sub (hd.neg.cexp.const_mul e)
  have hV : DifferentiableAt ℝ (fun x => first ell x v) u :=
    ((hell.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply (differentiableAt_const v)
  have heq : (fun x => first (symbol e ell) x v) =ᶠ[𝓝 u]
      (fun x => difference e ell x * first ell x v) := by
    filter_upwards [hell.eventually (by norm_num)] with x hx
    exact symbol_first e (hx.differentiableAt (by norm_num)) v
  have hh := hD.hasFDerivAt.mul hV.hasFDerivAt
  have hv := DFunLike.congr_fun hh.fderiv w
  change (fderiv ℝ (fun x => difference e ell x * first ell x v) u) w = _ at hv
  rw [← heq.fderiv_eq] at hv
  change second (symbol e ell) u v w = _ at hv
  simp only [add_apply, smul_apply, smul_eq_mul] at hv
  rw [show fderiv ℝ (difference e ell) u w = symbol e ell u * first ell u w from difference_first e hd w] at hv
  convert hv using 1
  simp only [first, second]
  ring

theorem log_differentials (e : ℂ) {ell : E → ℂ} {u : E}
    (hell : ContDiffAt ℝ 2 ell u) (hD : difference e ell u ≠ 0) (v w : E) :
    first ell u v = (difference e ell u)⁻¹ * first (symbol e ell) u v ∧
    second ell u v w =
      (difference e ell u)⁻¹ * second (symbol e ell) u v w -
        symbol e ell u * (difference e ell u)⁻¹ ^ 3 *
          first (symbol e ell) u v * first (symbol e ell) u w := by
  have hd := hell.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  constructor
  · rw [symbol_first e hd v, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  · rw [symbol_second e hell v w, symbol_first e hd v, symbol_first e hd w]
    field_simp [hD]
    ring

end Calculus

open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The normalized logarithm fixed by the actual full-mass measure. -/
def logarithm (hκ : 0 < κ) (z : ℂ) (u : L2T L) : ℂ := Complex.I * (κ : ℂ) * G hκ z u

def physicalDifference (hκ : 0 < κ) (z : ℂ) : L2T L → ℂ :=
  difference (Complex.exp (Complex.I*z*L)) (logarithm hκ z)

theorem logarithm_analytic (hκ : 0 < κ) {u : L2T L} {z : ℂ}
    (hp : RootCauchyJointR9.Regular κ (u,z)) :
    AnalyticAt ℝ (logarithm hκ z) u := by
  have ha := (RootCauchyJointR9.analyticAt_joint_regular hκ (u,z) hp).comp (f := fun v : L2T L => (v,z))
    (analyticAt_id.prod analyticAt_const)
  exact analyticAt_const.mul ha

/-- The local normalized multiplier equation at every nonreal point and
every real open-band crossing, for zero and nonunit physical profiles too. -/
theorem physical_symbol_eq (hκ : 0 < κ) {u : L2T L} {z : ℂ}
    (hp : RootCauchyJointR9.Regular κ (u,z)) :
    NormalizedTransfer.productSymbol L κ u z =
      symbol (Complex.exp (Complex.I*z*L)) (logarithm hκ z) u := by
  have hc := RootCauchyJointR9.cosine_regular hκ (u,z) hp
  have hf := PhysicalQuantumMeasure.cosine_fz L κ z (G hκ z u)
  change 2*Complex.cos ((L : ℂ)*z/2-(κ : ℂ)*G hκ z u) = _ at hc
  have he := hc.symm.trans hf
  have ht := RootTraceSymbolFinal.traceSymbol_all (L := L) hκ.le u z
  have hh := ht.trans he
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-(Complex.I*z*L/2))) at hh
  exact hh


/-- Both normalized multiplier branches expressed by the selected phase. -/
theorem physical_difference_phase (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    physicalDifference hκ z u = Complex.exp (Complex.I*z*L/2) *
      (Complex.exp (-DEF014PhaseAnalytic.selected hκ u z*Complex.I) -
        Complex.exp (DEF014PhaseAnalytic.selected hκ u z*Complex.I)) := by
  have h1 : Complex.exp (logarithm hκ z u) = Complex.exp (Complex.I*z*L/2) *
      Complex.exp (-DEF014PhaseAnalytic.selected hκ u z*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [logarithm, DEF014PhaseAnalytic.selected, SpatialTransfer.boundaryPhase, G]
    ring
  have h2 : Complex.exp (Complex.I*z*L) * Complex.exp (-logarithm hκ z u) =
      Complex.exp (Complex.I*z*L/2) * Complex.exp (DEF014PhaseAnalytic.selected hκ u z*Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp [logarithm, DEF014PhaseAnalytic.selected, SpatialTransfer.boundaryPhase, G]
    ring
  change Complex.exp (logarithm hκ z u) -
    Complex.exp (Complex.I*z*L) * Complex.exp (-logarithm hκ z u) = _
  rw [h1,h2]
  ring

theorem physical_difference_ne_zero (hκ : 0 < κ) {u : L2T L} {z : ℂ}
    (hp : RootCauchyJointR9.Regular κ (u,z)) : physicalDifference hκ z u ≠ 0 := by
  rw [physical_difference_phase]
  apply mul_ne_zero (Complex.exp_ne_zero _)
  intro hh
  have hs := Complex.two_sin (DEF014PhaseAnalytic.selected hκ u z)
  rw [hh, zero_mul] at hs
  have hsin : Complex.sin (DEF014PhaseAnalytic.selected hκ u z) = 0 :=
    (mul_eq_zero.mp hs).resolve_left (by norm_num)
  exact RootCauchyJointR9.sine_regular hκ (u,z) hp hsin

/-- Both source logarithm differential identities for the actual full-mass
Cauchy branch. The regularity and identities are proved, not supplied. -/
theorem physical_log_differentials (hκ : 0 < κ) {u : L2T L} {z : ℂ}
    (hp : RootCauchyJointR9.Regular κ (u,z)) (v w : L2T L) :
    first (logarithm hκ z) u v = (physicalDifference hκ z u)⁻¹ *
      first (fun x => NormalizedTransfer.productSymbol L κ x z) u v ∧
    second (logarithm hκ z) u v w = (physicalDifference hκ z u)⁻¹ *
      second (fun x => NormalizedTransfer.productSymbol L κ x z) u v w -
      NormalizedTransfer.productSymbol L κ u z * (physicalDifference hκ z u)⁻¹ ^ 3 *
        first (fun x => NormalizedTransfer.productSymbol L κ x z) u v *
        first (fun x => NormalizedTransfer.productSymbol L κ x z) u w := by
  have he : (fun x : L2T L => NormalizedTransfer.productSymbol L κ x z) =ᶠ[𝓝 u]
      symbol (Complex.exp (Complex.I*z*L)) (logarithm hκ z) := by
    have ho := (RootCauchyJointR9.isOpen_regular κ).preimage
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : L2T L => z)))
    filter_upwards [ho.mem_nhds hp] with x hx
    exact physical_symbol_eq hκ hx
  have h1 : ∀ a, first (fun x => NormalizedTransfer.productSymbol L κ x z) u a =
      first (symbol (Complex.exp (Complex.I*z*L)) (logarithm hκ z)) u a :=
    fun a => DFunLike.congr_fun he.fderiv_eq a
  have h2 : second (fun x => NormalizedTransfer.productSymbol L κ x z) u v w =
      second (symbol (Complex.exp (Complex.I*z*L)) (logarithm hκ z)) u v w := by
    have hv : (fun x => first (fun y => NormalizedTransfer.productSymbol L κ y z) x v) =ᶠ[𝓝 u]
        (fun x => first (symbol (Complex.exp (Complex.I*z*L)) (logarithm hκ z)) x v) :=
      he.fderiv.fun_comp (fun A => A v)
    exact DFunLike.congr_fun hv.fderiv_eq w
  rw [h1 v, h1 w, h2, physical_symbol_eq hκ hp]
  exact log_differentials _ ((logarithm_analytic hκ hp).contDiffAt)
    (physical_difference_ne_zero hκ hp) v w


/-- Spectral holomorphy through both half-planes and every real open band,
for the same actual normalized Cauchy logarithm. -/
theorem logarithm_spectral (hκ : 0 < κ) {u : L2T L} {z : ℂ}
    (hp : RootCauchyJointR9.Regular κ (u,z)) :
    DifferentiableAt ℂ (fun w => logarithm hκ w u) z :=
  (RootCauchyJointR9.differentiableAt_spectral_regular hκ (u,z) hp).const_mul _

/-- The reciprocal is the actual exponential of the negative Cauchy logarithm. -/
theorem multiplier_reciprocal (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    Complex.exp (logarithm hκ z u) ≠ 0 ∧
      (Complex.exp (logarithm hκ z u))⁻¹ = Complex.exp (-logarithm hκ z u) :=
  ⟨Complex.exp_ne_zero _, (Complex.exp_neg _).symm⟩

/-- The source discriminant-square identity for the normalized multiplier. -/
theorem physical_difference_square (hκ : 0 < κ) {u : L2T L} {z : ℂ}
    (hp : RootCauchyJointR9.Regular κ (u,z)) :
    physicalDifference hκ z u ^ 2 = NormalizedTransfer.productSymbol L κ u z ^ 2 -
      4*Complex.exp (Complex.I*z*L) := by
  rw [physical_symbol_eq hκ hp]
  have he : Complex.exp (logarithm hκ z u) * Complex.exp (-logarithm hκ z u) = 1 := by
    rw [← Complex.exp_add]
    simp
  unfold physicalDifference difference symbol
  linear_combination (-4*Complex.exp (Complex.I*z*L))*he

end QuantumNLS.Q07LogDifferentialsR16
