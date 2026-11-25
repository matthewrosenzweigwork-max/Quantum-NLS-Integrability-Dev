import QuantumNLS.Prop022OWeakIdentity

/-! PROP-022 takeover, stage O6a. The classical side of the covariance
argument. With J v = i v, the conjugated variational flow
  S'(t,s) = J⁻¹ ∘ S(t,s) ∘ J
solves d/dt S'(t,s) v = -i (a_t S'v - b_t conj S'v), i.e. the generator
`gen` of stage O4d, with the literal printed coefficients a_t, b_t.
This is derived from the printed linearized equation i dS/dt = a S + b conj S
proved in R124; no equation is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap Filter Topology
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022OClassical
open PhysicalTensor BetheCoefficientTransform Ext006KernelHilbertSchmidt Ext006BogoliubovAlg
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022VariationalR123
open Prop022PrintedCoefficientsR124 Prop022PairHSR122 Prop022OWeakIdentity
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

/-- Multiplication by i, as a real-linear equivalence. -/
def Jeq : L2T L ≃L[ℝ] L2T L where
  toFun x := Complex.I • x
  invFun x := (-Complex.I) • x
  map_add' x y := smul_add _ x y
  map_smul' r x := smul_comm Complex.I r x
  left_inv x := by
    change (-Complex.I) • Complex.I • x = x
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  right_inv x := by
    change Complex.I • (-Complex.I) • x = x
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  continuous_toFun := continuous_const_smul _
  continuous_invFun := continuous_const_smul _

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))

/-- The J-conjugated variational flow. -/
def Sp (t s : ℝ) : L2T L ≃L[ℝ] L2T L :=
  (Jeq.trans (flow B M A hA hB hs u₀ t s)).trans Jeq.symm

lemma Sp_apply (t s : ℝ) (v : L2T L) :
    Sp B M A hA hB hs u₀ t s v = (-Complex.I) • flow B M A hA hB hs u₀ t s (Complex.I • v) := rfl

lemma Sp_self (s : ℝ) (v : L2T L) : Sp B M A hA hB hs u₀ s s v = v := by
  rw [Sp_apply, flow_self, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

local notation "aₜ" t => numberCoefficient B (profile B M A hA hB hs u₀ t)
local notation "bₜ" t => pairCoefficient B (profile B M A hA hB hs u₀ t)

/-- The conjugated flow solves the generator equation with the printed coefficients. -/
theorem Sp_hasDerivAt (s t : ℝ) (v : L2T L) :
    HasDerivAt (fun r => Sp B M A hA hB hs u₀ r s v)
      (gen (aₜ t) (bₜ t) (Sp B M A hA hB hs u₀ t s v)) t := by
  have hd := flow_variational B M A hA hB hs u₀ s t (Complex.I • v)
  have hp := flow_printed_linearized B M A hA hB hs u₀ s t (Complex.I • v)
  rw [hd.deriv] at hp
  set D := fderiv ℝ (velocity B) (profile B M A hA hB hs u₀ t)
    (flow B M A hA hB hs u₀ t s (Complex.I • v))
  set X := flow B M A hA hB hs u₀ t s (Complex.I • v)
  have hD : D = (-Complex.I) • (numberOperator B (profile B M A hA hB hs u₀ t) X +
      pairKernel B (profile B M A hA hB hs u₀ t) (conjugation (physicalBasis L) X)) := by
    rw [← hp, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have hX : X = Complex.I • Sp B M A hA hB hs u₀ t s v := by
    rw [Sp_apply, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  have h := hd.const_smul (-Complex.I)
  refine h.congr_deriv ?_
  rw [hD, hX]
  change (-Complex.I) • (-Complex.I) • (aOp (aₜ t) (Complex.I • Sp B M A hA hB hs u₀ t s v) +
    bOp (bₜ t) (conjugation (physicalBasis L) (Complex.I • Sp B M A hA hB hs u₀ t s v))) = _
  rw [Prop022BlockEquationR124.conjugation_smul, Complex.conj_I, map_smul, map_smul, gen]
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  match_scalars <;> ring_nf <;> simp only [hI3, Complex.I_sq] <;> ring

/-- Coordinates of the conjugated flow applied to a fixed smearing. -/
def gco (s : ℝ) (h : H) (r : ℝ) : H :=
  (physicalBasis L).repr (Sp B M A hA hB hs u₀ r s ((physicalBasis L).repr.symm h))

lemma gco_self (s : ℝ) (h : H) : gco B M A hA hB hs u₀ s h s = h := by
  rw [gco, Sp_self, LinearIsometryEquiv.apply_symm_apply]

lemma gco_eq (s t : ℝ) (h : H) :
    gco B M A hA hB hs u₀ s h t =
      Prop022OWeylField.coordinateMap (Sp B M A hA hB hs u₀ t s) h := rfl

theorem gco_hasDerivAt (s : ℝ) (h : H) (t : ℝ) :
    HasDerivAt (gco B M A hA hB hs u₀ s h)
      (LamH (aₜ t) (bₜ t) (gco B M A hA hB hs u₀ s h t)) t := by
  have hd := Sp_hasDerivAt B M A hA hB hs u₀ s t ((physicalBasis L).repr.symm h)
  have hr := ((physicalBasis L).repr.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
    ).hasFDerivAt.comp_hasDerivAt t hd
  refine hr.congr_deriv ?_
  change (physicalBasis L).repr (gen _ _ _) = _
  rw [LamH, gco, LinearIsometryEquiv.symm_apply_apply]

end QuantumNLS.Prop022OClassical

#print axioms QuantumNLS.Prop022OClassical.gco_hasDerivAt
