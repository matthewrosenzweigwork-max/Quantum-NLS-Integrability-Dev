import QuantumNLS.Prop022OCovariance
import QuantumNLS.Prop022BD02R122

/-! PROP-022 takeover, stage O7a. Weyl conventions and vacuum transfer.

* The printed Weyl operator is W(v) = exp(a*(v) - a(v)). The reviewed
  EXT-006 source Weyl operator is sourceWeyl f = exp(i(a*(f) + a(f))).
  Since i(a*(-iv) + a(-iv)) = a*(v) - a(v) (a(.) is antilinear), the printed
  W(v) is `printedWeyl v := sourceWeyl ((-i) • v)`; the generator identity
  is proved on the smooth domain below.
* V implements S in the printed sense, V W(v) V⁻¹ = W(S v), exactly when V is
  a source-Weyl implementer of S' = J⁻¹ S J (J = multiplication by i).
* The beta block of S' is minus the beta block of S, and S' is symplectic
  iff S is; hence BD-02 applied at S' gives the printed number identity
  with the ORIGINAL beta(t,0). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.Prop022OVacuum
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext006KernelHilbertSchmidt Ext006SourceWeylR44a Ext006GlobalCovarianceR43a
open Ext006SourceOrientationR37a Ext006ReorientationR42a Ext006PhysQuasifree
open Ext006PhysFockCoord Ext006NumberPhase Ext006NaturalWeylR44a Ext006PhysSymplectic
open Ext006BogoliubovAlg Ext006SmoothOperatorsR34a Ext006StrongFieldR41a
open Prop022OClassical Prop022OCovariance Prop022FockPropagatorR122
variable {L : ℝ} [Fact (0 < L)]

/-! ### The printed Weyl operator -/

/-- The printed Weyl operator W(v) = exp(a*(v) - a(v)). -/
def printedWeyl (v : L2T L) : Fock L ≃ₗᵢ[ℂ] Fock L := sourceWeyl ((-Complex.I) • v)

/-- Generator identity: i times the source field of -i v is a*(v) - a(v). -/
theorem printedWeyl_generator (v : L2T L) (w : D) :
    Complex.I • (field ((physicalBasis L).repr ((-Complex.I) • v)) w).1 =
      (C ((physicalBasis L).repr v) w).1 - (A ((physicalBasis L).repr v) w).1 := by
  rw [map_smul]
  simp only [field, LinearMap.add_apply, Submodule.coe_add, Ext006InverseGraphsR36a.A_smul,
    Ext006InverseGraphsR36a.C_smul, LinearMap.smul_apply, Submodule.coe_smul]
  rw [show star (-Complex.I) = Complex.I by simp]
  rw [smul_add, smul_smul, smul_smul, Complex.I_mul_I, mul_neg, Complex.I_mul_I, neg_neg,
    one_smul, neg_one_smul]
  abel

/-- Printed implementation from source-Weyl implementation at J⁻¹ S J. -/
theorem printed_of_source (S : L2T L ≃L[ℝ] L2T L) (U : Fock L ≃ₗᵢ[ℂ] Fock L)
    (hU : SourceWeylImplementer S U) (S0 : L2T L → L2T L)
    (hS0 : ∀ v, S ((-Complex.I) • v) = (-Complex.I) • S0 v) :
    ∀ v x, U (printedWeyl v (U.symm x)) = printedWeyl (S0 v) x := by
  intro v x
  rw [printedWeyl, printedWeyl, hU, hS0]

lemma Sp_negI (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : Prop022FactorialCoefficientsR115.FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L)) (t s : ℝ) (v : L2T L) :
    Sp B M A hA hB hs u₀ t s ((-Complex.I) • v) =
      (-Complex.I) • Prop022VariationalR123.flow B M A hA hB hs u₀ t s v := by
  rw [Sp_apply, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

/-! ### Symplecticity and the beta block of J⁻¹ S J -/

lemma Sp_symplectic (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : Prop022FactorialCoefficientsR115.FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L)) (t s : ℝ) :
    Ext006SymplecticKernel.Symplectic (Sp B M A hA hB hs u₀ t s).toContinuousLinearMap := by
  intro x y
  have h := Prop022SymplecticR123.flow_symplectic B M A hA hB hs u₀ t s (Complex.I • x)
    (Complex.I • y)
  change (⟪(-Complex.I) • Prop022VariationalR123.flow B M A hA hB hs u₀ t s (Complex.I • x),
    (-Complex.I) • Prop022VariationalR123.flow B M A hA hB hs u₀ t s (Complex.I • y)⟫_ℂ).im = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  change (_ * ⟪(Prop022VariationalR123.flow B M A hA hB hs u₀ t s).toContinuousLinearMap
    (Complex.I • x), (Prop022VariationalR123.flow B M A hA hB hs u₀ t s).toContinuousLinearMap
    (Complex.I • y)⟫_ℂ).im = _
  rw [show (starRingEnd ℂ) (-Complex.I) * -Complex.I = 1 by simp, one_mul, h,
    inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_I, neg_mul, Complex.I_mul_I,
    neg_neg, one_mul]

lemma beta_Sp (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : Prop022FactorialCoefficientsR115.FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L)) (t s : ℝ) (x : L2T L) :
    beta (physicalBasis L) (Sp B M A hA hB hs u₀ t s) x =
      -beta (physicalBasis L) (Prop022VariationalR123.flow B M A hA hB hs u₀ t s) x := by
  change (1/2 : ℝ) • (Sp B M A hA hB hs u₀ t s (conjugation (physicalBasis L) x) +
      Complex.I • Sp B M A hA hB hs u₀ t s (Complex.I • conjugation (physicalBasis L) x)) =
    -((1/2 : ℝ) • (Prop022VariationalR123.flow B M A hA hB hs u₀ t s (conjugation (physicalBasis L) x) +
      Complex.I • Prop022VariationalR123.flow B M A hA hB hs u₀ t s
        (Complex.I • conjugation (physicalBasis L) x)))
  rw [Sp_apply, Sp_apply, show Complex.I • Complex.I • conjugation (physicalBasis L) x =
    -conjugation (physicalBasis L) x by rw [smul_smul, Complex.I_mul_I, neg_one_smul], map_neg,
    ← smul_neg]
  congr 1
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

lemma hsSq_neg (X : L2T L →L[ℂ] L2T L) :
    TraceClass.hsSq (physicalBasis L) (-X) = TraceClass.hsSq (physicalBasis L) X := by
  simp only [TraceClass.hsSq, ContinuousLinearMap.neg_apply, norm_neg]

lemma hsSq_beta_Sp (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : Prop022FactorialCoefficientsR115.FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L)) (t s : ℝ) :
    TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) (Sp B M A hA hB hs u₀ t s)) =
      TraceClass.hsSq (physicalBasis L) (Prop022VariationalR123.betaBlock B M A hA hB hs u₀ t s) := by
  have he : beta (physicalBasis L) (Sp B M A hA hB hs u₀ t s) =
      -Prop022VariationalR123.betaBlock B M A hA hB hs u₀ t s := by
    apply ContinuousLinearMap.ext
    intro x
    rw [beta_Sp]
    rfl
  rw [he, hsSq_neg]

/-! ### Phase invariance of the pure quasifree predicate -/

lemma heisAnn_phase (U : Fock L ≃ₗᵢ[ℂ] Fock L) (A B : H →L[ℂ] H) (hU : HeisAnn U A B)
    (z : ℂ) (hz : ‖z‖ = 1) : HeisAnn (phaseUnitary U z hz) A B := by
  intro d n m u w hu hw
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have h := hU d n m (z⁻¹ • u) (z⁻¹ • w)
    (fun c => by
      rw [lp.coeFn_smul, Pi.smul_apply, hu c, phaseUnitary_apply, inner_smul_right,
        smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul])
    (fun c => by
      rw [lp.coeFn_smul, Pi.smul_apply, hw c, phaseUnitary_apply, inner_smul_right,
        smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul])
  rw [phaseUnitary_apply, inner_smul_right, h, map_smul, map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

lemma heisCre_phase (U : Fock L ≃ₗᵢ[ℂ] Fock L) (A B : H →L[ℂ] H) (hU : HeisCre U A B)
    (z : ℂ) (hz : ‖z‖ = 1) : HeisCre (phaseUnitary U z hz) A B := by
  intro d n m u w hu hw
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have h := hU d n m (z⁻¹ • u) (z⁻¹ • w)
    (fun c => by
      rw [lp.coeFn_smul, Pi.smul_apply, hu c, phaseUnitary_apply, inner_smul_right,
        smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul])
    (fun c => by
      rw [lp.coeFn_smul, Pi.smul_apply, hw c, phaseUnitary_apply, inner_smul_right,
        smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul])
  rw [phaseUnitary_apply, inner_smul_right, h, map_smul, map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Vacuum conclusions for EVERY source-Weyl implementer of a symplectic map
with Hilbert--Schmidt beta block. -/
theorem implementer_vacuum (S : L2T L ≃L[ℝ] L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (V : Fock L ≃ₗᵢ[ℂ] Fock L) (hV : SourceWeylImplementer S V) :
    PhysicalQuasifreeSource (V vac) ∧ ‖V vac‖ = 1 ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (V vac) =
        TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (V vac) ≠ ⊤ := by
  obtain ⟨_, _, _, _, hall⟩ := Prop022BD02R122.PROP022_BD02_forward_implementer_and_vacuum_R122 S hS hβ
  obtain ⟨U, hAnn, hCre, _, hcov⟩ := original_source_bounded_covariance S hS hβ
  have hU : SourceWeylImplementer S U := by
    intro f x
    simp only [sourceWeyl_eq]
    exact hcov f 1 x
  obtain ⟨z, hz, hVz⟩ := sourceWeyl_unique_phase S U V hU hV
  have hterm := hall V hV
  refine ⟨⟨phaseUnitary U z hz, actualA (physicalBasis L) (reorient S),
    actualB (physicalBasis L) (reorient S),
    actual_blocks_symplectic (physicalBasis L) (reorient S) (reorient_symplectic S hS),
    heisAnn_phase U _ _ hAnn z hz, heisCre_phase U _ _ hCre z hz, by rw [hVz, phaseUnitary_apply]⟩,
    ?_, hterm.2.1, hterm.2.2⟩
  rw [LinearIsometryEquiv.norm_map, Ext006VacuumNumberR30a.vac_norm]

end QuantumNLS.Prop022OVacuum

#print axioms QuantumNLS.Prop022OVacuum.implementer_vacuum
#print axioms QuantumNLS.Prop022OVacuum.hsSq_beta_Sp
#print axioms QuantumNLS.Prop022OVacuum.printedWeyl_generator
