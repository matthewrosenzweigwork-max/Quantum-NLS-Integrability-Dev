import QuantumNLS.LOCAL009R23Final
import QuantumNLS.BetheSpectralCharges

/-! LOCAL-016 quantum input: exact 2π return for the literal bounded
integer occupation operator from LOCAL-009, including the vacuum sector.
This proves an operator identity, not an Egorov application. -/
set_option autoImplicit false
noncomputable section
open Complex Set
open scoped InnerProductSpace
namespace QuantumNLS.IndexedQuantumR27b
open BetheLabels BetheCoefficientTransform
open LOCAL009R23PhysicalInverse LOCAL009R23Final

def operatorExp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) : H →L[ℂ] H := NormedSpace.exp A

theorem operatorExp_zero_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (c : ℂ) : operatorExp (c • (0 : H →L[ℂ] H)) = 1 := by
  rw [smul_zero,operatorExp,NormedSpace.exp_zero]

theorem exp_eigen {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (x : H) (z : ℂ) (hx : A x = z • x) :
    NormedSpace.exp A x = Complex.exp z • x := by
  have hp (k : ℕ) : (A^k) x = z^k • x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp,ih,map_smul,hx,smul_smul,pow_succ]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL
    (ContinuousLinearMap.apply ℂ H x)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).smul_const x
  apply h1.unique
  simpa only [ContinuousLinearMap.apply_apply,smul_apply,hp,
    smul_smul,smul_eq_mul,← Complex.exp_eq_exp_ℂ] using h2

variable {L κ ε : ℝ} [Fact (0 < L)]

def propagator (hκ : 0 < κ) (hε : 0 < ε) (n : ℤ) (N : ℕ) (t : ℝ) :
    Sector L N →L[ℂ] Sector L N :=
  operatorExp ((-((t : ℂ)*Complex.I)) • occupationCount L κ ε hκ hε n N)

theorem propagator_eigen (hκ : 0 < κ) (hε : 0 < ε) {N : ℕ} (hN : 0 < N)
    (n : ℤ) (t : ℝ) (m : MArr N) :
    propagator (L := L) hκ hε n N t (basis (L := L) hκ hε hN m) =
      Complex.exp (-((t : ℂ)*Complex.I)*(m.1 n : ℂ)) • basis (L := L) hκ hε hN m := by
  apply exp_eigen
  rw [smul_apply,occupationCount_eigen hκ hε hN,smul_smul]

theorem propagator_period (hκ : 0 < κ) (hε : 0 < ε) (n : ℤ) (N : ℕ) :
    propagator (L := L) hκ hε n N (2*Real.pi) = 1 := by
  by_cases hN : 0 < N
  · apply NormalityBridge.clm_ext_basis (basis hκ hε hN)
    intro m
    rw [propagator_eigen hκ hε hN]
    have he : Complex.exp (-(((2*Real.pi : ℝ) : ℂ)*Complex.I)*(m.1 n : ℂ)) = 1 := by
      have hz : -(((2*Real.pi : ℝ) : ℂ)*Complex.I)*(m.1 n : ℂ) =
          ((-(m.1 n : ℤ) : ℤ) : ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
      rw [hz,Complex.exp_int_mul_two_pi_mul_I]
    rw [he,one_smul]
    rfl
  · have hzero : N = 0 := by omega
    subst N
    have hcount : occupationCount L κ ε hκ hε n 0 = 0 := by simp [occupationCount]
    unfold propagator
    rw [hcount]
    exact operatorExp_zero_smul _

end QuantumNLS.IndexedQuantumR27b
#print axioms QuantumNLS.IndexedQuantumR27b.propagator_period
