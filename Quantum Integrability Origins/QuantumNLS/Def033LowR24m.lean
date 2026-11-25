import QuantumNLS.Def033CoreR24m
import QuantumNLS.REF88PrintedChart
import QuantumNLS.Def024Order2Joint

/-! DEF-033 low orders, from the accepted global chart covariance and staged
DEF-024. No hierarchy predecessor is required for orders zero and one. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open MeasureTheory Filter Topology
namespace QuantumNLS.Def033LowR24m
open QuantumNLS.PhysicalTensor QuantumNLS.REF88Chart QuantumNLS.REF88PrintedChart
open QuantumNLS.Def033CoreR24m QuantumNLS.ClassicalCharges QuantumNLS.PhysicalProductPreparation
open QuantumNLS.Def024LowFlows
variable {L κ : ℝ} [Fact (0 < L)]

/-- Extract both literal covariance identities from the accepted global compatibility theorem. -/
theorem low_covariance (hκ : 0 < κ) {w : L2T L → K} (hw : PrintedChart hκ w)
    (u : L2T L) (n : ℤ) :
    (∀ γ : ℝ, w (Complex.exp ((γ : ℂ) * Complex.I) • u) n =
      Complex.exp ((γ : ℂ) * Complex.I) * w u n) ∧
    (∀ y : ℝ, w (QuantumNLS.BornTranslation.trans y u) n =
      Complex.exp (Complex.I * ((QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) * (y : ℂ)) * w u n) := by
  obtain ⟨d, CL, hd, hCL, Φl, Ψl, hl, ⟨Φ, Ψ, hf⟩, hall⟩ :=
    QuantumNLS.GlobalCompatR47a.global_compatibility L
  obtain ⟨hκC, -, -⟩ := hall Φ Ψ hf
  obtain ⟨hcov, -, -, -, -, -, -, huniq, -⟩ := hκC κ hκ
  have he := huniq w hw.symp hw.analytic hw.moduli hw.fourier hw.conj
  rw [he]
  exact ⟨(hcov u n).1, (hcov u n).2.1⟩

/-- In physical L², the order-zero frequency is 1 on every active coordinate. -/
theorem active_zero (hκ : 0 < κ) {w : L2T L → K} (hw : PrintedChart hκ w)
    (u : L2T L) (n : ℤ) (hn : 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) :
    ActiveFrequency (fun t => w (Complex.exp (-Complex.I * (t : ℂ)) • u) n) (w u n) 1 := by
  refine ⟨nonzero_of_action (hw.moduli u n) hn, fun t => ?_⟩
  have h := (low_covariance hκ hw u n).1 (-t)
  convert h using 1 <;> simp only [phase, mul_one, Complex.ofReal_neg] <;> congr 2 <;> ring

/-- Translation is u(x-t); covariance uses u(x+y), hence y=-t.
The frequency is +2πn/L, with no reflected sign or factor of two. -/
theorem active_one (hκ : 0 < κ) {w : L2T L → K} (hw : PrintedChart hκ w)
    (u : L2T L) (n : ℤ) (hn : 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) :
    ActiveFrequency (fun t => w (QuantumNLS.BornTranslation.trans (-t) u) n) (w u n)
      (QuantumNLS.LocalSpectral.pm L n) := by
  refine ⟨nonzero_of_action (hw.moduli u n) hn, fun t => ?_⟩
  have h := (low_covariance hκ hw u n).2 (-t)
  refine h.trans ?_
  congr 1
  unfold phase
  congr 1
  push_cast
  ring

/-- The L² embedding commutes with the explicit smooth order-zero flow. -/
theorem smoothClass_phase {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) :
    smoothClass (phase_smooth hu t) =
      Complex.exp (-Complex.I * (t : ℂ)) • smoothClass hu := by
  unfold smoothClass
  rw [← map_smul]
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [QuantumNLS.WeakDerivatives.liftC_coe]
    change phaseFlow t u y = Complex.exp (-Complex.I * (t : ℂ)) *
      QuantumNLS.WeakDerivatives.liftC hu.smooth.continuous hu.periodic (y : AddCircle L)
    rw [QuantumNLS.WeakDerivatives.liftC_coe]
    rfl

/-- The L² embedding commutes with the explicit smooth translation flow. -/
theorem smoothClass_trans {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (t : ℝ) :
    smoothClass (trans_smooth hu t) = QuantumNLS.BornTranslation.trans (-t) (smoothClass hu) := by
  apply Lp.ext
  have hs := (measurePreserving_add_right (volume : Measure (AddCircle L))
    ((-t : ℝ) : AddCircle L)).quasiMeasurePreserving.ae (smoothClass_ae hu)
  filter_upwards [smoothClass_ae (trans_smooth hu t),
    QuantumNLS.BornTranslation.coeFn_trans (-t) (smoothClass hu), hs] with x h1 h2 h3
  rw [h1, h2, h3]
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    have he : (y : AddCircle L) + ((-t : ℝ) : AddCircle L) = ((y - t : ℝ) : AddCircle L) := by
      simp [sub_eq_add_neg]
    rw [he, QuantumNLS.WeakDerivatives.liftC_coe, QuantumNLS.WeakDerivatives.liftC_coe]
    rfl

#print axioms smoothClass_trans
#print axioms low_covariance
#print axioms active_zero
#print axioms active_one
#print axioms smoothClass_phase
end QuantumNLS.Def033LowR24m
