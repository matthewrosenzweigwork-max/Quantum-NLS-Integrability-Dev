import QuantumNLS.IndexedCorrectedContourR30b

/-! The complete four-edge contour, normalization and Hermitian part. The
N=0 extension is given by its chosen kernels; for every positive sector the
operator is the literal LOCAL-009 expression. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
namespace QuantumNLS.IndexedContourAssemblyR30b
open LOCAL009R22LiteralScalar
open PhysicalTensor TensorCarrier KernelDefinition KernelConvergence LocalPlacement
  IndexedCFCBindingR29b IndexedCauchyKernelsR30b IndexedCorrectedContourR30b
  IndexedKernelIntegralR29b IndexedInverseSeriesR28b
  LOCAL009R23OperatorContour LOCAL009R22OperatorSupport PeriodReconstruction Local014RealSymbol
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance] IndexedCauchyKernelsR30b.kernelComplexSpace
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

def a (L : ℝ) (n : ℤ) : ℝ := momentum L n-halfWidth L
def b (L : ℝ) (n : ℤ) : ℝ := momentum L n+halfWidth L

def bottom (κ : ℝ) (n : ℤ) := intList (fun x => fullKernels (L := L) κ (x+(-halfWidth L : ℝ)*I)) (a L n) (b L n)
def top (κ : ℝ) (n : ℤ) := intList (fun x => fullKernels (L := L) κ (x+halfWidth L*I)) (a L n) (b L n)
def right (κ : ℝ) (n : ℤ) := intList (fun y => fullKernels (L := L) κ (b L n+y*I)) (-halfWidth L) (halfWidth L)
def left (κ : ℝ) (n : ℤ) := intList (fun y => fullKernels (L := L) κ (a L n+y*I)) (-halfWidth L) (halfWidth L)
def bottomLimit (κ : ℝ) (n : ℤ) := intLimit (fun x => inverseLimit (L := L) κ (x+(-halfWidth L : ℝ)*I)) (a L n) (b L n)
def topLimit (κ : ℝ) (n : ℤ) := intLimit (fun x => inverseLimit (L := L) κ (x+halfWidth L*I)) (a L n) (b L n)
def rightLimit (κ : ℝ) (n : ℤ) := intLimit (fun y => inverseLimit (L := L) κ (b L n+y*I)) (-halfWidth L) (halfWidth L)
def leftLimit (κ : ℝ) (n : ℤ) := intLimit (fun y => inverseLimit (L := L) κ (a L n+y*I)) (-halfWidth L) (halfWidth L)

def contourKernels (κ : ℝ) (n : ℤ) (N : ℕ) : KernelList (H := L2T L) N :=
  scaleList (2*Real.pi*I)⁻¹
    (((bottom (L := L) κ n N+scaleList (-1) (top (L := L) κ n N))+
      scaleList I (right (L := L) κ n N))+scaleList (-I) (left (L := L) κ n N))
def contourLimit (κ : ℝ) (n : ℤ) (p : ℕ) : BoundedSymmetricKernel (L2T L) p :=
  (2*Real.pi*I)⁻¹ • (((bottomLimit (L := L) κ n p+(-1 : ℂ) • topLimit (L := L) κ n p)+
    I • rightLimit (L := L) κ n p)+(-I) • leftLimit (L := L) κ n p)

theorem edges (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) :
    (ConvergesOnRadius 8 (bottom (L := L) κ n) (bottomLimit (L := L) κ n) ∧
      ∀ N, 0 < N → RadiusBound.represented (bottom (L := L) κ n N) =
        ∫ x in a L n..b L n, integrand L κ 1 (eps N) N (x+(-halfWidth L : ℝ)*I)) ∧
    (ConvergesOnRadius 8 (top (L := L) κ n) (topLimit (L := L) κ n) ∧
      ∀ N, 0 < N → RadiusBound.represented (top (L := L) κ n N) =
        ∫ x in a L n..b L n, integrand L κ 1 (eps N) N (x+halfWidth L*I)) ∧
    (ConvergesOnRadius 8 (right (L := L) κ n) (rightLimit (L := L) κ n) ∧
      ∀ N, 0 < N → RadiusBound.represented (right (L := L) κ n N) =
        ∫ y in -halfWidth L..halfWidth L, integrand L κ 1 (eps N) N (b L n+y*I)) ∧
    (ConvergesOnRadius 8 (left (L := L) κ n) (leftLimit (L := L) κ n) ∧
      ∀ N, 0 < N → RadiusBound.represented (left (L := L) κ n N) =
        ∫ y in -halfWidth L..halfWidth L, integrand L κ 1 (eps N) N (a L n+y*I)) := by
  have hL : 0 < L := Fact.out
  have hh : 0 < halfWidth L := by unfold halfWidth; positivity
  have hab : a L n ≤ b L n := by unfold a b; linarith
  have hv : -halfWidth L ≤ halfWidth L := by linarith
  refine ⟨integrated_full hκ hs n hab _ (by fun_prop) ?_,
    integrated_full hκ hs n hab _ (by fun_prop) ?_,
    integrated_full hκ hs n hv _ (by fun_prop) ?_,
    integrated_full hκ hs n hv _ (by fun_prop) ?_⟩
  · intro x hx; exact horizontal_mem hx (Or.inl rfl)
  · intro x hx; exact horizontal_mem hx (Or.inr rfl)
  · intro y hy; exact vertical_mem hy (Or.inr rfl)
  · intro y hy; exact vertical_mem hy (Or.inl rfl)

theorem contour_converges (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) :
    ConvergesOnRadius 8 (contourKernels (L := L) κ n) (contourLimit (L := L) κ n) := by
  obtain ⟨h1,h2,h3,h4⟩ := edges hκ hs n
  exact converges_smul (converges_add (by norm_num)
    (converges_add (by norm_num) (converges_add (by norm_num) h1.1 (converges_smul h2.1 (-1)))
      (converges_smul h3.1 I)) (converges_smul h4.1 (-I))) _

theorem represented_contour (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) :
    RadiusBound.represented (contourKernels (L := L) κ n N) = approximation L κ 1 (eps N) n N := by
  obtain ⟨h1,h2,h3,h4⟩ := edges hκ hs n
  unfold contourKernels
  rw [represented_smul,represented_add,represented_add,represented_add,
    represented_smul,represented_smul,represented_smul,h1.2 N hN,h2.2 N hN,h3.2 N hN,h4.2 N hN]
  simp only [approximation,rectIntegral,a,b,neg_smul,one_smul,sub_eq_add_neg]

end QuantumNLS.IndexedContourAssemblyR30b
#print axioms QuantumNLS.IndexedContourAssemblyR30b.contour_converges
#print axioms QuantumNLS.IndexedContourAssemblyR30b.represented_contour
