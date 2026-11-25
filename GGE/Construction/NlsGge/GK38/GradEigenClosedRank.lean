import NlsGge.GK38.GradEigenClosedKernelSymmetry
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem closed_rows_independent (u : PhysicalL2) (n : ℤ) (hc : u ∈ Z n) (r s : ℝ)
    (hz : r • realKernelCLM (closedKernel1 u n)+s • realKernelCLM (closedKernel2 u n)=0) :
    r=0 ∧ s=0 := by
  let k : PairKernelCont38 := (r : ℂ) • closedKernel1 u n+(s : ℂ) • closedKernel2 u n
  have hsym : realSymmetric k := realSymmetric_add _ _
    (realSymmetric_smul _ _ (by simp) (realSymmetric_closedKernel1 u n))
    (realSymmetric_smul _ _ (by simp) (realSymmetric_closedKernel2 u n))
  have hfun : realKernelCLM k=0 := by
    dsimp only [k]
    rw [realKernelCLM_add,realKernelCLM_real_smul,realKernelCLM_real_smul]
    exact hz
  have hk : k=0 := real_kernel_injective_target k hsym hfun
  have h0 := congrArg (fun w : PairKernelCont38 => w t0 0) hk
  have h1 := congrArg (fun w : PairKernelCont38 => w t0 1) hk
  change (r : ℂ)*closedKernel1 u n t0 0+(s : ℂ)*closedKernel2 u n t0 0=0 at h0
  change (r : ℂ)*closedKernel1 u n t0 1+(s : ℂ)*closedKernel2 u n t0 1=0 at h1
  have hinit := closed_kernel_initial_values_target u n
  rw [hinit.2.1,hinit.2.2 hc] at h0 h1
  simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,mul_one] at h0 h1
  have hp : (s : ℂ)*parity n*Complex.I=0 := by linear_combination h0/2-h1/2
  have hpar : parity n ≠ 0 := by exact zpow_ne_zero _ (by norm_num)
  have hsC : (s : ℂ)=0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right Complex.I_ne_zero)).resolve_right hpar
  have hs : s=0 := Complex.ofReal_injective hsC
  rw [hs,Complex.ofReal_zero,zero_mul,add_zero] at h0
  have hα : ((((energy (dirState u n))⁻¹+(energy (neuState u n))⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hinit.1
  have hrC : (r : ℂ)=0 := (mul_eq_zero.mp h0).resolve_right hα
  exact ⟨Complex.ofReal_injective hrC,hs⟩

theorem independent_rows_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E →L[ℝ] ℝ)
    (hind : ∀ r s : ℝ, r • f+s • g=0 → r=0 ∧ s=0) :
    Function.Surjective (f.prod g) := by
  let L : E →ₗ[ℝ] Normal := (f.prod g).toLinearMap
  by_contra hn
  have hproper : L.range<⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    exact hn (LinearMap.range_eq_top.mp he))
  obtain ⟨ell,hell,hker⟩ := L.range.exists_le_ker_of_lt_top hproper
  have hsplit (p : Normal) : ell p=p.1*ell (1,0)+p.2*ell (0,1) := by
    calc
      ell p=ell (p.1 • ((1,0) : Normal)+p.2 • ((0,1) : Normal)) := by
        congr 1
        ext <;> simp
      _ = _ := by rw [map_add,map_smul,map_smul]; rfl
  have hrow : ell (1,0) • f+ell (0,1) • g=0 := by
    ext x
    have hz : ell (L x)=0 := hker ⟨x,rfl⟩
    rw [hsplit] at hz
    change f x*ell (1,0)+g x*ell (0,1)=0 at hz
    change ell (1,0)*f x+ell (0,1)*g x=0
    linear_combination hz
  obtain ⟨hfst,hsnd⟩ := hind _ _ hrow
  apply hell
  apply LinearMap.ext
  intro p
  change ell p=0
  rw [hsplit,hfst,hsnd]
  simp

def ClosedSubmersionTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ), u ∈ Z n → Function.Surjective (closedDerivative n u)

theorem closed_submersion_target : ClosedSubmersionTarget := by
  intro u n hc
  have hrows := independent_rows_surjective (realKernelCLM (closedKernel1 u n))
    (realKernelCLM (closedKernel2 u n)) (closed_rows_independent u n hc)
  change Function.Surjective (fderiv ℝ (closedEquations n) u)
  rw [(closed_derivative_kernels_target u n).fderiv]
  exact hrows

end
end NlsGge.GK38.GradEigen38
