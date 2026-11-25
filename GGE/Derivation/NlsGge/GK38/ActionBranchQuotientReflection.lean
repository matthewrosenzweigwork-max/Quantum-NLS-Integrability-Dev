import NlsGge.GK38.ActionBranchReflection
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ComplexConjugate
namespace NlsGge.GK38.ActionBranch
noncomputable section

theorem discrim_hasDeriv_conj (u : PhysicalL2) (z : ℂ) :
    HasDerivAt (discrim (realSlice u))
      (conj (deriv (discrim (realSlice u)) z)) (conj z) := by
  have hd : HasDerivAt (discrim (realSlice u))
      (deriv (discrim (realSlice u)) z) z :=
    ((analyticOnNhd_discrim_z (realSlice u)) z (mem_univ _)).differentiableAt.hasDerivAt
  have hc := hd.conj_conj
  apply hc.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro w
  simpa only [Function.comp_apply, Complex.conj_conj] using discrim_conj u (conj w)

theorem discrim_deriv_conj (u : PhysicalL2) (z : ℂ) :
    deriv (discrim (realSlice u)) (conj z) =
      conj (deriv (discrim (realSlice u)) z) :=
  (discrim_hasDeriv_conj u z).deriv

theorem discrim_quotient_conj (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    deriv (discrim (realSlice u)) (conj z) / canonRoot38 (realSlice u) (conj z) =
      -conj (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z) := by
  have hroot := canonRoot_ne_zero38 (realSlice u) (realSlice_mem_gkW u) z
    (rootDomain_realSlice_nonreal38 u z hz).2
  have hrootc := canonRoot_ne_zero38 (realSlice u) (realSlice_mem_gkW u) (conj z)
    (rootDomain_realSlice_nonreal38 u (conj z) (by simpa using hz)).2
  rw [discrim_deriv_conj, canonical_root_conj u z hz, div_neg, map_div₀]

theorem actionIntegrand_conj (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    actionIntegrand38 (realSlice u) (conj z) =
      -conj (actionIntegrand38 (realSlice u) z) := by
  unfold actionIntegrand38
  rw [mul_div_assoc, mul_div_assoc, discrim_quotient_conj u z hz, map_mul]
  ring

theorem discrim_deriv_div_root_lower (u : PhysicalL2) (z : ℂ) (hz : z.im < 0) :
    deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z =
      -Complex.I * conj (deriv (actualQuasimomentumE02_38 u) (conj z)) := by
  have hzc : 0 < (conj z).im := by simpa using hz
  have hr := discrim_quotient_conj u (conj z) (ne_of_gt hzc)
  rw [Complex.conj_conj, discrim_deriv_div_root_upper u (conj z) hzc] at hr
  rw [hr, map_mul, map_neg, Complex.conj_I]
  ring

end
end NlsGge.GK38.ActionBranch
