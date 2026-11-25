import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.ThirdConsultation.G6.Energy031A

                                                                                          
                                                                                                                       
                                                                                                             
                                                                                              
                                                                                                                   
                                                                                                                    
                                                                                                 
                                                                                      
                                                                                                           
                                                                                   
set_option autoImplicit false
open NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.PDE
namespace PDE063Aux
noncomputable section

theorem exp_rot_norm (θ : ℝ) : ‖Complex.exp (-Complex.I * (θ : ℂ))‖ = 1 := by
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem exp_rot_eq (θ : ℝ) :
    Complex.exp (-Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * (-Complex.I) := by
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem rot_support (ω : ℤ → ℝ) (z : ℤ → ℂ) (t : ℝ) :
    {n : ℤ | Complex.exp (-Complex.I * ((t * ω n : ℝ) : ℂ)) * z n ≠ 0} = {n : ℤ | z n ≠ 0} := by
  ext n
  simp [Complex.exp_ne_zero]

theorem rot_finite (ω : ℤ → ℝ) (z : ℤ → ℂ) (hz : {n : ℤ | z n ≠ 0}.Finite) (t : ℝ) :
    {n : ℤ | Complex.exp (-Complex.I * ((t * ω n : ℝ) : ℂ)) * z n ≠ 0}.Finite := by
  rw [rot_support]
  exact hz

theorem rotDeriv_finite (ω : ℤ → ℝ) (z : ℤ → ℂ) (hz : {n : ℤ | z n ≠ 0}.Finite) (t : ℝ) :
    {n : ℤ | -Complex.I * (ω n : ℂ) * (Complex.exp (-Complex.I * ((t * ω n : ℝ) : ℂ)) * z n) ≠ 0}.Finite := by
  refine hz.subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  apply hn
  rw [h0, mul_zero, mul_zero]

/-- The coordinate evaluation as an additive map on the carrier. -/
def coordHom (r : ℝ) (k : ℤ) : SobolevCarrier38 r →+ ℂ :=
  AddMonoidHom.mk' (fun x => carrierCoe38 r x k) (fun x y => carrierCoe38_add r x y k)

/-- Carrier vector of a single mode. -/
theorem single_mem (r : ℝ) (n : ℤ) (a : ℂ) : (Pi.single n a : ℤ → ℂ) ∈ seqSobolev38 r :=
  finiteSupport_mem_seqSobolev38 r _ ((Set.finite_singleton n).subset (fun k hk => by
    rw [Set.mem_singleton_iff]
    by_contra h
    exact hk (by simp [Pi.single_apply, h])))

theorem coe_combo (r : ℝ) (S : Finset ℤ) (z : ℤ → ℂ) (a b : ℤ → ℝ) (k : ℤ) :
    carrierCoe38 r (∑ n ∈ S, (a n • carrierMk38 r (Pi.single n (z n)) (single_mem r n (z n)) +
        b n • carrierMk38 r (Pi.single n (-Complex.I * z n)) (single_mem r n (-Complex.I * z n)))) k =
      if k ∈ S then (a k : ℂ) * z k + (b k : ℂ) * (-Complex.I * z k) else 0 := by
  have h := map_sum (coordHom r k) (fun n => a n • carrierMk38 r (Pi.single n (z n)) (single_mem r n (z n)) +
        b n • carrierMk38 r (Pi.single n (-Complex.I * z n)) (single_mem r n (-Complex.I * z n))) S
  change carrierCoe38 r _ k = _ at h
  rw [h]
  simp only [coordHom, AddMonoidHom.mk'_apply, carrierCoe38_add, carrierCoe38_smul, carrierCoe38_mk]
  split_ifs with hk
  · rw [Finset.sum_eq_single k]
    · simp
    · intro n _ hnk
      simp [Pi.single_eq_of_ne' hnk]
    · intro h'; exact absurd hk h'
  · refine Finset.sum_eq_zero (fun n hn => ?_)
    have hnk : n ≠ k := fun e => hk (e ▸ hn)
    simp [Pi.single_eq_of_ne' hnk]

theorem rotation_core (r : ℝ) (ω : ℤ → ℝ) (z : ℤ → ℂ) (hz : {n : ℤ | z n ≠ 0}.Finite)
    (hmem : ∀ t : ℝ, (fun n : ℤ => Complex.exp (-Complex.I * ((t * ω n : ℝ) : ℂ)) * z n) ∈ seqSobolev38 r)
    (hdmem : ∀ t : ℝ, (fun n : ℤ => -Complex.I * (ω n : ℂ) *
      (Complex.exp (-Complex.I * ((t * ω n : ℝ) : ℂ)) * z n)) ∈ seqSobolev38 r) :
    ContDiff ℝ 1 (fun t : ℝ => carrierMk38 r _ (hmem t)) ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => carrierMk38 r _ (hmem s)) (carrierMk38 r _ (hdmem t)) t) ∧
    (∀ (t : ℝ) (n : ℤ), ‖carrierCoe38 r (carrierMk38 r _ (hmem t)) n‖^2 = ‖z n‖^2) ∧
    ∀ t : ℝ, {n : ℤ | carrierCoe38 r (carrierMk38 r _ (hmem t)) n ≠ 0} = {n : ℤ | z n ≠ 0} := by
  set S := hz.toFinset with hS
  set A : ℤ → SobolevCarrier38 r := fun n => carrierMk38 r (Pi.single n (z n)) (single_mem r n (z n)) with hA
  set B : ℤ → SobolevCarrier38 r := fun n =>
    carrierMk38 r (Pi.single n (-Complex.I * z n)) (single_mem r n (-Complex.I * z n)) with hB
  have hzero : ∀ k, k ∉ S → z k = 0 := by
    intro k hk
    by_contra h
    exact hk (hz.mem_toFinset.2 h)
  have hcurve : (fun t : ℝ => carrierMk38 r _ (hmem t)) =
      fun t : ℝ => ∑ n ∈ S, (Real.cos (t * ω n) • A n + Real.sin (t * ω n) • B n) := by
    funext t
    apply carrierCoe38_injective
    funext k
    rw [carrierCoe38_mk, coe_combo r S z (fun n => Real.cos (t * ω n)) (fun n => Real.sin (t * ω n)) k]
    split_ifs with hk
    · rw [exp_rot_eq]; ring
    · rw [hzero k hk, mul_zero]
  have hderiv : ∀ t : ℝ, carrierMk38 r _ (hdmem t) =
      ∑ n ∈ S, ((-Real.sin (t * ω n) * ω n) • A n + (Real.cos (t * ω n) * ω n) • B n) := by
    intro t
    apply carrierCoe38_injective
    funext k
    rw [carrierCoe38_mk, coe_combo r S z (fun n => -Real.sin (t * ω n) * ω n)
      (fun n => Real.cos (t * ω n) * ω n) k]
    split_ifs with hk
    · rw [exp_rot_eq]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    · rw [hzero k hk, mul_zero, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcurve]
    refine ContDiff.sum (fun n _ => ?_)
    have hc : ContDiff ℝ 1 (fun s : ℝ => Real.cos (s * ω n)) := by fun_prop
    have hs : ContDiff ℝ 1 (fun s : ℝ => Real.sin (s * ω n)) := by fun_prop
    exact (hc.smul contDiff_const).add (hs.smul contDiff_const)
  · intro t
    rw [hcurve, hderiv t]
    refine HasDerivAt.fun_sum (fun n _ => ?_)
    have h1 : HasDerivAt (fun s : ℝ => s * ω n) (1 * ω n) t := (hasDerivAt_id' t).mul_const (ω n)
    have hc := (h1.cos).smul_const (A n)
    have hs := (h1.sin).smul_const (B n)
    convert hc.add hs using 2 <;> ring
  · intro t n
    rw [carrierCoe38_mk, norm_mul, exp_rot_norm, one_mul]
  · intro t
    simp only [carrierCoe38_mk]
    exact rot_support ω z t

end
end PDE063Aux
end NlsGge.ThirdConsultation.PDE
