import NlsGge.GK38.GradEigenRealPeriodic
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem constant_nilpotent_discrim (a b z : ℂ) (hz : z^2=a*b) :
    discrim (constL2 a,constL2 b) z=2 := by
  simp only [discrim_eq,monodromyPair_eq_fundPair,
    constant_nilpotent_fundamental a b z hz]
  simp [zsCoeffPair,Complex.real_smul]
  ring

theorem unit_constant_discrim (a : ℂ) (ha : a*star a=1) (z : ℂ) :
    discrim (realSlice (constL2 a)) z=discrim (realSlice (constL2 1)) z := by
  by_cases hz : z^2=1
  · rw [realSlice_constL2,realSlice_constL2]
    rw [constant_nilpotent_discrim a (star a) z (hz.trans ha.symm)]
    rw [constant_nilpotent_discrim 1 (star 1) z (by simpa using hz)]
  · obtain ⟨κ,hκ⟩ := IsAlgClosed.exists_pow_nat_eq (z^2-1) (n := 2) (by norm_num)
    have hκ0 : κ ≠ 0 := by
      intro he
      rw [he,zero_pow (by decide : 2 ≠ 0)] at hκ
      exact hz (sub_eq_zero.mp hκ.symm)
    have hκa : κ^2=z^2-a*star a := by rw [ha]; exact hκ
    have hκ1 : κ^2=z^2-(1 : ℂ)*star 1 := by simpa using hκ
    unfold discrim
    rw [trace_monodromyPair_realSlice_const a z κ hκ0 hκa,
      trace_monodromyPair_realSlice_const 1 z κ hκ0 hκ1]

theorem unit_constant_gap_endpoints (a : ℂ) (ha : a*star a=1) (n : ℤ) :
    actualGapLowerAllE02_38 (constL2 a) n=actualGapLowerAllE02_38 (constL2 1) n ∧
    actualGapUpperAllE02_38 (constL2 a) n=actualGapUpperAllE02_38 (constL2 1) n := by
  have hper : perChar (realSlice (constL2 a))=perChar (realSlice (constL2 1)) := by
    funext z
    simp only [perChar,perCharOf,unit_constant_discrim a ha z]
  have hseq := lamSeq_eq_of_perChar_eq38 hper
  constructor
  · apply Complex.ofReal_injective
    rw [← (lamPlus_real (constL2 a) n).2,← (lamPlus_real (constL2 1) n).2]
    exact congrFun hseq (2*n)
  · apply Complex.ofReal_injective
    rw [← (lamPlus_real (constL2 a) n).1,← (lamPlus_real (constL2 1) n).1]
    exact congrFun hseq (2*n+1)

theorem probe_imaginary_constant_endpoints :
    actualGapLowerAllE02_38 (constL2 Complex.I) 0= -1 ∧
    actualGapUpperAllE02_38 (constL2 Complex.I) 0=1 := by
  have h := unit_constant_gap_endpoints Complex.I (by simp [Complex.I_sq]) 0
  rw [realType_probe_nonfree_constant38.2.2.1,
    realType_probe_nonfree_constant38.2.2.2.1] at h
  exact h

theorem probe_phased_periodic_state (upper : Bool) (t : Time) :
    state (realSlice (constL2 Complex.I))
      (endpoint (constL2 Complex.I) 0 upper : ℂ) (phasedSeed upper) t=phasedSeed upper := by
  have he : endpoint (constL2 Complex.I) 0 upper=(if upper then (1 : ℝ) else -1) := by
    cases upper
    · exact probe_imaginary_constant_endpoints.1
    · exact probe_imaginary_constant_endpoints.2
  rw [he,realSlice_constL2]
  cases upper <;>
    apply constant_nilpotent_state Complex.I (star Complex.I) _ (by simp [Complex.I_sq]) <;>
    ext i <;> fin_cases i <;>
    simp [phasedSeed,zsCoeffPair,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem probe_phased_periodic_square (upper : Bool) (t : Time) :
    square (state (realSlice (constL2 Complex.I))
      (endpoint (constL2 Complex.I) 0 upper : ℂ) (phasedSeed upper)) t =
      (if upper then ![-2*Complex.I,2*Complex.I] else ![2*Complex.I,-2*Complex.I]) := by
  change starProd38
    (state (realSlice (constL2 Complex.I))
      (endpoint (constL2 Complex.I) 0 upper : ℂ) (phasedSeed upper) t)
    (state (realSlice (constL2 Complex.I))
      (endpoint (constL2 Complex.I) 0 upper : ℂ) (phasedSeed upper) t) = _
  simp only [probe_phased_periodic_state]
  cases upper <;> ext i <;> fin_cases i <;>
    norm_num [phasedSeed,starProd38] <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem constant_kernel_energy_value (w : PairKernelCont38) (v : PairVec38)
    (hv : ∀ t : Time, w t=v) : energy w=‖v 0‖^2+‖v 1‖^2 := by
  have hi := (kernel_integrability w).2.1
  have he (s : ℝ) : pairKernelExt38 w s=v := hv (projIcc 0 1 zero_le_one s)
  simp [energy,he]

theorem constant_square_pairing_value (w : PairKernelCont38) (v : PairVec38)
    (hv : ∀ t : Time, w t=v) (c : ℂ) :
    integralPairCLM38 (square w) t1 (realSlice (constL2 c)) =
      v 1*v 1*c+v 0*v 0*star c := by
  have hi := intervalIntegrable_pairKernel38 (square w) t1 (realSlice (constL2 c))
  change pairIntegral38 (square w) t1 (realSlice (constL2 c)) = _
  rw [realSlice_constL2]
  unfold pairIntegral38
  have he (s : ℝ) : pairKernelExt38 (square w) s=starProd38 v v := by
    change starProd38 (w (projIcc 0 1 zero_le_one s))
      (w (projIcc 0 1 zero_le_one s))=starProd38 v v
    rw [hv]
  have hae : (fun s => pairKernelExt38 (square w) s 0 *
      potRepFst38 (constL2 c,constL2 (star c)) s +
      pairKernelExt38 (square w) s 1 *
      potRepSnd38 (constL2 c,constL2 (star c)) s) =ᵐ[volume]
      fun _ => v 1*v 1*c+v 0*v 0*star c := by
    filter_upwards [coverRep38_const_ae c,coverRep38_const_ae (star c)] with s hs hs'
    simp only [he,potRepFst38,potRepSnd38]
    change v 1*v 1*coverRep38 (constL2 c) s +
      v 0*v 0*coverRep38 (constL2 (star c)) s = _
    rw [hs,hs']
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs _ using hs)]
  simp [t1]

end
end NlsGge.GK38.GradEigen38
