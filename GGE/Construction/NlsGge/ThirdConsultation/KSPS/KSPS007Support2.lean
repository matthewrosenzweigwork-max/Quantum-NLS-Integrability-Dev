import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support
import NlsGge.ThirdConsultation.KSPS.KSPS003Support1

                                                                                                                     
                                                                                              
                                                                                    
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2
open NlsGge.ThirdConsultation.KSPS003Support

namespace NlsGge.ThirdConsultation.KSPS007Support2

theorem ode_duhamel_scalar (a : ℂ) {d b : ℝ → ℂ}
    (hdc : ContinuousOn d (Set.Icc (0 : ℝ) 1)) (hb : IntervalIntegrable b volume 0 1)
    (hd : ∀ x ∈ Set.Icc (0 : ℝ) 1, d x = ∫ t in (0 : ℝ)..x, (a * d t + b t)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      d x = ∫ t in (0 : ℝ)..x, Complex.exp (a * ((x : ℂ) - (t : ℂ))) * b t := by
  have hdi : IntervalIntegrable d volume 0 1 := hdc.intervalIntegrable_of_Icc zero_le_one
  have hh : IntervalIntegrable (fun t => a * d t + b t) volume 0 1 := (hdi.const_mul a).add hb
  have hd0 : d 0 = 0 := by
    have := hd 0 ⟨le_rfl, zero_le_one⟩
    simpa using this
  have hprim : PrimOn d (fun t => a * d t + b t) :=
    ⟨hh, fun t ht => by rw [hd t ht, hd0]; simp⟩
  intro x hx
  have hibp := ibp_exp hprim (-a) hx
  have hsub := uIcc_sub hx
  have hexc : Continuous fun s : ℝ => Complex.exp (-a * (s : ℂ)) := by fun_prop
  have i1 : IntervalIntegrable (fun s : ℝ => Complex.exp (-a * (s : ℂ)) * d s) volume 0 x :=
    (hexc.continuousOn.mul (hdc.mono hsub)).intervalIntegrable
  have i2 : IntervalIntegrable (fun s : ℝ => Complex.exp (-a * (s : ℂ)) * b s) volume 0 x :=
    (ii_mono hb hx).continuousOn_mul hexc.continuousOn
  have hsplit : ∫ s in (0 : ℝ)..x, Complex.exp (-a * (s : ℂ)) * (a * d s + b s) =
      a * (∫ s in (0 : ℝ)..x, Complex.exp (-a * (s : ℂ)) * d s) +
        ∫ s in (0 : ℝ)..x, Complex.exp (-a * (s : ℂ)) * b s := by
    have h := intervalIntegral.integral_add (i1.const_mul a) i2
    rw [intervalIntegral.integral_const_mul] at h
    rw [← h]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  rw [hsplit, hd0] at hibp
  have hB : ∫ s in (0 : ℝ)..x, Complex.exp (-a * (s : ℂ)) * b s = Complex.exp (-a * (x : ℂ)) * d x := by
    linear_combination hibp
  have hfin : ∫ t in (0 : ℝ)..x, Complex.exp (a * ((x : ℂ) - (t : ℂ))) * b t =
      Complex.exp (a * (x : ℂ)) * ∫ s in (0 : ℝ)..x, Complex.exp (-a * (s : ℂ)) * b s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show Complex.exp (a * ((x : ℂ) - (t : ℂ))) * b t = Complex.exp (a * (x : ℂ)) * (Complex.exp (-a * (t : ℂ)) * b t)
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hfin, hB, ← mul_assoc, ← Complex.exp_add]
  have : a * (x : ℂ) + -a * (x : ℂ) = 0 := by ring
  rw [this]
  simp

end NlsGge.ThirdConsultation.KSPS007Support2
