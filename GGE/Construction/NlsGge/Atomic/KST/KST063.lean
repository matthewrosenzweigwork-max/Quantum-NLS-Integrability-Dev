import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST058
import NlsGge.Atomic.KST.KST059
import NlsGge.Atomic.KST.KST062
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST061Host

                                                                                                        
                                                                                                    
                                                                                                          
                                                                                                    
                                                                                                          
                                                                                                     
                                                                                                       
                                                                                                    
                                                                                               
                                                                        
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST001 NlsGge.Atomic.KST002 NlsGge.Pilot NlsGge.GK38
open NlsGge.Atomic.DM046

namespace NlsGge.ThirdConsultation.KST

namespace KST063W

/-- The square root of the pointwise two-channel Fourier energy, as a complex sequence. -/
def fieldGap (φ : PeriodicPair) (n : ℤ) : ℂ :=
  ((Real.sqrt (‖physicalFourier φ.1 n‖ ^ 2 + ‖physicalFourier φ.2 n‖ ^ 2) : ℝ) : ℂ)

theorem fieldGap_norm_sq (φ : PeriodicPair) (n : ℤ) :
    ‖fieldGap φ n‖ ^ 2 = ‖physicalFourier φ.1 n‖ ^ 2 + ‖physicalFourier φ.2 n‖ ^ 2 := by
  unfold fieldGap
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]

/-- The doubled-cover energy of a pair is the weighted gap energy of its field-energy sequence. -/
theorem normSq₂_eq_gapEnergy (W : ℤ → ℝ) (hW : EvenWeight W) (φ : PeriodicPair) :
    weightedNormSq₂ W φ = NlsGge.Atomic.KST059.weightedGapEnergy W (fieldGap φ) := by
  rw [periodOne_weightedPair_norm W φ hW]
  unfold weightedEvenFourierNormSq NlsGge.Atomic.KST059.weightedGapEnergy
  refine tsum_congr fun m => ?_
  simp only [weightedPairMode]
  rw [fieldGap_norm_sq, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]

theorem productWeight_even {w v : ℤ → ℝ} (hw : EvenWeight w) (hv : EvenWeight v) :
    EvenWeight (productWeight w v) :=
  ⟨productOneLe hw.one_le hv.one_le, fun k => by
    simp only [productWeight, hw.even, hv.even]⟩

/-- Step (1): an auxiliary slow unbounded weight with `φ ∈ H^{wω}`. -/
theorem exists_aux_weight (ω : ℤ → ℝ) (hE : EvenWeight ω) (φ : PeriodicPair)
    (hφ : weightedNormSq₂ ω φ < ⊤) :
    ∃ w : ℤ → ℝ, NlsGge.Atomic.KST059.SlowUnboundedWeight w ∧
      weightedNormSq₂ (productWeight w ω) φ < ⊤ := by
  have hγ : NlsGge.Atomic.KST059.weightedGapEnergy ω (fieldGap φ) < ⊤ := by
    rw [← normSq₂_eq_gapEnergy ω hE φ]
    exact hφ
  obtain ⟨c, hslow, -, hgap⟩ :=
    NlsGge.Atomic.KST059.exists_common_auxiliary_weight φ ω hE (fieldGap φ) hγ
  refine ⟨NlsGge.Atomic.KST.dyadicAuxiliaryWeight c, hslow, ?_⟩
  have hwE : EvenWeight (NlsGge.Atomic.KST.dyadicAuxiliaryWeight c) :=
    ⟨hslow.1.one_le, hslow.1.even⟩
  rw [normSq₂_eq_gapEnergy _ (productWeight_even hwE hE) φ]
  exact hgap

/-- A pointwise comparison of weights gives a comparison of doubled-cover energies. -/
theorem normSq₂_mono (v u : ℤ → ℝ) (h : ∀ k, v k ^ 2 ≤ u k ^ 2) (ψ : PeriodicPair) :
    weightedNormSq₂ v ψ ≤ weightedNormSq₂ u ψ := by
  unfold weightedNormSq₂
  refine ENNReal.tsum_le_tsum fun k => ?_
  unfold weightedPairMode
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (h k)) le_rfl

section Realisation

variable (W : ℤ → ℝ) (hE : EvenWeight W) [Fact (∀ m : ℤ, 0 < periodOneWeight W m ^ 2)]

theorem periodicPair_wp (u : Weighted W) :
    periodicPair (weightedPotential W hE.one_le u) = periodOnePhysicalPair W hE u := rfl

theorem normSq₂_wp (u : Weighted W) :
    weightedNormSq₂ W (periodicPair (weightedPotential W hE.one_le u)) =
      ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [periodicPair_wp]
  exact periodOnePhysicalPair_full_doubled_energy_eq_norm W hE u

theorem periodicPair_wp_sub (u z : Weighted W) :
    periodicPair (weightedPotential W hE.one_le z) - periodicPair (weightedPotential W hE.one_le u) =
      periodicPair (weightedPotential W hE.one_le (z - u)) := by
  have h := (NlsGge.ThirdConsultation.KST.KST033S.wpCLM W hE.one_le).map_sub z u
  simp only [NlsGge.ThirdConsultation.KST.KST033S.wpCLM_apply] at h
  rw [h]
  apply Prod.ext
  · simp [periodicPair]
  · simp [periodicPair]

end Realisation

end KST063W

theorem kst063 (ω : ℤ → ℝ) (hω : AdmissibleWeight ω)
    (hsub : SubmultiplicativeWeight ω) (φ : PotPair)
    (hφ : weightedNormSq₂ ω φ < ⊤) (ε : ℝ) (hreal : RealForm ε φ)
    (e : ℝ) (he : 0 < e) :
  ∃ ψ : PotPair, RealForm ε ψ ∧ pairFiniteGap ψ ∧
    weightedNormSq₂ ω ψ < ⊤ ∧
    weightedNormSq₂ ω (ψ-φ) < ENNReal.ofReal (e^2) := by
  have hE : EvenWeight ω := ⟨hω.1, hω.2.1⟩
  have hv : SecondaryWeight ω := ⟨hω, hsub⟩
  obtain ⟨w, hwu, hφw⟩ := KST063W.exists_aux_weight ω hE φ hφ
  have hWE : EvenWeight (productWeight w ω) :=
    KST063W.productWeight_even ⟨hwu.1.one_le, hwu.1.even⟩ hE
  letI hF : Fact (∀ m : ℤ, 0 < periodOneWeight (productWeight w ω) m ^ 2) :=
    weightFact (productWeight w ω) hWE.one_le
  obtain ⟨x, hx⟩ := periodOnePhysicalPair_exists_of_finite_energy (productWeight w ω) hWE φ hφw
  have hxφ : periodicPair (weightedPotential (productWeight w ω) hWE.one_le x) = φ := hx
  set M : ℝ := 1 + ‖x true‖ + ‖x false‖ with hMdef
  have hM : 1 ≤ M := by
    have h1 := norm_nonneg (x true)
    have h2 := norm_nonneg (x false)
    linarith
  have hxU : x ∈ componentOpenBall (productWeight w ω) M := by
    intro ch
    have h1 := norm_nonneg (x true)
    have h2 := norm_nonneg (x false)
    cases ch
    · simp only [hMdef]; linarith
    · simp only [hMdef]; linarith
  have hrealx : RealForm ε (periodicPair (weightedPotential (productWeight w ω) hWE.one_le x)) := by
    rw [hxφ]
    exact hreal
  obtain ⟨⟨J₀, -, hJ₀⟩, hT⟩ := kst062 w 2 M hM hwu.1 hwu.2.2.1 ω hv ε hreal.1 x hxU hrealx
  have hclose : ∃ z : Weighted (productWeight w ω), z ∈ Metric.ball x e ∧
      RealForm ε (periodicPair (weightedPotential (productWeight w ω) hWE.one_le z)) ∧
      pairFiniteGap (periodicPair (weightedPotential (productWeight w ω) hWE.one_le z)) := by
    obtain ⟨J, hJa, hJb⟩ :=
      ((hT.eventually (Metric.ball_mem_nhds x he)).and (eventually_ge_atTop J₀)).exists
    obtain ⟨-, -, -, -, hrf, hgap⟩ := hJ₀ J hJb
    exact ⟨_, hJa, hrf, hgap⟩
  obtain ⟨z, hzball, hzreal, hzgap⟩ := hclose
  refine ⟨periodicPair (weightedPotential (productWeight w ω) hWE.one_le z), hzreal, hzgap, ?_, ?_⟩
  · have hmono : ∀ k, ω k ^ 2 ≤ productWeight w ω k ^ 2 := fun k => by
      have h1 := hwu.1.one_le k
      have h2 := hE.one_le k
      simp only [productWeight]
      have h3 : ω k ≤ w k * ω k := le_mul_of_one_le_left (by linarith) h1
      exact pow_le_pow_left₀ (by linarith) h3 2
    refine lt_of_le_of_lt (KST063W.normSq₂_mono ω _ hmono _) ?_
    rw [KST063W.normSq₂_wp (productWeight w ω) hWE]
    exact ENNReal.ofReal_lt_top
  · have hmono : ∀ k, ω k ^ 2 ≤ productWeight w ω k ^ 2 := fun k => by
      have h1 := hwu.1.one_le k
      have h2 := hE.one_le k
      simp only [productWeight]
      have h3 : ω k ≤ w k * ω k := le_mul_of_one_le_left (by linarith) h1
      exact pow_le_pow_left₀ (by linarith) h3 2
    rw [← hxφ, KST063W.periodicPair_wp_sub (productWeight w ω) hWE x z]
    refine lt_of_le_of_lt (KST063W.normSq₂_mono ω _ hmono _) ?_
    rw [KST063W.normSq₂_wp (productWeight w ω) hWE, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hd : ‖z - x‖ < e := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.1 hzball
    exact pow_lt_pow_left₀ hd (norm_nonneg _) (by norm_num)

end NlsGge.ThirdConsultation.KST
end
