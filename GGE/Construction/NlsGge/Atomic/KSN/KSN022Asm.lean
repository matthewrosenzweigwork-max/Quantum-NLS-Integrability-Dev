import Mathlib
import NlsGge.Atomic.KSN.KSN022Host
import NlsGge.Atomic.G6.G6024Sup2Core

                                                                                  
                                                                                       
                                                                                                                 
                                                                                                         
                                          
                                                                                                        
                                                                                                      
                                                                                                      
                                                                               
                                                                                                        
                                                                                                                  
                                                            
                                                                                                 
                                                                                                             
                                                                                                              
                                                                                                                  
                                                                                                            
                                                                                                         
                                                                       
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSN
open NlsGge.ThirdConsultation.G6024S

namespace NlsGge.ThirdConsultation.KSN022S
noncomputable section

/-! ### The bounded embedding h(N+1) → hs -/

theorem smw_le_two_pow (N : ℕ) (s : ℝ) (hsN : s ≤ (N : ℝ) + 1) (n : ℤ) :
    sobolevModeWeight s n ≤ 2 ^ (N + 1) * scaleWeight ((N : ℝ) + 1) n ^ 2 := by
  have e : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  have hb := bracket_one_le n
  calc sobolevModeWeight s n ≤ sobolevModeWeight ((N : ℝ) + 1) n := sobolevModeWeight_mono hsN n
    _ = (1 + (n : ℝ) ^ 2) ^ (N + 1) := by rw [e, smw_eq]
    _ ≤ (2 * bracket n ^ 2) ^ (N + 1) :=
        pow_le_pow_left₀ (by positivity) (jb_sq_le_two_bracket_sq n) _
    _ = 2 ^ (N + 1) * scaleWeight ((N : ℝ) + 1) n ^ 2 := by
        rw [e, sw_eq, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (N + 1)]

theorem sw_succ_pos (N : ℕ) (n : ℤ) : 0 < scaleWeight ((N : ℝ) + 1) n := by
  have e : (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e, sw_eq]; exact pow_pos (lt_of_lt_of_le one_pos (bracket_one_le _)) _

def fromSeqS (N : ℕ) (y : PairScale ((N : ℝ) + 1)) (n : ℤ) : ℂ :=
  y (true, n) / (scaleWeight ((N : ℝ) + 1) n : ℂ)

theorem fromSeqS_sq_le (N : ℕ) (s : ℝ) (hsN : s ≤ (N : ℝ) + 1) (y : PairScale ((N : ℝ) + 1)) (n : ℤ) :
    sobolevModeWeight s n * ‖fromSeqS N y n‖ ^ 2 ≤ 2 ^ (N + 1) * ‖y (true, n)‖ ^ 2 := by
  unfold fromSeqS
  have hp := sw_succ_pos N n
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le, div_pow]
  have h := smw_le_two_pow N s hsN n
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right h (sq_nonneg ‖y (true, n)‖)
  nlinarith

theorem fromSeqS_mem (N : ℕ) (s : ℝ) (hsN : s ≤ (N : ℝ) + 1) (y : PairScale ((N : ℝ) + 1)) :
    fromSeqS N y ∈ seqSobolev38 s := by
  show Memℓp (weightedCoordinates (sobolevModeWeight s) (fromSeqS N y)) 2
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    (((fromSeq_fibre N y).1).mul_left (2 ^ (N + 1)))
  rw [weightedCoordinates, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sobolevModeWeight_pos _ _).le]
  exact fromSeqS_sq_le N s hsN y n

def fromPairS (N : ℕ) (s : ℝ) (hsN : s ≤ (N : ℝ) + 1) :
    PairScale ((N : ℝ) + 1) →L[ℝ] SobolevCarrier38 s :=
  LinearMap.mkContinuous
    { toFun := fun y => carrierMk38 s (fromSeqS N y) (fromSeqS_mem N s hsN y)
      map_add' := fun x y => by
        apply carrierExt38
        funext n
        rw [carrierCoe38_add]
        simp only [carrierCoe38_mk, fromSeqS, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        apply carrierExt38
        funext n
        rw [RingHom.id_apply, carrierCoe38_smul]
        simp only [carrierCoe38_mk, fromSeqS, lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
        ring }
    (Real.sqrt (2 ^ (N + 1))) (fun y => by
      have h0 := carrier_hasSum_norm_sq38 s (carrierMk38 s (fromSeqS N y) (fromSeqS_mem N s hsN y))
      simp only [carrierCoe38_mk] at h0
      have h2 : ‖carrierMk38 s (fromSeqS N y) (fromSeqS_mem N s hsN y)‖ ^ 2 ≤
          (Real.sqrt (2 ^ (N + 1)) * ‖y‖) ^ 2 := by
        rw [← h0.tsum_eq, mul_pow, Real.sq_sqrt (by positivity)]
        obtain ⟨hs, hle⟩ := fromSeq_fibre N y
        refine (h0.summable.tsum_le_tsum (fun n => fromSeqS_sq_le N s hsN y n) (hs.mul_left _)).trans ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hle (by positivity)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2)

theorem fromPairS_coe (N : ℕ) (s : ℝ) (hsN : s ≤ (N : ℝ) + 1) (y : PairScale ((N : ℝ) + 1)) (n : ℤ) :
    carrierCoe38 s (fromPairS N s hsN y) n = y (true, n) / (scaleWeight ((N : ℝ) + 1) n : ℂ) := rfl

/-! ### The bounded embedding Hs → HN and the physical embedding -/

theorem seqEmbed_eq (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (z : SobolevCarrier38 s) :
    sequenceSobolevEmbedRealExponent s hs z = sequenceSobolevEmbed N (carrierIncl38 hNs z) := by
  apply lp.ext
  show carrierCoe38 0 (carrierIncl38 hs z) =
    carrierCoe38 0 (carrierIncl38 (Nat.cast_nonneg N) (carrierIncl38 hNs z))
  rw [carrierCoe38_incl38, carrierCoe38_incl38, carrierCoe38_incl38]

theorem embed_eq (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (u : PhysicalSobolev38 s) :
    physicalSobolevEmbedRealExponent s hs u =
      physicalSobolevEmbed N ((physicalSobolevFourierEquiv38 (N : ℝ)).symm
        (carrierIncl38 hNs (physicalSobolevFourierEquiv38 s u))) := by
  unfold physicalSobolevEmbedRealExponent physicalSobolevEmbed
  rw [LinearIsometryEquiv.apply_symm_apply, seqEmbed_eq N s hs hNs]

theorem toPair_mem_dom (N : ℕ) (z : SobolevCarrier38 (N : ℝ)) :
    toPair N z ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N) := by
  have h := toPair_mem_complexDomain N ((physicalSobolevFourierEquiv38 (N : ℝ)).symm z)
  rwa [LinearIsometryEquiv.apply_symm_apply] at h

theorem toPair_isReal (N : ℕ) (z : SobolevCarrier38 (N : ℝ)) : IsRealPair (N : ℝ) (toPair N z) := by
  intro n
  rw [raw_toPair, raw_toPair]
  simp only [Bool.false_eq_true, ↓reduceIte, neg_neg, star_neg]

/-- Raw coordinate identity at a real exponent (integer one-smoothing at N, restricted). -/
theorem coord (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s)
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (u : PhysicalSobolev38 s) (n : ℤ) :
    physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u) n =
      carrierCoe38 s (physicalSobolevFourierEquiv38 s u) n +
        smoothingCoefficient N (toPair N (carrierIncl38 hNs (physicalSobolevFourierEquiv38 s u))) true n := by
  have hv : physicalSobolevFourierEquiv38 (N : ℝ) ((physicalSobolevFourierEquiv38 (N : ℝ)).symm
      (carrierIncl38 hNs (physicalSobolevFourierEquiv38 s u))) =
      carrierIncl38 hNs (physicalSobolevFourierEquiv38 s u) := LinearIsometryEquiv.apply_symm_apply _ _
  rw [embed_eq N s hs hNs u, birkhoff_coord N _ hSR n, hv, carrierCoe38_incl38]

/-- The forward map at a real exponent as Fourier plus the restricted one-smoothing correction. -/
def decomp (N : ℕ) (s : ℝ) (hNs : (N : ℝ) ≤ s) (hsN : s ≤ (N : ℝ) + 1) (u : PhysicalSobolev38 s) :
    SobolevCarrier38 s :=
  physicalSobolevFourierEquiv38 s u +
    fromPairS N s hsN (complexSmoothing N (toPair N (carrierIncl38 hNs (physicalSobolevFourierEquiv38 s u))))

theorem birkhoff_fun_eq (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (hsN : s ≤ (N : ℝ) + 1)
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hmem : ∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2)
    (u : PhysicalSobolev38 s) :
    (fun n : ℤ => physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u) n) =
      carrierCoe38 s (decomp N s hNs hsN u) := by
  funext n
  set x := toPair N (carrierIncl38 hNs (physicalSobolevFourierEquiv38 s u)) with hxdef
  have hx : x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N) := toPair_mem_dom N _
  have hcs : complexSmoothing N x = ⟨storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x), hmem x hx⟩ := by
    unfold complexSmoothing sequenceLift
    rw [dif_pos (hmem x hx)]
  unfold decomp
  rw [carrierCoe38_add, fromPairS_coe, coord N s hs hNs hSR u n, ← hxdef, hcs]
  congr 1
  show _ = storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x) (true, n) / _
  unfold storedSequence
  have hw : ((scaleWeight ((N : ℝ) + 1) n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sw_succ_pos N n).ne'
  field_simp

theorem birkhoff_mem (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (hsN : s ≤ (N : ℝ) + 1)
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hmem : ∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2)
    (u : PhysicalSobolev38 s) :
    (fun n : ℤ => physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u) n) ∈ seqSobolev38 s := by
  rw [birkhoff_fun_eq N s hs hNs hsN hSR hmem u]
  exact carrierCoe38_mem s _

theorem birkhoff_eq (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (hsN : s ≤ (N : ℝ) + 1)
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hmem : ∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2)
    (u : PhysicalSobolev38 s) :
    birkhoffSobolevRealExponent s hs u = decomp N s hNs hsN u := by
  have hm := birkhoff_mem N s hs hNs hsN hSR hmem u
  apply carrierExt38
  unfold birkhoffSobolevRealExponent
  simp only []
  rw [dif_pos hm, carrierCoe38_mk]
  exact birkhoff_fun_eq N s hs hNs hsN hSR hmem u

theorem birkhoff_seq (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (hsN : s ≤ (N : ℝ) + 1)
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hmem : ∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2)
    (u : PhysicalSobolev38 s) :
    sequenceSobolevEmbedRealExponent s hs (birkhoffSobolevRealExponent s hs u) =
      physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u) := by
  apply lp.ext
  show carrierCoe38 0 (carrierIncl38 hs (birkhoffSobolevRealExponent s hs u)) = _
  rw [carrierCoe38_incl38, birkhoff_eq N s hs hNs hsN hSR hmem u,
    ← birkhoff_fun_eq N s hs hNs hsN hSR hmem u]

theorem birkhoff_analytic (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (hsN : s ≤ (N : ℝ) + 1)
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hA : AnalyticOnNhd ℂ (complexSmoothing N) (complexDomain (N : ℝ) (Nat.cast_nonneg N)))
    (hmem : ∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2) :
    AnalyticOnNhd ℝ (birkhoffSobolevRealExponent s hs) Set.univ := by
  intro u _
  have heq : birkhoffSobolevRealExponent s hs = decomp N s hNs hsN :=
    funext (birkhoff_eq N s hs hNs hsN hSR hmem)
  rw [heq]
  set F := (physicalSobolevFourierEquiv38 s).toContinuousLinearEquiv.toContinuousLinearMap
  set L := (toPair N).comp ((carrierIncl38 hNs).comp F)
  have hF : AnalyticAt ℝ (fun u => physicalSobolevFourierEquiv38 s u) u := F.analyticAt u
  have hT : AnalyticAt ℝ (fun u => L u) u := L.analyticAt u
  have hC : AnalyticAt ℝ (complexSmoothing N) (L u) :=
    (hA _ (toPair_mem_dom N _)).restrictScalars
  have hP : AnalyticAt ℝ (fun y => fromPairS N s hsN y) (complexSmoothing N (L u)) :=
    (fromPairS N s hsN).analyticAt _
  have hCT : AnalyticAt ℝ (fun u => complexSmoothing N (L u)) u :=
    AnalyticAt.comp (g := complexSmoothing N) (f := fun u => L u) hC hT
  exact hF.add (AnalyticAt.comp (g := fun y => fromPairS N s hsN y)
    (f := fun u => complexSmoothing N (L u)) hP hCT)

theorem birkhoff_bdd (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hNs : (N : ℝ) ≤ s) (hsN : s ≤ (N : ℝ) + 1)
    (hSR : ∀ (v : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice v) = physicalBirkhoff v n)
    (hmem : ∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2)
    (hbd : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
        ‖complexSmoothing N x‖ ≤ C) :
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalSobolev38 s,
      ‖u‖ ≤ B → ‖birkhoffSobolevRealExponent s hs u‖ ≤ C := by
  intro B hB
  obtain ⟨C, hC0, hC⟩ := hbd (‖toPair N‖ * (‖carrierIncl38 hNs‖ * B)) (by positivity)
  refine ⟨B + ‖fromPairS N s hsN‖ * C, by positivity, fun u hu => ?_⟩
  rw [birkhoff_eq N s hs hNs hsN hSR hmem u]
  unfold decomp
  set z := physicalSobolevFourierEquiv38 s u
  have hz : ‖z‖ = ‖u‖ := LinearIsometryEquiv.norm_map _ u
  have hx : ‖toPair N (carrierIncl38 hNs z)‖ ≤ ‖toPair N‖ * (‖carrierIncl38 hNs‖ * B) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [hz]; exact hu
  have hcs := hC _ (toPair_isReal N _) hx
  calc ‖z + fromPairS N s hsN (complexSmoothing N (toPair N (carrierIncl38 hNs z)))‖
      ≤ ‖z‖ + ‖fromPairS N s hsN (complexSmoothing N (toPair N (carrierIncl38 hNs z)))‖ := norm_add_le _ _
    _ ≤ B + ‖fromPairS N s hsN‖ * C := by
        refine add_le_add (hz ▸ hu) ?_
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hcs (norm_nonneg _))

/-- KSN-022 head body from the KSN-019 head body at every N ≥ 1 and the landed real-slice identity. -/
theorem KSN022_of (s : ℝ) (hs : 1 ≤ s)
    (hSR : ∀ (u : PhysicalL2) (n : ℤ), scalarBirkhoff true n (realSlice u) = physicalBirkhoff u n)
    (hK19 : ∀ N : ℕ, 1 ≤ N →
      AnalyticOnNhd ℂ (complexSmoothing N) (complexDomain (N : ℝ) (Nat.cast_nonneg N)) ∧
      (∀ x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
        Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
        ∀ b n, rawCoefficient ((N : ℝ) + 1) (complexSmoothing N x) b n =
          smoothingCoefficient N x b n) ∧
      (∀ x₀ ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
        ∃ (U : Set (PairScale (N : ℝ))) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
          U ⊆ complexDomain (N : ℝ) (Nat.cast_nonneg N) ∧ 0 ≤ C ∧
          ∀ x ∈ U, ‖complexSmoothing N x‖ ≤ C) ∧
      (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
          ‖complexSmoothing N x‖ ≤ C)) :
    AnalyticOnNhd ℝ (birkhoffSobolevRealExponent s (by linarith)) Set.univ ∧
    (∀ u : PhysicalSobolev38 s,
      (fun n : ℤ => physicalBirkhoff (physicalSobolevEmbedRealExponent s (by linarith) u) n)
        ∈ seqSobolev38 s ∧
      sequenceSobolevEmbedRealExponent s (by linarith)
        (birkhoffSobolevRealExponent s (by linarith) u) =
          physicalBirkhoff (physicalSobolevEmbedRealExponent s (by linarith) u)) ∧
    (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalSobolev38 s,
      ‖u‖ ≤ B → ‖birkhoffSobolevRealExponent s (by linarith) u‖ ≤ C) := by
  have hs0 : 0 ≤ s := by linarith
  have hNs : ((⌊s⌋₊ : ℕ) : ℝ) ≤ s := Nat.floor_le hs0
  have hsN : s ≤ ((⌊s⌋₊ : ℕ) : ℝ) + 1 := (Nat.lt_floor_add_one s).le
  have hN : 1 ≤ ⌊s⌋₊ := Nat.le_floor (by exact_mod_cast hs)
  obtain ⟨hA, hM, -, hbd⟩ := hK19 ⌊s⌋₊ hN
  have hmem := fun x hx => (hM x hx).1
  exact ⟨birkhoff_analytic _ s hs0 hNs hsN hSR hA hmem,
    fun u => ⟨birkhoff_mem _ s hs0 hNs hsN hSR hmem u, birkhoff_seq _ s hs0 hNs hsN hSR hmem u⟩,
    birkhoff_bdd _ s hs0 hNs hsN hSR hmem hbd⟩

end
end NlsGge.ThirdConsultation.KSN022S
