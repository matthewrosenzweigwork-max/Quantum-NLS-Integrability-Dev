import NlsGge.ThirdConsultation.G1.G1098Host
import NlsGge.ThirdConsultation.G1.G1098PairCLM
import NlsGge.ThirdConsultation.G1.G1098MixBL
import NlsGge.ThirdConsultation.G1.G1098StateAnalytic
import NlsGge.ThirdConsultation.G1.G1098M1
import NlsGge.ThirdConsultation.G1.G1098M2H
import NlsGge.ThirdConsultation.G1.G1098Reindex
import NlsGge.ThirdConsultation.G1.G1098RealBasis
import NlsGge.ThirdConsultation.G1.G1098Synth
import NlsGge.ThirdConsultation.G1.G1098Assembly
import NlsGge.GK38.DirichletRealReality

                                                                                     
                                                                                       
                                                                                                     
                                                                                                     
                                                                                                
                                                                                            
                                                                                                  
                                                             
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.G1098Basis NlsGge.Atomic.G1098Synth NlsGge.Atomic.G1098Assembly
open NlsGge.Atomic.G1098Reindex

namespace NlsGge.Atomic.G1098
noncomputable section

/-! ### Realness of the real slices -/

theorem mixedKernel_eq_complex (u v : PhysicalL2) (n : ℤ) (minus : Bool) :
    mixedKernel u v n minus = complexMixedKernel (realSlice u) (realSlice v) n minus := by
  have ht : ∀ w : PhysicalL2, terminalState w n = complexTerminalState (realSlice w) n :=
    fun w => by unfold terminalState complexTerminalState; rw [muSeq_eq_gkMu38]
  have hd : ∀ w : PhysicalL2, dirState w n = complexDirState (realSlice w) n :=
    fun w => by unfold dirState complexDirState; rw [muSeq_eq_gkMu38]
  unfold mixedKernel complexMixedKernel
  rw [hd u, hd v, ht u, ht v]

theorem mixedColumn_eq_complex (u v : PhysicalL2) (n : ℤ) (minus : Bool) :
    mixedColumn u v n minus = complexMixedColumn (realSlice u) (realSlice v) n minus := by
  unfold mixedColumn complexMixedColumn
  rw [mixedKernel_eq_complex]

/-! ### Elementary norm facts -/

theorem sq_norm_sub_le_two (a b : PhysicalL2) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem norm_smul_sq_le_of_le_one {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : PhysicalL2) :
    ‖c • x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hc0 hc1)

theorem lp2_norm_sq {α : Type*} (f : lp (fun _ : α => ℂ) (2 : ENNReal)) :
    ‖f‖ ^ 2 = ∑' a, ‖f a‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) f
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- Parseval for a countable family of physical L2 vectors: the Fourier coefficients of the family
have total square sum equal to the total square sum of the family. -/
theorem par_fam {ι : Type*} (x : ι → PhysicalL2) (hx : Summable fun j => ‖x j‖ ^ 2) :
    Summable (fun a : ι × ℤ => ‖reflectedFourierL2 (x a.1) a.2‖ ^ 2) ∧
      ∑' a : ι × ℤ, ‖reflectedFourierL2 (x a.1) a.2‖ ^ 2 = ∑' j, ‖x j‖ ^ 2 := by
  have hfib : ∀ j : ι, Summable (fun k : ℤ => ‖reflectedFourierL2 (x j) k‖ ^ 2) := by
    intro j
    have h := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).mp
      (lp.memℓp (reflectedFourierL2 (x j)))
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hsum : ∀ j : ι, ∑' k : ℤ, ‖reflectedFourierL2 (x j) k‖ ^ 2 = ‖x j‖ ^ 2 := by
    intro j
    have h := lp2_norm_sq (reflectedFourierL2 (x j))
    rw [LinearIsometryEquiv.norm_map] at h
    exact h.symm
  have hnn : (0 : ι × ℤ → ℝ) ≤ fun a => ‖reflectedFourierL2 (x a.1) a.2‖ ^ 2 :=
    fun a => sq_nonneg _
  have hS : Summable (fun a : ι × ℤ => ‖reflectedFourierL2 (x a.1) a.2‖ ^ 2) :=
    (summable_prod_of_nonneg hnn).mpr ⟨hfib, by simpa only [hsum] using hx⟩
  refine ⟨hS, ?_⟩
  rw [Summable.tsum_prod' hS hfib]
  exact tsum_congr hsum

/-! ### Fourier coefficient family of the vacuum-subtracted complex columns -/

/-- Fourier coefficient functional at `k` on physical L2. -/
def fourierCoefCLM (k : ℤ) : PhysicalL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) (2 : ENNReal) k).comp
    reflectedFourierL2.toLinearIsometry.toContinuousLinearMap

theorem fourierCoefCLM_apply (k : ℤ) (x : PhysicalL2) :
    fourierCoefCLM k x = reflectedFourierL2 x k :=
  rfl

/-- Vacuum-subtracted complex mixed column at a complex potential pair. -/
def famVec (p : PotPair × PotPair) (j : ℤ × Bool) : PhysicalL2 :=
  complexMixedColumn p.1 p.2 j.1 j.2 - mixedReference j.1 j.2

def famCoef (p : PotPair × PotPair) (a : (ℤ × Bool) × ℤ) : ℂ :=
  reflectedFourierL2 (famVec p a.1) a.2

theorem famCoef_memℓp (p : PotPair × PotPair)
    (hp : Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2) :
    Memℓp (famCoef p) (2 : ENNReal) := by
  refine memℓp_gen ?_
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, famCoef] using (par_fam (famVec p) hp).1

/-- The Fourier coefficient family as an `ℓ²` vector (totalized: zero off the summability set). -/
noncomputable def famPhi (p : PotPair × PotPair) : lp (fun _ : (ℤ × Bool) × ℤ => ℂ) (2 : ENNReal) :=
  if h : Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2 then ⟨famCoef p, famCoef_memℓp p h⟩ else 0

theorem famPhi_apply (p : PotPair × PotPair) (h : Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2)
    (a : (ℤ × Bool) × ℤ) : famPhi p a = famCoef p a :=
  congrArg (fun F : lp (fun _ : (ℤ × Bool) × ℤ => ℂ) (2 : ENNReal) => F a)
    (dif_pos h : famPhi p = ⟨famCoef p, famCoef_memℓp p h⟩)

theorem famPhi_tsum (p : PotPair × PotPair) (h : Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2) :
    ∑' a, ‖famPhi p a‖ ^ 2 = ∑' j : ℤ × Bool, ‖famVec p j‖ ^ 2 := by
  have e : ∀ a : (ℤ × Bool) × ℤ, ‖famPhi p a‖ ^ 2 = ‖reflectedFourierL2 (famVec p a.1) a.2‖ ^ 2 :=
    fun a => congrArg (fun z : ℂ => ‖z‖ ^ 2) (famPhi_apply p h a)
  exact (tsum_congr e).trans (par_fam (famVec p) h).2

theorem summable_famVec_real (u v : PhysicalL2) :
    Summable fun j : ℤ × Bool => ‖famVec (realSlice u, realSlice v) j‖ ^ 2 := by
  obtain ⟨U, hU, _, _, _, _, h⟩ :=
    NlsGge.ThirdConsultation.G1098M2H.complexMixedColumn_local_square_sum u v
  exact (h _ (mem_of_mem_nhds hU)).1

theorem summable_famVec_sub {P Q : PotPair × PotPair}
    (hP : Summable fun j : ℤ × Bool => ‖famVec P j‖ ^ 2)
    (hQ : Summable fun j : ℤ × Bool => ‖famVec Q j‖ ^ 2) :
    Summable fun j : ℤ × Bool => ‖famVec P j - famVec Q j‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => sq_norm_sub_le_two _ _)
    ((hP.mul_left 2).add (hQ.mul_left 2))

theorem famPhi_sub_norm_sq {P Q : PotPair × PotPair}
    (hP : Summable fun j : ℤ × Bool => ‖famVec P j‖ ^ 2)
    (hQ : Summable fun j : ℤ × Bool => ‖famVec Q j‖ ^ 2) :
    ‖famPhi P - famPhi Q‖ ^ 2 = ∑' j : ℤ × Bool, ‖famVec P j - famVec Q j‖ ^ 2 := by
  rw [lp2_norm_sq]
  have e : ∀ a : (ℤ × Bool) × ℤ,
      ‖(famPhi P - famPhi Q) a‖ ^ 2 = ‖reflectedFourierL2 (famVec P a.1 - famVec Q a.1) a.2‖ ^ 2 := by
    intro a
    simp only [lp.coeFn_sub, Pi.sub_apply, famPhi_apply P hP a, famPhi_apply Q hQ a, famCoef,
      map_sub]
  exact (tsum_congr e).trans
    (par_fam (fun j => famVec P j - famVec Q j) (summable_famVec_sub hP hQ)).2

/-- Analyticity of the Fourier coefficient family on an open set where the column square sums are
uniformly bounded (M1 coordinates, M2 bound, M3 transfer). -/
theorem famPhi_analyticOn (U : Set (PotPair × PotPair)) (hUo : IsOpen U)
    (hUs : U ⊆ gkW ×ˢ gkW) (hUsum : ∀ p ∈ U, Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2)
    (C : ℝ) (hC0 : 0 ≤ C) (hCb : ∀ p ∈ U, ∑' j : ℤ × Bool, ‖famVec p j‖ ^ 2 ≤ C) :
    AnalyticOnNhd ℂ famPhi U := by
  obtain ⟨σ⟩ : Nonempty (((ℤ × Bool) × ℤ) ≃ ℤ) := nonempty_equiv_of_countable
  refine analyticOnNhd_of_coords_of_locBdd_reindex σ famPhi hUo (fun a => ?_) (fun x hx => ?_)
  · intro x hx
    have hcol : AnalyticAt ℂ (fun y : PotPair × PotPair => complexMixedColumn y.1 y.2 a.1.1 a.1.2) x :=
      NlsGge.Atomic.G1098M1.g1098M1_column_analyticOnNhd a.1.1 a.1.2 x (hUs hx)
    have hv : AnalyticAt ℂ (fun y : PotPair × PotPair => famVec y a.1) x :=
      hcol.sub analyticAt_const
    have hL : AnalyticAt ℂ (fun y : PotPair × PotPair => fourierCoefCLM a.2 (famVec y a.1)) x :=
      AnalyticAt.comp (f := fun y : PotPair × PotPair => famVec y a.1) (x := x)
        ((fourierCoefCLM a.2).analyticAt (famVec x a.1)) hv
    exact hL.congr (Filter.eventually_of_mem (hUo.mem_nhds hx) fun y hy =>
      (fourierCoefCLM_apply a.2 (famVec y a.1)).trans (famPhi_apply y (hUsum y hy) a).symm)
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUo x hx
    refine ⟨r, hr, C + 1, fun y hy => ?_⟩
    have hyU : y ∈ U := hball hy
    have hsq : ‖famPhi y‖ ^ 2 ≤ C := by
      rw [lp2_norm_sq, famPhi_tsum y (hUsum y hyU)]
      exact hCb y hyU
    nlinarith [norm_nonneg (famPhi y), sq_nonneg (‖famPhi y‖ - 1)]

/-! ### Synthesis operator on the normalized real basis -/

/-- Normalized synthesis coefficients of the vacuum-subtracted columns. -/
def wfam (u v : PhysicalL2) (j : ℤ × Bool) : PhysicalL2 :=
  ((‖mixedReference j.1 j.2‖⁻¹ : ℝ)) • (mixedColumn u v j.1 j.2 - mixedReference j.1 j.2)

theorem norm_mixedReference_ge_one (n : ℤ) (minus : Bool) : 1 ≤ ‖mixedReference n minus‖ := by
  rw [norm_mixedReference]
  split_ifs <;> norm_num

theorem inv_norm_mixedReference_le_one (n : ℤ) (minus : Bool) :
    ‖mixedReference n minus‖⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (norm_mixedReference_ge_one n minus)

theorem wfam_eq_famVec (u v : PhysicalL2) (j : ℤ × Bool) :
    wfam u v j = ((‖mixedReference j.1 j.2‖⁻¹ : ℝ)) • famVec (realSlice u, realSlice v) j := by
  unfold wfam famVec
  simp only [mixedColumn_eq_complex]

theorem norm_wfam_sq_le (u v : PhysicalL2) (j : ℤ × Bool) :
    ‖wfam u v j‖ ^ 2 ≤ ‖famVec (realSlice u, realSlice v) j‖ ^ 2 := by
  rw [wfam_eq_famVec]
  exact norm_smul_sq_le_of_le_one (inv_nonneg.mpr (norm_nonneg _))
    (inv_norm_mixedReference_le_one j.1 j.2) _

theorem summable_wfam (u v : PhysicalL2) : Summable fun j => ‖wfam u v j‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => norm_wfam_sq_le u v j)
    (summable_famVec_real u v)

theorem norm_wfam_sub_sq_le (u v u₀ v₀ : PhysicalL2) (j : ℤ × Bool) :
    ‖wfam u v j - wfam u₀ v₀ j‖ ^ 2 ≤
      ‖famVec (realSlice u, realSlice v) j - famVec (realSlice u₀, realSlice v₀) j‖ ^ 2 := by
  rw [wfam_eq_famVec, wfam_eq_famVec, ← smul_sub]
  exact norm_smul_sq_le_of_le_one (inv_nonneg.mpr (norm_nonneg _))
    (inv_norm_mixedReference_le_one j.1 j.2) _

theorem summable_wfam_sub (u v u₀ v₀ : PhysicalL2) :
    Summable fun j => ‖wfam u v j - wfam u₀ v₀ j‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => norm_wfam_sub_sq_le u v u₀ v₀ j)
    (summable_famVec_sub (summable_famVec_real u v) (summable_famVec_real u₀ v₀))

theorem mixedRealBasis_ref (n : ℤ) (minus : Bool) :
    mixedReference n minus = (‖mixedReference n minus‖ : ℝ) • mixedRealBasis (n, minus) := by
  rw [mixedRealBasis_apply, mixedBasisVec_eq_smul, smul_smul,
    mul_inv_cancel₀ (norm_mixedReference_pos n minus).ne', one_smul]

/-- The bounded operator `id + synthOp` built from the normalized column coefficients. -/
noncomputable def synthA (u v : PhysicalL2) : PhysicalL2 →L[ℝ] PhysicalL2 :=
  ContinuousLinearMap.id ℝ PhysicalL2 + synthOp mixedRealBasis (w := wfam u v) (summable_wfam u v)

theorem synthA_basis (u v : PhysicalL2) (j : ℤ × Bool) :
    synthA u v (mixedRealBasis j) = mixedRealBasis j + wfam u v j := by
  unfold synthA
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, synthOp_basis]

theorem synthA_ref (u v : PhysicalL2) (n : ℤ) (minus : Bool) :
    synthA u v (mixedReference n minus) = mixedColumn u v n minus := by
  have e2 : (‖mixedReference n minus‖ : ℝ) • wfam u v (n, minus)
      = mixedColumn u v n minus - mixedReference n minus := by
    unfold wfam
    rw [smul_smul, mul_inv_cancel₀ (norm_mixedReference_pos n minus).ne', one_smul]
  rw [mixedRealBasis_ref n minus, map_smul, synthA_basis, smul_add, e2, ← mixedRealBasis_ref n minus]
  abel

theorem mixedSquaredOperator_eq_synthA (u v : PhysicalL2) :
    mixedSquaredOperator u v = synthA u v :=
  mixedSquaredOperator_eq_of u v (synthA u v) (synthA_ref u v)

/-! ### The head G1_098 -/

/-- Operator-norm estimate for the synthesis difference, by Parseval on the Fourier family. -/
theorem mSO_sub_le (u v u₀ v₀ : PhysicalL2)
    (hs : Summable fun j : ℤ × Bool => ‖famVec (realSlice u, realSlice v) j‖ ^ 2)
    (hs0 : Summable fun j : ℤ × Bool => ‖famVec (realSlice u₀, realSlice v₀) j‖ ^ 2) :
    ‖mixedSquaredOperator u v - mixedSquaredOperator u₀ v₀‖ ≤
      ‖famPhi (realSlice u, realSlice v) - famPhi (realSlice u₀, realSlice v₀)‖ := by
  have hA : ‖mixedSquaredOperator u v - mixedSquaredOperator u₀ v₀‖ ≤
      Real.sqrt (∑' j, ‖wfam u v j - wfam u₀ v₀ j‖ ^ 2) := by
    rw [mixedSquaredOperator_eq_synthA, mixedSquaredOperator_eq_synthA]
    unfold synthA
    rw [add_sub_add_left_eq_sub]
    exact norm_synthOp_sub_le mixedRealBasis (summable_wfam u v) (summable_wfam u₀ v₀)
      (summable_wfam_sub u v u₀ v₀)
  have hB : ∑' j, ‖wfam u v j - wfam u₀ v₀ j‖ ^ 2 ≤
      ∑' j, ‖famVec (realSlice u, realSlice v) j - famVec (realSlice u₀, realSlice v₀) j‖ ^ 2 :=
    Summable.tsum_le_tsum (fun j => norm_wfam_sub_sq_le u v u₀ v₀ j)
      (summable_wfam_sub u v u₀ v₀) (summable_famVec_sub hs hs0)
  have hC' := famPhi_sub_norm_sq hs hs0
  calc _ ≤ Real.sqrt (∑' j, ‖wfam u v j - wfam u₀ v₀ j‖ ^ 2) := hA
    _ ≤ Real.sqrt (‖famPhi (realSlice u, realSlice v)
          - famPhi (realSlice u₀, realSlice v₀)‖ ^ 2) :=
        Real.sqrt_le_sqrt (hB.trans hC'.symm.le)
    _ = _ := Real.sqrt_sq (norm_nonneg _)

theorem realPair_continuous :
    Continuous fun x : PhysicalL2 × PhysicalL2 => (realSlice x.1, realSlice x.2) :=
  (realSlice.continuous.comp continuous_fst).prodMk (realSlice.continuous.comp continuous_snd)

theorem tendsto_norm_sub_of_continuousAt {X Y : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup Y] {F : X → Y} {x0 : X} (hF : ContinuousAt F x0) :
    Tendsto (fun x => ‖F x - F x0‖) (𝓝 x0) (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp hF

theorem continuousAt_of_norm_le {X Y : Type*} [TopologicalSpace X] [SeminormedAddCommGroup Y]
    {F : X → Y} {x0 : X} {h : X → ℝ} (hle : ∀ᶠ x in 𝓝 x0, ‖F x - F x0‖ ≤ h x)
    (hh : Tendsto h (𝓝 x0) (𝓝 0)) : ContinuousAt F x0 :=
  tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _) hle hh)

theorem famPhi_pair_continuousAt (U : Set (PotPair × PotPair)) (hUo : IsOpen U)
    (hUs : U ⊆ gkW ×ˢ gkW) (hUsum : ∀ p ∈ U, Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2)
    (C : ℝ) (hC0 : 0 ≤ C) (hCb : ∀ p ∈ U, ∑' j : ℤ × Bool, ‖famVec p j‖ ^ 2 ≤ C)
    (x0 : PhysicalL2 × PhysicalL2) (hq : (realSlice x0.1, realSlice x0.2) ∈ U) :
    ContinuousAt (fun x : PhysicalL2 × PhysicalL2 => famPhi (realSlice x.1, realSlice x.2)) x0 :=
  ContinuousAt.comp (f := fun x : PhysicalL2 × PhysicalL2 => (realSlice x.1, realSlice x.2))
    (x := x0) ((famPhi_analyticOn U hUo hUs hUsum C hC0 hCb _ hq).continuousAt)
    realPair_continuous.continuousAt

theorem mSO_eventually_le (U : Set (PotPair × PotPair)) (hUsum : ∀ p ∈ U,
      Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2)
    (x0 : PhysicalL2 × PhysicalL2) (hq : (realSlice x0.1, realSlice x0.2) ∈ U)
    (hUn : U ∈ 𝓝 (realSlice x0.1, realSlice x0.2)) :
    ∀ᶠ x in 𝓝 x0, ‖mixedSquaredOperator x.1 x.2 - mixedSquaredOperator x0.1 x0.2‖ ≤
      ‖famPhi (realSlice x.1, realSlice x.2) - famPhi (realSlice x0.1, realSlice x0.2)‖ := by
  have hPU : ∀ᶠ x in 𝓝 x0, (realSlice x.1, realSlice x.2) ∈ U :=
    realPair_continuous.continuousAt.preimage_mem_nhds hUn
  filter_upwards [hPU] with x hx
  exact mSO_sub_le x.1 x.2 x0.1 x0.2 (hUsum _ hx) (hUsum _ hq)

/-- Continuity of the mixed squared-eigenfunction map in operator norm. -/
theorem mixedSquaredOperator_continuous :
    Continuous (fun p : PhysicalL2 × PhysicalL2 => mixedSquaredOperator p.1 p.2) := by
  refine continuous_iff_continuousAt.mpr fun x0 => ?_
  obtain ⟨U, hUn, hUo, hUs, C, hC0, hC⟩ :=
    NlsGge.ThirdConsultation.G1098M2H.complexMixedColumn_local_square_sum x0.1 x0.2
  have hq : (realSlice x0.1, realSlice x0.2) ∈ U := mem_of_mem_nhds hUn
  have hUsum : ∀ p ∈ U, Summable fun j : ℤ × Bool => ‖famVec p j‖ ^ 2 :=
    fun p hp => (hC p hp).1
  have hCb : ∀ p ∈ U, ∑' j : ℤ × Bool, ‖famVec p j‖ ^ 2 ≤ C := fun p hp => (hC p hp).2
  exact continuousAt_of_norm_le
    (F := fun p : PhysicalL2 × PhysicalL2 => mixedSquaredOperator p.1 p.2)
    (h := fun x => ‖famPhi (realSlice x.1, realSlice x.2)
      - famPhi (realSlice x0.1, realSlice x0.2)‖)
    (mSO_eventually_le U hUsum x0 hq hUn)
    (tendsto_norm_sub_of_continuousAt
      (F := fun x : PhysicalL2 × PhysicalL2 => famPhi (realSlice x.1, realSlice x.2))
      (famPhi_pair_continuousAt U hUo hUs hUsum C hC0 hCb x0 hq))

/-- G1-098 (verbatim head of STATEMENTS/G1.md; Pro round 9 section 13). -/
theorem G1_098 :
    (∀ u v : PhysicalL2,
      ∃! A : PhysicalL2 →L[ℝ] PhysicalL2,
        ∀ n : ℤ, ∀ minus : Bool,
          A (mixedReference n minus) = mixedColumn u v n minus) ∧
    (∀ u v : PhysicalL2, ∀ n : ℤ, ∀ minus : Bool,
      mixedSquaredOperator u v (mixedReference n minus) = mixedColumn u v n minus) ∧
    Continuous (fun p : PhysicalL2 × PhysicalL2 => mixedSquaredOperator p.1 p.2) := by
  refine ⟨fun u v => ⟨synthA u v, synthA_ref u v, fun A hA =>
    eq_of_mixedReference A (synthA u v) fun n minus =>
      (hA n minus).trans (synthA_ref u v n minus).symm⟩, fun u v n minus => ?_,
    mixedSquaredOperator_continuous⟩
  rw [mixedSquaredOperator_eq_synthA]
  exact synthA_ref u v n minus

end
end NlsGge.Atomic.G1098
