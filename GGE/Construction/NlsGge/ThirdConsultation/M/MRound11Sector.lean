import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.Analysis.FullCoverFourier
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST016

   
                                                                          

                                                                                                     
                                                                                                     
                                                                                                         
                                                                                  
                                                                                           
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoModeSupp

open scoped InnerProduct InnerProductSpace
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open NlsGge.ThirdConsultation.MTwoMode

/-- The parity sector as a subspace (inner-product form of the Fourier-support condition). -/
def sectorSub (n : ℤ) : Submodule ℂ KSTPairL2 where
  carrier := {f | ∀ (b : Bool) (k : ℤ), k % 2 ≠ n % 2 →
    inner ℂ (PiLp.single 2 b (spectralBasis k) : KSTPairL2) f = 0}
  zero_mem' := by
    intro b k _
    simp
  add_mem' := by
    intro f g hf hg b k hk
    rw [inner_add_right, hf b k hk, hg b k hk, add_zero]
  smul_mem' := by
    intro c f hf b k hk
    rw [inner_smul_right, hf b k hk, mul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem fourierCoeff_eq_inner (g : SpectralScalarL2) (k : ℤ) :
    _root_.fourierCoeff g k = inner ℂ (spectralBasis k) g := by
  have hb : (fourierBasis (T := (2 : ℝ))) k = spectralBasis k :=
    congrFun (coe_fourierBasis (T := (2 : ℝ))) k
  rw [NlsGge.Atomic.KST016.fc_repr, ← hb]
  exact (fourierBasis (T := (2 : ℝ))).repr_apply_apply g k

theorem mem_sectorSub_iff_parity (n : ℤ) (f : KSTPairL2) :
    f ∈ sectorSub n ↔ paritySector n f := by
  constructor
  · intro h b k hk
    have := h b k hk
    rw [NlsGge.Atomic.KST016.inner_single_left, ← fourierCoeff_eq_inner] at this
    exact this
  · intro h b k hk
    rw [NlsGge.Atomic.KST016.inner_single_left, ← fourierCoeff_eq_inner]
    exact h b k hk

theorem mem_sectorSub_iff_repr (n : ℤ) (f : KSTPairL2) :
    f ∈ sectorSub n ↔
      ∀ (b : Bool) (k : ℤ), k % 2 ≠ n % 2 →
        (fourierBasis (T := (2 : ℝ))).repr (f b) k = 0 := by
  rw [mem_sectorSub_iff_parity]
  unfold paritySector
  simp only [NlsGge.Atomic.KST016.fc_repr]

theorem sectorSub_isClosed (n : ℤ) : IsClosed (sectorSub n : Set KSTPairL2) := by
  have h : (sectorSub n : Set KSTPairL2) =
      ⋂ b : Bool, ⋂ k : ℤ, ⋂ (_ : k % 2 ≠ n % 2),
        {f : KSTPairL2 | inner ℂ (PiLp.single 2 b (spectralBasis k) : KSTPairL2) f = 0} := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_iInter]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun b => isClosed_iInter fun k => isClosed_iInter fun _ => ?_
  exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

theorem inner_basis_basis (k m : ℤ) :
    inner ℂ (spectralBasis k) (spectralBasis m) = if k = m then (1 : ℂ) else 0 :=
  orthonormal_iff_ite.mp (orthonormal_fourier (T := (2 : ℝ))) k m

theorem kstPnLower_mem (n : ℤ) : kstPnLower n ∈ sectorSub n := by
  intro b k hk
  have hkn : k ≠ n := fun h => hk (by rw [h])
  unfold kstPnLower
  rw [NlsGge.Atomic.KST016.inner_single_left]
  cases b
  · simp [inner_basis_basis, hkn]
  · simp

theorem kstPnUpper_mem (n : ℤ) : kstPnUpper n ∈ sectorSub n := by
  intro b k hk
  have hkn : k ≠ -n := fun h => hk (by rw [h]; omega)
  unfold kstPnUpper
  rw [NlsGge.Atomic.KST016.inner_single_left]
  cases b
  · simp
  · simp [inner_basis_basis, hkn]

theorem spectralPn_mem (n : ℤ) (x : KSTPairL2) : spectralPn n x ∈ sectorSub n := by
  rw [spectralPn_apply]
  exact add_mem (Submodule.smul_mem _ _ (kstPnUpper_mem n))
    (Submodule.smul_mem _ _ (kstPnLower_mem n))

theorem fm_single_mem (n c : ℤ) (b0 : Bool) (g : SpectralScalarL2)
    (hg : ∀ m : ℤ, m % 2 ≠ 0 → _root_.fourierCoeff g m = 0) (hc : c % 2 = n % 2) :
    (PiLp.single 2 b0 (NlsGge.Schur.fourierMultiplier c g) : KSTPairL2) ∈ sectorSub n := by
  intro b k hk
  rw [NlsGge.Atomic.KST016.inner_single_left]
  by_cases hb : b = b0
  · subst hb
    simp only [PiLp.single_eq_same]
    rw [NlsGge.Atomic.KST016.inner_basis_mul]
    exact hg _ (by omega)
  · simp [hb]

theorem potentialOnPn_mem (p : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (x : KSTPairL2) :
    NlsGge.Atomic.KST012.potentialOnPn p n x ∈ sectorSub n := by
  rw [NlsGge.Atomic.KST016.pot_apply]
  refine add_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · exact fm_single_mem n n true _
      (fun m hm => NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd _ m hm) rfl
  · refine fm_single_mem n (-n) false _
      (fun m hm => NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd _ m hm) (by omega)

theorem qOperator_mem (p : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n) (f : KSTPairL2)
    (hf : f ∈ sectorSub n) :
    NlsGge.Atomic.KST006.qOperator p n z hz f ∈ sectorSub n := by
  rw [mem_sectorSub_iff_repr] at hf ⊢
  intro b l hl
  cases b
  · rw [NlsGge.Atomic.KST006.qOperator_lower_coeff]
    refine (tsum_congr (fun m => ?_)).trans tsum_zero
    by_cases hm : (l - m) % 2 = 0
    · have : m % 2 ≠ n % 2 := by omega
      rw [hf true m this]
      simp
    · rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd _ _ hm]
      simp
  · rw [NlsGge.Atomic.KST006.qOperator_upper_coeff]
    refine (tsum_congr (fun m => ?_)).trans tsum_zero
    by_cases hm : (l - m) % 2 = 0
    · have : m % 2 ≠ n % 2 := by omega
      rw [hf false m this]
      simp
    · rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd _ _ hm]
      simp

theorem qOperator_pow_mem (p : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n) (f : KSTPairL2)
    (hf : f ∈ sectorSub n) (m : ℕ) :
    ((NlsGge.Atomic.KST006.qOperator p n z hz) ^ m) f ∈ sectorSub n := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    rw [pow_succ']
    exact qOperator_mem p n z hz _ ih

/-- The Neumann inverse preserves the parity sector under the small-square hypothesis. -/
theorem inverse_one_sub_mem (p : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖NlsGge.Atomic.KST006.qOperator p n z hz ^ 2‖ < 1) (f : KSTPairL2)
    (hf : f ∈ sectorSub n) :
    Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator p n z hz) f ∈ sectorSub n := by
  have hs := (NlsGge.Atomic.KST016.inverse_series_of_square_small _ hT).2
  have hs' : HasSum (fun m : ℕ => ((NlsGge.Atomic.KST006.qOperator p n z hz) ^ m) f)
      (Ring.inverse (1 - NlsGge.Atomic.KST006.qOperator p n z hz) f) :=
    (ContinuousLinearMap.apply ℂ KSTPairL2 f).hasSum hs
  refine (sectorSub_isClosed n).mem_of_tendsto hs'.tendsto_sum_nat
    (Filter.Eventually.of_forall fun N => ?_)
  exact Submodule.sum_mem _ (fun m _ => qOperator_pow_mem p n z hz f hf m)

theorem complementaryMultiplier_mem (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n) (f : KSTPairL2)
    (hf : f ∈ sectorSub n) :
    complementaryMultiplier n z hz f ∈ sectorSub n := by
  rw [mem_sectorSub_iff_repr] at hf ⊢
  intro b k hk
  have h : complementaryMultiplier n z hz f b = scalarComplementaryMultiplier n z hz b (f b) := rfl
  rw [h, scalarComplementaryMultiplier_repr, hf b k hk, mul_zero]

/-- The reconstructed eigenvector `u + D(V u + (1-T)⁻¹ T V u)` lies in the parity sector of `n`. -/
theorem reconstruction_mem (p : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : ‖NlsGge.Atomic.KST006.qOperator p n z hz ^ 2‖ < 1) (u : KSTPairL2)
    (hu : u ∈ sectorSub n) :
    u + NlsGge.Atomic.KST012.reconstructedComplement p n z hz u ∈ sectorSub n := by
  refine add_mem hu ?_
  unfold NlsGge.Atomic.KST012.reconstructedComplement
  refine complementaryMultiplier_mem n z hz _ (add_mem (potentialOnPn_mem p n u) ?_)
  unfold NlsGge.Atomic.KST012.qEquationSolution
  exact inverse_one_sub_mem p n z hz hT _ (qOperator_mem p n z hz _ (potentialOnPn_mem p n u))

end NlsGge.ThirdConsultation.MTwoModeSupp

end
