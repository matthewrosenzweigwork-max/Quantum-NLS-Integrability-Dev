import Mathlib
import NlsGge.Atomic.M.M006
import NlsGge.Atomic.M.M014
import NlsGge.GK38.MolnarMoments
import NlsGge.GK38.RealTypeSpectrumLevels
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.ThirdConsultation.M.HigherActionContinuous
import NlsGge.Atomic.M.M018Density
import NlsGge.Atomic.M.M018Even

/- M-018 UNIFORM ACTION TAILS AT EVERY ORDER, PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   SUPPORT (no packet increment). Target NlsGge/Atomic/M/M018Tails.lean, namespace NlsGge.ThirdConsultation.M018T.
   For k ≥ 2 and v_j → u in SobolevR (k-1): the order-k actions of physicalOfSobolev (v_j) have ENNReal tails small
   uniformly in j.  Odd k = 2m+1: h782's odd_higher_action_tails_of_tendsto (hypothesis `hodd`, its exact head type)
   after the continuous cast to SobolevR m.  Even k = 2m: M018E.even_action_le, the odd tails at 2m+1 and 2m-1, and for
   m = 1 Scheffé tails of the order-1 actions (Σ_n higherAction w n 1 = ‖w‖², landed GK38.momentSum_zero_eq_normSq +
   M-014; pointwise convergence from h782's higherAction_continuous_real).  `hcast` is the exact type of h782's
   MOddSum.physicalOfSobolev_lowerSobolevCast (pending landing). -/
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.GKDefinitionDesign NlsGge.Birkhoff
open NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.M018T

open NlsGge.ThirdConsultation.M

theorem continuous_physicalOfSobolev (m : ℕ) :
    Continuous (fun w : SobolevR m => physicalOfSobolev w) :=
  (riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)).continuous.comp
    (continuous_ordinarySobolevCoordinates m)

theorem continuous_lowerSobolevCast (i m : ℕ) (him : i ≤ m) :
    Continuous (fun w : SobolevR m => lowerSobolevCast i m him w) := by
  set castL : SobolevR m →L[ℝ] SobolevR i :=
    ((physicalSobolevFourierEquiv38 (i : ℝ)).symm.toContinuousLinearEquiv :
        SobolevCarrier38 (i : ℝ) →L[ℝ] SobolevR i).comp
      ((carrierIncl38 (Nat.cast_le.mpr him : (i : ℝ) ≤ (m : ℝ))).comp
        ((physicalSobolevFourierEquiv38 (m : ℝ)).toContinuousLinearEquiv :
          SobolevR m →L[ℝ] SobolevCarrier38 (m : ℝ)))
  have e : (fun w : SobolevR m => lowerSobolevCast i m him w) = fun w => castL w := funext fun w => rfl
  rw [e]
  exact castL.continuous

theorem odd_action_nonneg (w : PhysicalL2) (n : ℤ) (m : ℕ) :
    0 ≤ higherAction w n (2 * m + 1) := by
  obtain ⟨-, -, -, -, he⟩ := higher_action_gap_integral w n (2 * m + 1) (by omega)
  rw [he]
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (gap_endpoint_levels38 w n).1 ?_)
  intro x _
  rw [show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]
  exact mul_nonneg (by positivity) (actualGapHeightE02_38_nonneg w x)

theorem action_one_hasSum (w : PhysicalL2) (hw : SobolevSquareSummable 1 (physicalFourier w)) :
    HasSum (fun n : ℤ => higherAction w n 1) (‖w‖ ^ 2) := by
  have h := momentSum_zero_eq_normSq w hw
  convert h using 1
  funext n
  obtain ⟨-, -, -, -, he⟩ := higher_action_gap_integral w n 1 le_rfl
  rw [he]
  simp [periodicMinus, periodicPlus, spectralHeight]

/-- ENNReal tail monotonicity in the cutoff. -/
theorem etail_anti (f : ℤ → ℝ≥0∞) {L L' : ℕ} (h : L ≤ L') :
    (∑' n : ℤ, if L' ≤ n.natAbs then f n else 0) ≤ ∑' n : ℤ, if L ≤ n.natAbs then f n else 0 :=
  ENNReal.tsum_le_tsum (fun n => by
    by_cases h1 : L' ≤ n.natAbs
    · rw [if_pos h1, if_pos (le_trans h h1)]
    · rw [if_neg h1]; exact bot_le)

/-- Tails of a sum of two uniformly small tails. -/
theorem etail_add (a c d : ℕ → ℤ → ℝ) (hle : ∀ j n, |a j n| ≤ c j n + d j n)
    (hc0 : ∀ j n, 0 ≤ c j n) (hd0 : ∀ j n, 0 ≤ d j n)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal (c j n) else 0) < ENNReal.ofReal ε)
    (hd : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal (d j n) else 0) < ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal |a j n| else 0) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨L1, h1⟩ := hc (ε / 2) (by positivity)
  obtain ⟨L2, h2⟩ := hd (ε / 2) (by positivity)
  refine ⟨max L1 L2, fun j => ?_⟩
  calc (∑' n : ℤ, if max L1 L2 ≤ n.natAbs then ENNReal.ofReal |a j n| else 0)
      ≤ ∑' n : ℤ, ((if max L1 L2 ≤ n.natAbs then ENNReal.ofReal (c j n) else 0) +
          (if max L1 L2 ≤ n.natAbs then ENNReal.ofReal (d j n) else 0)) := by
        refine ENNReal.tsum_le_tsum (fun n => ?_)
        split_ifs
        · rw [← ENNReal.ofReal_add (hc0 j n) (hd0 j n)]; exact ENNReal.ofReal_le_ofReal (hle j n)
        · simp
    _ = (∑' n : ℤ, if max L1 L2 ≤ n.natAbs then ENNReal.ofReal (c j n) else 0) +
          ∑' n : ℤ, if max L1 L2 ≤ n.natAbs then ENNReal.ofReal (d j n) else 0 := ENNReal.tsum_add
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add (lt_of_le_of_lt (etail_anti _ (le_max_left _ _)) (h1 j))
          (lt_of_le_of_lt (etail_anti _ (le_max_right _ _)) (h2 j))
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- Odd-order tails (with the factor 4^m removed) for a sequence in a higher Sobolev space. -/
theorem odd_tails
    (hodd : ∀ (m : ℕ) (hm : 1 ≤ m) (v : ℕ → SobolevR m) (u : SobolevR m)
      (hv : Tendsto v atTop (𝓝 u)),
      ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
        (∑' n : ℤ, if L ≤ n.natAbs then
          ENNReal.ofReal ((4 : ℝ) ^ m *
            higherAction (physicalOfSobolev (v j)) n (2 * m + 1))
          else 0) < ENNReal.ofReal ε)
    (hcast : ∀ (i m : ℕ) (him : i ≤ m) (u : SobolevR m),
      physicalOfSobolev (lowerSobolevCast i m him u) = physicalOfSobolev u)
    (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r) (v : ℕ → SobolevR r) (u : SobolevR r)
    (hv : Tendsto v atTop (𝓝 u)) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then
        ENNReal.ofReal (higherAction (physicalOfSobolev (v j)) n (2 * m + 1)) else 0) <
        ENNReal.ofReal ε := by
  intro ε hε
  have hw : Tendsto (fun j => lowerSobolevCast m r hmr (v j)) atTop
      (𝓝 (lowerSobolevCast m r hmr u)) :=
    ((continuous_lowerSobolevCast m r hmr).tendsto u).comp hv
  obtain ⟨L, hL⟩ := hodd m hm _ _ hw ε hε
  refine ⟨L, fun j => lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) (hL j)⟩
  rw [hcast]
  split_ifs
  · refine ENNReal.ofReal_le_ofReal ?_
    have h0 := odd_action_nonneg (physicalOfSobolev (v j)) n m
    have h4 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  · exact le_rfl

/-- Order-one (Scheffé) tails. -/
theorem one_tails (r : ℕ) (hr : 1 ≤ r)
    (hcast : ∀ (i m : ℕ) (him : i ≤ m) (u : SobolevR m),
      physicalOfSobolev (lowerSobolevCast i m him u) = physicalOfSobolev u)
    (v : ℕ → SobolevR r) (u : SobolevR r) (hv : Tendsto v atTop (𝓝 u)) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then
        ENNReal.ofReal |higherAction (physicalOfSobolev (v j)) n 1| else 0) <
        ENNReal.ofReal ε := by
  have hH1 : ∀ w : SobolevR r, SobolevSquareSummable 1 (physicalFourier (physicalOfSobolev w)) := by
    intro w
    rw [← hcast 1 r hr w, ← physicalSobolevEmbed_eq_M]
    simpa using (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) _).1
      (physicalSobolevEmbed_mem 1 (lowerSobolevCast 1 r hr w))
  have hpu : Tendsto (fun j => physicalOfSobolev (v j)) atTop (𝓝 (physicalOfSobolev u)) :=
    ((continuous_physicalOfSobolev r).tendsto u).comp hv
  refine NlsGge.ThirdConsultation.M018D.scheffe_tails
    (fun j n => higherAction (physicalOfSobolev (v j)) n 1)
    (fun n => higherAction (physicalOfSobolev u) n 1)
    (fun j => ‖physicalOfSobolev (v j)‖ ^ 2) (‖physicalOfSobolev u‖ ^ 2)
    (fun j n => by simpa using odd_action_nonneg (physicalOfSobolev (v j)) n 0)
    (fun n => ((higherAction_continuous_real n 1 le_rfl).tendsto _).comp hpu)
    (fun j => action_one_hasSum _ (hH1 (v j))) (action_one_hasSum _ (hH1 u))
    ((continuous_norm.tendsto _).comp hpu |>.pow 2)

/-- Uniform tails of the order-k actions, every k ≥ 2. -/
theorem action_tails
    (hodd : ∀ (m : ℕ) (hm : 1 ≤ m) (v : ℕ → SobolevR m) (u : SobolevR m)
      (hv : Tendsto v atTop (𝓝 u)),
      ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
        (∑' n : ℤ, if L ≤ n.natAbs then
          ENNReal.ofReal ((4 : ℝ) ^ m *
            higherAction (physicalOfSobolev (v j)) n (2 * m + 1))
          else 0) < ENNReal.ofReal ε)
    (hcast : ∀ (i m : ℕ) (him : i ≤ m) (u : SobolevR m),
      physicalOfSobolev (lowerSobolevCast i m him u) = physicalOfSobolev u)
    (k : ℕ) (hk : 2 ≤ k) (v : ℕ → SobolevR (k - 1)) (u : SobolevR (k - 1))
    (hv : Tendsto v atTop (𝓝 u)) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then
        ENNReal.ofReal |higherAction (physicalOfSobolev (v j)) n k| else 0) <
        ENNReal.ofReal ε := by
  rcases Nat.even_or_odd' k with ⟨m, hkm | hkm⟩
  · -- even k = 2m, m ≥ 1
    subst hkm
    have hm : 1 ≤ m := by omega
    have hup := odd_tails hodd hcast (2 * m - 1) m hm (by omega) v u hv
    have hle : ∀ j n, |higherAction (physicalOfSobolev (v j)) n (2 * m)| ≤
        higherAction (physicalOfSobolev (v j)) n (2 * m - 1) +
          higherAction (physicalOfSobolev (v j)) n (2 * m + 1) := by
      intro j n
      have e := NlsGge.ThirdConsultation.M018E.even_action_le (physicalOfSobolev (v j)) n m hm
      have h1 : 0 ≤ higherAction (physicalOfSobolev (v j)) n (2 * m - 1) := by
        have := odd_action_nonneg (physicalOfSobolev (v j)) n (m - 1)
        rwa [show 2 * (m - 1) + 1 = 2 * m - 1 by omega] at this
      have h2 := odd_action_nonneg (physicalOfSobolev (v j)) n m
      linarith
    have hlow : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
        (∑' n : ℤ, if L ≤ n.natAbs then
          ENNReal.ofReal (higherAction (physicalOfSobolev (v j)) n (2 * m - 1)) else 0) <
          ENNReal.ofReal ε := by
      by_cases hm1 : m = 1
      · intro ε hε
        have e : 2 * m - 1 = 1 := by omega
        obtain ⟨L, hL⟩ := one_tails (2 * m - 1) (by omega) hcast v u hv ε hε
        refine ⟨L, fun j => lt_of_le_of_lt (le_of_eq ?_) (hL j)⟩
        refine tsum_congr (fun n => ?_)
        split_ifs
        · rw [congrArg (higherAction (physicalOfSobolev (v j)) n) e,
            abs_of_nonneg (by simpa using odd_action_nonneg (physicalOfSobolev (v j)) n 0)]
        · rfl
      · have h := odd_tails hodd hcast (2 * m - 1) (m - 1) (by omega) (by omega) v u hv
        rwa [show 2 * (m - 1) + 1 = 2 * m - 1 by omega] at h
    refine etail_add _ _ _ hle (fun j n => ?_) (fun j n => odd_action_nonneg _ n m) hlow hup
    have := odd_action_nonneg (physicalOfSobolev (v j)) n (m - 1)
    rwa [show 2 * (m - 1) + 1 = 2 * m - 1 by omega] at this
  · -- odd k = 2m+1, m ≥ 1
    subst hkm
    have hm : 1 ≤ m := by omega
    have h := odd_tails hodd hcast (2 * m + 1 - 1) m hm (by omega) v u hv
    intro ε hε
    obtain ⟨L, hL⟩ := h ε hε
    refine ⟨L, fun j => lt_of_le_of_lt (le_of_eq (tsum_congr (fun n => ?_))) (hL j)⟩
    split_ifs
    · rw [abs_of_nonneg (odd_action_nonneg _ n m)]
    · rfl

end NlsGge.ThirdConsultation.M018T
