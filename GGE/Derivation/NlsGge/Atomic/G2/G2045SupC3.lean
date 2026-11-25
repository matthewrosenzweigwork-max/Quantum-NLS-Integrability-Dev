import Mathlib
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.Atomic.G2.G2045SupB4
-- WRAPPER-IMPORTS-BEGIN
import NlsGge.Atomic.G1.G1086
import NlsGge.Atomic.KST.KST065
import NlsGge.Atomic.G2.G2045SupA4
import NlsGge.Atomic.G2.G2045SupC2
import NlsGge.Atomic.G2.G2042
import NlsGge.Atomic.G2.G2043
import NlsGge.Atomic.G2.G2075
-- WRAPPER-IMPORTS-END

/- G2-045 support kit G2045SupC3 (proof development, AUTHOR; not reviewed).
   Target NlsGge/Atomic/G2/G2045SupC3.lean, namespace NlsGge.GKDefinitionDesign.
   Real-slice trace identity for every u in H^(k-1): sum' n, higherAction k (realSlice u) n
   = -k/(2I)^(k-1) * hierarchyHamiltonian k (realSlice u).  Route (G2045_STOP.md item D): G1_086 supplies finite-gap
   v with physicalSobolevNorm (k-1) (v-u) small; kst065 gives smoothness; G2045SupA_finiteGap_trace gives the identity
   at realSlice v; pass to the limit with the continuity of F (G2045SupC2) and of H_k (G2045SupB4).
   Also the transfer pairSobolev (realSlice u) <-> physicalSobolev u used by the ball identity's `hr` hypothesis. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

/-- `u ∈ H^N` implies `realSlice u ∈ H^N × H^N`. -/
theorem g2045c_real_pair (N : ℕ) (u : PhysicalL2) (hu : physicalSobolev (N : ℝ) u) :
    pairSobolev (N : ℝ) (realSlice u) := ⟨hu, g2045b_psob_star _ _ hu⟩

/-- `realSlice u ∈ H^N × H^N` implies `u ∈ H^N` (first component). -/
theorem g2045c_pair_real (N : ℕ) (u : PhysicalL2) (h : pairSobolev (N : ℝ) (realSlice u)) :
    physicalSobolev (N : ℝ) u := h.1

theorem g2045c_real_pn_sub (N : ℕ) (v u : PhysicalL2) :
    pairSobolevNorm (N : ℝ) (realSlice v - realSlice u) ≤ 2 * physicalSobolevNorm (N : ℝ) (v - u) := by
  have e : realSlice v - realSlice u = realSlice (v - u) := (map_sub realSlice v u).symm
  rw [e]
  unfold pairSobolevNorm
  show Real.sqrt (physicalSobolevNorm (N : ℝ) (v - u) ^ 2 + physicalSobolevNorm (N : ℝ) (star (v - u)) ^ 2) ≤ _
  rw [g2045b_psn_star]
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg zero_le_two (psn_nonneg N _), ?_⟩
  nlinarith [sq_nonneg (physicalSobolevNorm (N : ℝ) (v - u))]

/-- Core of the real-slice trace identity.  Hypotheses (all landed theorems, instantiated in the wrapper):
`hFc` continuity of `F` at `realSlice u` (G2045SupC2), `hdens` = second conjunct of `G1_086`,
`htrace` = finite-gap trace identity (G2045SupA_finiteGap_trace with the smoothness of `kst065`). -/
theorem g2045c_real_trace_core (k : ℕ) (hk : 2 ≤ k) (u : PhysicalL2)
    (hu : physicalSobolev ((k - 1 : ℕ) : ℝ) u)
    (hFc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ φ : PotPair, pairSobolev ((k - 1 : ℕ) : ℝ) φ →
      pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - realSlice u) < δ →
      ‖(∑' n : ℤ, higherAction k φ n) - ∑' n : ℤ, higherAction k (realSlice u) n‖ < ε)
    (hdens : ∀ r : ℝ, 0 ≤ r → ∀ w : PhysicalL2, physicalSobolev r w → ∀ ε : ℝ, 0 < ε →
      ∃ v : PhysicalL2, NlsGge.ThirdConsultation.finiteGap v ∧ physicalSobolev r v ∧
        physicalSobolevNorm r (v - w) < ε)
    (htrace : ∀ v : PhysicalL2, NlsGge.ThirdConsultation.finiteGap v →
      HasSum (fun n : ℤ => higherAction k (realSlice v) n)
        (-(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice v))) :
    ∑' n : ℤ, higherAction k (realSlice u) n =
      -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice u) := by
  have hc : pairSobolev ((k - 1 : ℕ) : ℝ) (realSlice u) := g2045c_real_pair _ u hu
  set κ : ℝ := ‖-(k : ℂ) / (2 * Complex.I) ^ (k - 1)‖ with hκ
  have hκ0 : 0 ≤ κ := norm_nonneg _
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∑' n : ℤ, higherAction k (realSlice u) n) -
        -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice u)‖ < ε := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, hF⟩ := hFc (ε / 2) (by positivity)
    obtain ⟨δ₂, hδ₂, hH⟩ := g2045b_hamiltonian_continuous k hk (realSlice u) hc (ε / (2 * (κ + 1)))
      (by positivity)
    obtain ⟨v, hfg, hv, hvn⟩ := hdens ((k - 1 : ℕ) : ℝ) (Nat.cast_nonneg _) u hu
      (min δ₁ δ₂ / 2) (half_pos (lt_min hδ₁ hδ₂))
    have hφ : pairSobolev ((k - 1 : ℕ) : ℝ) (realSlice v) := g2045c_real_pair _ v hv
    have hpn : pairSobolevNorm ((k - 1 : ℕ) : ℝ) (realSlice v - realSlice u) < min δ₁ δ₂ :=
      lt_of_le_of_lt (g2045c_real_pn_sub _ v u) (by linarith)
    have hs := htrace v hfg
    have h1 := hF (realSlice v) hφ (lt_of_lt_of_le hpn (min_le_left _ _))
    have h2 := hH (realSlice v) hφ (lt_of_lt_of_le hpn (min_le_right _ _))
    rw [hs.tsum_eq] at h1
    set a : ℂ := -(k : ℂ) / (2 * Complex.I) ^ (k - 1) with ha
    have e : (∑' n : ℤ, higherAction k (realSlice u) n) - a * hierarchyHamiltonian k (realSlice u) =
        -(a * hierarchyHamiltonian k (realSlice v) - ∑' n : ℤ, higherAction k (realSlice u) n) +
        a * (hierarchyHamiltonian k (realSlice v) - hierarchyHamiltonian k (realSlice u)) := by ring
    have h3 : ‖a * (hierarchyHamiltonian k (realSlice v) - hierarchyHamiltonian k (realSlice u))‖ <
        ε / 2 := by
      rw [norm_mul]
      have : κ * ‖hierarchyHamiltonian k (realSlice v) - hierarchyHamiltonian k (realSlice u)‖ ≤
          κ * (ε / (2 * (κ + 1))) := mul_le_mul_of_nonneg_left h2.le hκ0
      have h4 : κ * (ε / (2 * (κ + 1))) < ε / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      exact lt_of_le_of_lt this h4
    rw [e]
    calc _ ≤ ‖-(a * hierarchyHamiltonian k (realSlice v) - ∑' n : ℤ, higherAction k (realSlice u) n)‖ +
          ‖a * (hierarchyHamiltonian k (realSlice v) - hierarchyHamiltonian k (realSlice u))‖ :=
            norm_add_le _ _
      _ < ε := by rw [norm_neg]; linarith
  by_contra hne
  have hpos : 0 < ‖(∑' n : ℤ, higherAction k (realSlice u) n) -
      -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice u)‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 hne)
  exact lt_irrefl _ (key _ hpos)

-- WRAPPER-BEGIN
theorem g2045c_real_trace (k : ℕ) (hk : 2 ≤ k) (u : PhysicalL2)
    (hu : physicalSobolev ((k - 1 : ℕ) : ℝ) u) :
    ∑' n : ℤ, higherAction k (realSlice u) n =
      -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice u) :=
  g2045c_real_trace_core k hk u hu
    (g2045c_F_continuous k hk (realSlice u) (G2_075.2.1 ⟨u, rfl⟩) (g2045c_real_pair _ u hu))
    G1_086.2
    (fun v hfg => (G2045SupA_finiteGap_trace v (NlsGge.ThirdConsultation.KST.kst065 v hfg).2.1 hfg k hk).2)
-- WRAPPER-END

end NlsGge.GKDefinitionDesign
end
