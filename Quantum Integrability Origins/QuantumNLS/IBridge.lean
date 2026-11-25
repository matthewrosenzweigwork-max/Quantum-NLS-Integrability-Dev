import Mathlib
import QuantumNLS.BulkResponseRiesz

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (I), support: the limit functional `𝒥` and the quadratic completion at the response

Source (F03.tex): `𝒥(F) = (L/2)‖F‖² + (κ/2)𝓔(F) − ⟨Q,F⟩`; the response `F` of (CC:F03:limit-equation) is the unique minimizer; used in the proof of the strong limit as
"quadratic completion at the minimizer".

For the response `F` (`IsBulkResponse L κ Q F`, `Q` measurable) and `w` in the form domain (`J_sub_J`):
`𝒥(w) − 𝒥(F) = (L/2)‖w − F‖² + (κ/2)𝓔(w − F)`.  (`core_small` extracts, from `IsFormCore`, an element of the core with `𝒥(G) − 𝒥(F)` small.)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.IBridge

open QuantumNLS.BulkResponseRiesz (mu2 inner_eq_integral memLp_quot bulkForm_eq_inner sub_mem iota iota_sub
  ae_fst ae_snd)
open QuantumNLS.BulkResponseForm (L2Unit quot formEnergy bulkForm formDomain IsBulkResponse IsFormCore)
open QuantumNLS.QuantileForm (uI)

variable {L κ : ℝ} {Q : ℝ → ℝ}

theorem energy_toReal (hQm : Measurable Q) (w : L2Unit) (hw : w ∈ formDomain Q) :
    (formEnergy Q w).toReal = ∫ p, quot Q w p.1 p.2 ^ 2 ∂mu2 := by
  have hm := memLp_quot Q hQm w hw
  have hi : Integrable (fun p : ℝ × ℝ => quot Q w p.1 p.2 ^ 2) mu2 := hm.integrable_sq
  have : formEnergy Q w = ENNReal.ofReal (∫ p, quot Q w p.1 p.2 ^ 2 ∂mu2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun p => sq_nonneg _)]
    rfl
  rw [this, ENNReal.toReal_ofReal (integral_nonneg fun p => sq_nonneg _)]

theorem bulkForm_self (hQm : Measurable Q) (w : L2Unit) (hw : w ∈ formDomain Q) :
    bulkForm L κ Q w w = L * ‖w‖ ^ 2 + κ * (formEnergy Q w).toReal := by
  rw [energy_toReal hQm w hw]
  unfold bulkForm
  have h1 : ∫ t, (w : ℝ → ℝ) t * (w : ℝ → ℝ) t ∂uI = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
  have h2 : ∫ p, quot Q w p.1 p.2 * quot Q w p.1 p.2 ∂(uI.prod uI) =
      ∫ p, quot Q w p.1 p.2 ^ 2 ∂mu2 :=
    integral_congr_ae (Eventually.of_forall fun p => by simp [sq])
  rw [h1, h2]

/-- The functional `𝒥(w) = (L/2)‖w‖² + (κ/2)𝓔(w) − ⟨Q,w⟩` (`Q0` the `L²` element of `Q`). -/
def Jfun (L κ : ℝ) (Q : ℝ → ℝ) (Q0 w : L2Unit) : ℝ :=
  (L / 2) * ‖w‖ ^ 2 + (κ / 2) * (formEnergy Q w).toReal - inner ℝ Q0 w

theorem inner_Q0 {Q0 : L2Unit} (hQ0 : (Q0 : ℝ → ℝ) =ᵐ[uI] Q) (H : L2Unit) :
    ∫ t, Q t * (H : ℝ → ℝ) t ∂uI = inner ℝ Q0 H := by
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hQ0] with t h
  rw [h]

/-- **Quadratic completion at the response.** -/
theorem J_sub_J (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hQm : Measurable Q) {Q0 : L2Unit}
    (hQ0 : (Q0 : ℝ → ℝ) =ᵐ[uI] Q) {F : L2Unit} (hF : IsBulkResponse L κ Q F)
    {w : L2Unit} (hw : w ∈ formDomain Q) :
    Jfun L κ Q Q0 w - Jfun L κ Q Q0 F =
      (L / 2) * ‖w - F‖ ^ 2 + (κ / 2) * (formEnergy Q ((w - F : L2Unit) : ℝ → ℝ)).toReal := by
  obtain ⟨hFd, hFe⟩ := hF
  have hd := sub_mem hQm hw hFd
  have hJ : ∀ u : L2Unit, u ∈ formDomain Q →
      Jfun L κ Q Q0 u = (1 / 2) * bulkForm L κ Q u u - inner ℝ Q0 u := fun u hu => by
    unfold Jfun; rw [bulkForm_self (L := L) (κ := κ) hQm u hu]; ring
  have hB : bulkForm L κ Q w w = bulkForm L κ Q F F + 2 * inner ℝ Q0 (w - F) +
      bulkForm L κ Q ((w - F : L2Unit) : ℝ → ℝ) ((w - F : L2Unit) : ℝ → ℝ) := by
    have e1 := bulkForm_eq_inner hL hκ hQm w w hw hw
    have e2 := bulkForm_eq_inner hL hκ hQm F F hFd hFd
    have e3 := bulkForm_eq_inner hL hκ hQm (w - F) (w - F) hd hd
    have e4 := bulkForm_eq_inner hL hκ hQm F (w - F) hFd hd
    have hι := iota_sub (L := L) (κ := κ) hQm hw hFd
    have hab : inner ℝ (iota L κ hQm F hFd) (iota L κ hQm (w - F) hd) = inner ℝ Q0 (w - F) := by
      rw [← e4, hFe _ hd, inner_Q0 hQ0]
    have hw' : iota L κ hQm w hw = iota L κ hQm (w - F) hd + iota L κ hQm F hFd := by
      rw [hι]; abel
    rw [e1, hw']
    simp only [inner_add_left, inner_add_right]
    rw [real_inner_comm (iota L κ hQm F hFd) (iota L κ hQm (w - F) hd), hab, ← e2, ← e3]
    ring
  rw [hJ w hw, hJ F hFd, hB, bulkForm_self (L := L) (κ := κ) hQm (w - F) hd, inner_sub_right]
  ring

theorem formEnergy_swap_sub (F G : L2Unit) :
    formEnergy Q ((F - G : L2Unit) : ℝ → ℝ) = formEnergy Q ((G - F : L2Unit) : ℝ → ℝ) := by
  unfold formEnergy
  refine lintegral_congr_ae ?_
  filter_upwards [ae_fst (Lp.coeFn_sub F G), ae_snd (Lp.coeFn_sub F G),
    ae_fst (Lp.coeFn_sub G F), ae_snd (Lp.coeFn_sub G F)] with p h1 h2 h3 h4
  simp only [quot]
  rw [h1, h2, h3, h4]
  simp only [Pi.sub_apply]
  have : ((F p.1 - G p.1) - (F p.2 - G p.2)) / (Q p.1 - Q p.2) =
      -(((G p.1 - F p.1) - (G p.2 - F p.2)) / (Q p.1 - Q p.2)) := by ring
  rw [this, neg_sq]

/-- From core density at the response: an element `G` of the core with `𝒥(G) − 𝒥(F)` small. -/
theorem core_small (hL : 0 < L) (hκ : 0 < κ) {S : Set L2Unit} (hS : IsFormCore L κ Q S)
    {F : L2Unit} (hF : F ∈ formDomain Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ G ∈ S, G ∈ formDomain Q ∧
      (L / 2) * ‖G - F‖ ^ 2 + (κ / 2) * (formEnergy Q ((G - F : L2Unit) : ℝ → ℝ)).toReal < ε := by
  obtain ⟨hSd, hS2⟩ := hS
  obtain ⟨G, hG, hlt⟩ := hS2 F hF (2 * ε) (by positivity)
  refine ⟨G, hG, hSd hG, ?_⟩
  have hfin : formEnergy Q ((F - G : L2Unit) : ℝ → ℝ) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hκ), add_top] at hlt
    exact absurd hlt (not_lt.2 le_top)
  have h1 : ENNReal.ofReal (L * ‖F - G‖ ^ 2) + ENNReal.ofReal κ *
      formEnergy Q ((F - G : L2Unit) : ℝ → ℝ) =
      ENNReal.ofReal (L * ‖F - G‖ ^ 2 + κ * (formEnergy Q ((F - G : L2Unit) : ℝ → ℝ)).toReal) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hκ.le,
      ENNReal.ofReal_toReal hfin]
  rw [h1] at hlt
  have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
  rw [norm_sub_rev, formEnergy_swap_sub] at h2
  linarith

end QuantumNLS.IBridge

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.IBridge.J_sub_J
#print axioms QuantumNLS.IBridge.core_small
