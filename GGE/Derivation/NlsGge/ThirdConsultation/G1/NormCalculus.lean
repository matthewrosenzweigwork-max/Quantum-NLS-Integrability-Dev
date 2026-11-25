import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.NLS38.ClassicalSolution38a

/- G1PB (proof development, AUTHOR; not reviewed). Supporting module for G1-034: Sobolev norm calculus on PhysicalL2
   (add/neg/finite sum/derivative/monotone/product), all via `physicalSobolevNorm (m:ℝ)` = `hn m (fourierSeq38 u)`.
   Target NlsGge/ThirdConsultation/G1/NormCalculus.lean. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem physicalSobolev_iff_mem (m : ℕ) (u : PhysicalL2) :
    physicalSobolev (m : ℝ) u ↔ fourierSeq38 u ∈ seqSobolev38 (m : ℝ) :=
  (mem_seqSobolev38_iff _ _).symm

theorem fS_add (u v : PhysicalL2) : fourierSeq38 (u + v) = fourierSeq38 u + fourierSeq38 v := by
  funext n; unfold fourierSeq38; simp

theorem fS_neg (u : PhysicalL2) : fourierSeq38 (-u) = -fourierSeq38 u := by
  funext n; unfold fourierSeq38; simp

theorem fS_zero : fourierSeq38 (0 : PhysicalL2) = 0 := by
  funext n; unfold fourierSeq38; simp

theorem hn_neg' (m : ℕ) (x : ℤ → ℂ) : hn m (-x) = hn m x := by
  unfold hn; simp

theorem hn_zero' (m : ℕ) : hn m (0 : ℤ → ℂ) = 0 := by
  unfold hn; simp

theorem seq_add_mem {r : ℝ} {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 r) (hy : y ∈ seqSobolev38 r) :
    x + y ∈ seqSobolev38 r :=
  (weightedSubmodule (sobolevModeWeight r)).add_mem hx hy

theorem seq_neg_mem {r : ℝ} {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 r) : -x ∈ seqSobolev38 r :=
  (weightedSubmodule (sobolevModeWeight r)).neg_mem hx

theorem hn_add' (m : ℕ) {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ)) (hy : y ∈ seqSobolev38 (m : ℝ)) :
    hn m (x + y) ≤ hn m x + hn m y := by
  have e : x + y = carrierCoe38 (m : ℝ) (carrierMk38 (m : ℝ) x hx + carrierMk38 (m : ℝ) y hy) := rfl
  rw [e, hn_coe38]
  have h1 := hn_coe38 m (carrierMk38 (m : ℝ) x hx)
  have h2 := hn_coe38 m (carrierMk38 (m : ℝ) y hy)
  rw [carrierCoe38_mk] at h1 h2
  rw [h1, h2]
  exact norm_add_le _ _

theorem psn_add (m : ℕ) {u v : PhysicalL2} (hu : physicalSobolev (m : ℝ) u) (hv : physicalSobolev (m : ℝ) v) :
    physicalSobolev (m : ℝ) (u + v) ∧
      physicalSobolevNorm (m : ℝ) (u + v) ≤ physicalSobolevNorm (m : ℝ) u + physicalSobolevNorm (m : ℝ) v := by
  rw [physicalSobolev_iff_mem] at hu hv ⊢
  rw [psn_eq_hn, psn_eq_hn, psn_eq_hn, fS_add]
  exact ⟨seq_add_mem hu hv, hn_add' m hu hv⟩

theorem psn_neg (m : ℕ) {u : PhysicalL2} (hu : physicalSobolev (m : ℝ) u) :
    physicalSobolev (m : ℝ) (-u) ∧ physicalSobolevNorm (m : ℝ) (-u) = physicalSobolevNorm (m : ℝ) u := by
  rw [physicalSobolev_iff_mem] at hu ⊢
  rw [psn_eq_hn, psn_eq_hn, fS_neg]
  exact ⟨seq_neg_mem hu, hn_neg' m _⟩

theorem psn_nonneg (m : ℕ) (u : PhysicalL2) : 0 ≤ physicalSobolevNorm (m : ℝ) u := by
  rw [psn_eq_hn]; exact Real.sqrt_nonneg _

theorem psn_sum (m : ℕ) {ι : Type*} (s : Finset ι) (f : ι → PhysicalL2)
    (hf : ∀ i ∈ s, physicalSobolev (m : ℝ) (f i)) :
    physicalSobolev (m : ℝ) (∑ i ∈ s, f i) ∧
      physicalSobolevNorm (m : ℝ) (∑ i ∈ s, f i) ≤ ∑ i ∈ s, physicalSobolevNorm (m : ℝ) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨?_, ?_⟩
    · rw [physicalSobolev_iff_mem, fS_zero]; exact (weightedSubmodule (sobolevModeWeight (m : ℝ))).zero_mem
    · rw [psn_eq_hn, fS_zero, hn_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨h1, h2⟩ := psn_add m (hf a (Finset.mem_insert_self a s)) ih'.1
    exact ⟨h1, h2.trans (add_le_add le_rfl ih'.2)⟩

theorem psn_mono {m m' : ℕ} (h : m ≤ m') {u : PhysicalL2} (hu : physicalSobolev (m' : ℝ) u) :
    physicalSobolev (m : ℝ) u ∧ physicalSobolevNorm (m : ℝ) u ≤ physicalSobolevNorm (m' : ℝ) u := by
  rw [physicalSobolev_iff_mem] at hu ⊢
  rw [psn_eq_hn, psn_eq_hn]
  exact ⟨seqSobolev38_mono (by exact_mod_cast h) hu, hn_mono38 h hu⟩

theorem fS_weakDerivative (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    fourierSeq38 (weakDerivative u) = -dx (fourierSeq38 u) := by
  have hd := weakDerivative_domain_of_H1 u hu
  funext n
  have := weakDerivative_coeff u hd n
  change reflectedFourierL2 (weakDerivative u) n = _
  rw [this]
  simp only [Pi.neg_apply, dx]
  change _ * fourierSeq38 u n = _
  ring

theorem psn_deriv (m : ℕ) {u : PhysicalL2} (hu : physicalSobolev ((m + 1 : ℕ) : ℝ) u) :
    physicalSobolev (m : ℝ) (weakDerivative u) ∧
      physicalSobolevNorm (m : ℝ) (weakDerivative u) ≤ 2 * Real.pi * physicalSobolevNorm ((m + 1 : ℕ) : ℝ) u := by
  have hu1 : physicalSobolev ((1 : ℕ) : ℝ) u := (psn_mono (Nat.le_add_left 1 m) hu).1
  have hu1' : physicalSobolev 1 u := by simpa using hu1
  rw [physicalSobolev_iff_mem] at hu ⊢
  rw [psn_eq_hn, psn_eq_hn, fS_weakDerivative u hu1']
  exact ⟨seq_neg_mem (dx_mem m hu), by rw [hn_neg']; exact hn_dx_le m hu⟩

theorem psn_prod (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : PhysicalL2, physicalSobolev (m : ℝ) u → physicalSobolev (m : ℝ) v →
      physicalSobolev (m : ℝ) (physicalProduct u v) ∧
      physicalSobolevNorm (m : ℝ) (physicalProduct u v) ≤
        C * physicalSobolevNorm (m : ℝ) u * physicalSobolevNorm (m : ℝ) v := by
  obtain ⟨C, hC, h⟩ := NlsGge.Atomic.LIB087.sobolev_mul_norm_le m hm
  refine ⟨C, hC, fun u v hu hv => ?_⟩
  have hu' := (physicalSobolev_iff_ordinary _ u).1 hu
  have hv' := (physicalSobolev_iff_ordinary _ v).1 hv
  obtain ⟨hu1, hp, hb⟩ := h u v hu' hv'
  rw [physicalProduct_eq_h1MulL2 u v hu1]
  refine ⟨(physicalSobolev_iff_ordinary _ _).2 hp, ?_⟩
  rw [psn_eq_L2 m _ hp, psn_eq_L2 m u hu', psn_eq_L2 m v hv']
  exact hb

end NlsGge.GKDefinitionDesign
end
