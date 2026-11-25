import Mathlib
import NlsGge.ThirdConsultation.F.Basic
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Hierarchy.F03Spectral38
import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38

/- F-003 PRODUCTION01 (proof development, AUTHOR; target NlsGge/Atomic/F/F003.lean, namespace NlsGge.ThirdConsultation.F). Head verbatim from STATEMENTS/F.md F-003.
   Proof: continuity/agreement/uniqueness from continuous_localRemainderSobolev38, localRemainderSobolev38_smooth_spectral, localRemainderSobolev38_unique_spectral;
   polynomial clause: closure of 'sum of diagonals of degree <= d' (Pd) under add/smul/sum, with localRemainderMonomialValue38_polynomial and localRemainderSobolev38_bound. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.Birkhoff
open scoped ContDiff

namespace NlsGge.ThirdConsultation.F
noncomputable section
namespace F003Aux

def Pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) (V : E → ℝ) : Prop :=
  ∃ A : (k : Fin (d + 1)) → ContinuousMultilinearMap ℝ (fun _ : Fin k.val => E) ℝ,
    ∀ y, V y = ∑ k : Fin (d + 1), A k (fun _ => y)

theorem Pd_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) :
    Pd d (fun _ : E => (0 : ℝ)) :=
  ⟨fun _ => 0, fun y => by simp⟩

theorem Pd_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) (V W : E → ℝ)
    (hV : Pd d V) (hW : Pd d W) : Pd d (fun y => V y + W y) := by
  obtain ⟨A, hA⟩ := hV
  obtain ⟨B, hB⟩ := hW
  exact ⟨fun k => A k + B k, fun y => by simp [hA y, hB y, Finset.sum_add_distrib]⟩

theorem Pd_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) (c : ℝ)
    (V : E → ℝ) (hV : Pd d V) : Pd d (fun y => c * V y) := by
  obtain ⟨A, hA⟩ := hV
  exact ⟨fun k => c • A k, fun y => by simp [hA y, Finset.mul_sum]⟩

theorem Pd_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} (d : ℕ)
    (s : Finset ι) (f : ι → E → ℝ) (h : ∀ i ∈ s, Pd d (f i)) :
    Pd d (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Pd_zero d
  | insert a s ha ih =>
    have := Pd_add d (f a) (fun y => ∑ i ∈ s, f i y) (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

theorem Pd_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d n : ℕ) (hn : n ≤ d)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) :
    Pd d (fun y => L (fun _ => y)) := by
  refine ⟨fun k => if h : n = k.val then cast (by rw [h]) L else 0, fun y => ?_⟩
  rw [Finset.sum_eq_single ⟨n, Nat.lt_succ_of_le hn⟩]
  · simp
  · intro k _ hk
    have : n ≠ k.val := fun h => hk (Fin.ext h.symm)
    simp [this]
  · simp

end F003Aux

open F003Aux in
theorem f003 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    Continuous (Vm38 m β) ∧ agreesLocalRemainder m β (Vm38 m β) ∧
    (∃ d : ℕ, d ≤ 2 * m + 2 ∧
      ∃ A : (k : Fin (d + 1)) → ContinuousMultilinearMap ℝ
          (fun _ : Fin k.val => SobolevHilbert ((m - 1 : ℕ) : ℝ)) ℝ,
        (∀ y, Vm38 m β y = ∑ k : Fin (d + 1), A k (fun _ => y)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |Vm38 m β y| ≤ C * (1 + ‖y‖ ^ d)) ∧
    (∀ V : SobolevHilbert ((m - 1 : ℕ) : ℝ) → ℝ,
      Continuous V → agreesLocalRemainder m β V → V = Vm38 m β) := by
  refine ⟨(continuous_localRemainderSobolev38 m β).comp (continuous_toCarrier38 _),
    fun U hU hper y hy => localRemainderSobolev38_smooth_spectral m hm β U hU hper y hy,
    ?_, ?_⟩
  · have hPd : Pd (2 * m + 2) (Vm38 m β) := by
      have hmono : ∀ j q, Pd (2 * m + 2)
          (fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) =>
            localRemainderMonomialValue38 m j q (toCarrier38 _ y)) := by
        intro j q
        obtain ⟨n, hn, L, hL⟩ := localRemainderMonomialValue38_polynomial m j q
        have h := Pd_diag (E := SobolevHilbert ((m - 1 : ℕ) : ℝ)) (2 * m + 2) n hn L
        have e : (fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) =>
            localRemainderMonomialValue38 m j q (toCarrier38 _ y)) =
            fun y => L (fun _ => y) := funext fun y => hL (toCarrier38 _ y)
        rw [e]; exact h
      have := Pd_sum (E := SobolevHilbert ((m - 1 : ℕ) : ℝ)) (2 * m + 2) (Finset.range (m + 1))
        (fun j y => β j * ∑ q ∈ (normalizedRemainder38 j).support,
          localRemainderMonomialValue38 m j q (toCarrier38 _ y))
        (fun j _ => Pd_smul _ _ _ (Pd_sum _ _ _ (fun q _ => hmono j q)))
      exact this
    obtain ⟨A, hA⟩ := hPd
    obtain ⟨C, hC0, hC⟩ := localRemainderSobolev38_bound m β
    exact ⟨2 * m + 2, le_rfl, A, hA, C, hC0, fun y => by
      have := hC (toCarrier38 _ y)
      rwa [norm_toCarrier38] at this⟩
  · intro V hV hag
    funext y
    exact localRemainderSobolev38_unique_spectral m hm β V hV
      (fun U hU hper x hx => (hag U hU hper x hx).2) y

end
end NlsGge.ThirdConsultation.F
