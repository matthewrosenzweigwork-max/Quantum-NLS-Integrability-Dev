import NlsGge.Hierarchy.ALMonodromyAlgebra38
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

                                                                                                                                                                                                     
-- Route: shift lemma alPartial(b+n) = alPartial_{shift b}(n) * alPartial b; periodicity alPartial(L+m) = alPartial m * alPartial L
-- (alpha is a ZMod L field, so the shifted-by-L index is the identity); combine to M_beta P = P M, giving the conjugation
-- M_beta = P M P^{-1}; the trace is conjugation invariant. Determinants from det_alTransfer38, det_alPartial38, det_alMonodromy38.

namespace NlsGge.Atomic.AL001

open NlsGge.AblowitzLadik
open scoped Matrix

theorem hsucc_alPartial {L : ℕ} (δ : ZMod L → ℂ) (z : ℂ) (k : ℕ) :
    alPartial38 δ z (k + 1) = alTransfer38 (δ (k : ZMod L)) z * alPartial38 δ z k := rfl

theorem AL001_shift {L : ℕ} (γ : ZMod L → ℂ) (z : ℂ) (b : ℕ) (n : ℕ) :
    alPartial38 γ z (b + n) =
      alPartial38 (fun j => γ (j + (b : ZMod L))) z n * alPartial38 γ z b := by
  induction n with
  | zero => simp [alPartial38]
  | succ n ih =>
    rw [show b + (n + 1) = (b + n) + 1 from rfl, hsucc_alPartial, ih, hsucc_alPartial,
      Matrix.mul_assoc]
    have hcast : γ ((b + n : ℕ) : ZMod L) = (fun j => γ (j + (b : ZMod L))) (n : ZMod L) := by
      simp only [Nat.cast_add]
      rw [add_comm]
    rw [hcast]

theorem AL001_periodic {L : ℕ} (γ : ZMod L → ℂ) (z : ℂ) (m : ℕ) :
    alPartial38 γ z (L + m) = alPartial38 γ z m * alPartial38 γ z L := by
  rw [AL001_shift γ z L m]
  have hfun : (fun j => γ (j + ((L : ℕ) : ZMod L))) = γ := by
    funext j
    rw [ZMod.natCast_self, add_zero]
  rw [hfun]

theorem AL001 :
  ∀ (L : ℕ) [NeZero L] (α : ZMod L → ℂ), IsALField38 α → ∀ z : ℂ, z ≠ 0 →
    (∀ j : ZMod L, IsUnit (alTransfer38 (α j) z)) ∧
    (∀ j : ZMod L, (alTransfer38 (α j) z).det = 1) ∧
    (alMonodromy38 α z).det = 1 ∧
    (∀ k : ℕ, (alPartial38 α z k).det = 1) ∧
    (∀ m : ℕ, alMonodromy38 (fun j => α (j + (m : ZMod L))) z =
        alPartial38 α z m * alMonodromy38 α z * (alPartial38 α z m)⁻¹) ∧
    (∀ m : ℕ, Matrix.trace (alMonodromy38 (fun j => α (j + (m : ZMod L))) z) =
        Matrix.trace (alMonodromy38 α z)) := by
  intro L _ α hα z hz
  have hdetT : ∀ j : ZMod L, (alTransfer38 (α j) z).det = 1 :=
    fun j => det_alTransfer38 (α j) z (hα j) hz
  have hconj : ∀ m : ℕ, alMonodromy38 (fun j => α (j + (m : ZMod L))) z =
      alPartial38 α z m * alMonodromy38 α z * (alPartial38 α z m)⁻¹ := by
    intro m
    have hP : IsUnit (alPartial38 α z m).det := by
      rw [det_alPartial38 hα hz m]
      exact isUnit_one
    have h1 := AL001_shift α z m L
    have h2 := AL001_periodic α z m
    rw [add_comm L m] at h2
    have hcomm : alMonodromy38 (fun j => α (j + (m : ZMod L))) z * alPartial38 α z m =
        alPartial38 α z m * alMonodromy38 α z := by
      unfold alMonodromy38
      exact h1.symm.trans h2
    calc alMonodromy38 (fun j => α (j + (m : ZMod L))) z
        = alMonodromy38 (fun j => α (j + (m : ZMod L))) z *
            (alPartial38 α z m * (alPartial38 α z m)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
      _ = (alMonodromy38 (fun j => α (j + (m : ZMod L))) z * alPartial38 α z m) *
            (alPartial38 α z m)⁻¹ := by rw [Matrix.mul_assoc]
      _ = alPartial38 α z m * alMonodromy38 α z * (alPartial38 α z m)⁻¹ := by rw [hcomm]
  refine ⟨fun j => ?_, hdetT, det_alMonodromy38 hα hz, fun k => det_alPartial38 hα hz k, hconj, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, hdetT j]
    exact isUnit_one
  · intro m
    have hP : IsUnit (alPartial38 α z m).det := by
      rw [det_alPartial38 hα hz m]
      exact isUnit_one
    rw [hconj m, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP,
      Matrix.one_mul]


end NlsGge.Atomic.AL001
