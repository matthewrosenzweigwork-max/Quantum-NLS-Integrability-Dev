import Mathlib
import NlsGge.Birkhoff.W04WeightedSmoothing38b

/-!
# R-097: translation orbit Fourier coefficients and exact norm

Source head: Pro round 6 (commit c5547100), section 10G, R-097
`orbit_fourier_and_norm` (binding index entry R-097), including the restored
Banach-valued Fourier clause.

The proof is the synthesis route of the landed W04 files:
* `orbitCLM38 c s r σ hσ x` is the weighted coefficient vector `G` of the orbit
  (`W04WeightedSmoothing38b`, `orbitCLM38_apply`, `orbitMk38`);
* `Composition.fourierCoeff_synth`, `memAw_synth`, `awNorm_synth` give the Fourier,
  `A_w` and norm clauses for `f = synth (orbitWeight38 c s) G`;
* `coeff_orbitMk38` identifies the `n`-th coefficient with `hSingle38`;
* `norm_orbitMk38` is the exact norm identity `‖G‖ = ‖x‖`;
* `synth_orbitMk38` is the orbit identity (W04.02).
No analytic hypothesis is added.
-/

set_option autoImplicit false

open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Composition

namespace NlsGge.ThirdConsultation.R

theorem orbit_fourier_and_norm
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (s r σ : ℝ) (hσ : s + 1 - r = σ)
    (x : ECarrier38 c σ) :
    let G := orbitCLM38 c s r σ hσ x
    let f := synth (orbitWeight38 c s) G
    MemAw (orbitWeight38 c s) f ∧
    (∀ n : ℤ,
      fourierCoeff f n = hSingle38 r n (eCoe38 c σ x n)) ∧
    awNorm (orbitWeight38 c s) f = ‖x‖ ∧
    ‖G‖ = ‖x‖ ∧
    (∀ t : ℝ,
      f (t : AddCircle (1 : ℝ)) =
        hMk38 r (rotSeq38 (2 * Real.pi * t) (eCoe38 c σ x))
          (rotSeq38_mem r _
            (seqE38_subset_seqSobolev38 c σ r
              (eCoe38_mem c σ x)))) := by
  intro G f
  have hw : AdmissibleWeight (orbitWeight38 c s) := orbitWeight38_admissible c s
  have hG : G = orbitMk38 c s r σ hσ (eCoe38 c σ x) (eCoe38_mem c σ x) := rfl
  refine ⟨memAw_synth hw G, ?_, ?_, ?_, ?_⟩
  · intro n
    show fourierCoeff (synth (orbitWeight38 c s) G) n = _
    rw [fourierCoeff_synth hw G n, hG, coeff_orbitMk38]
  · show awNorm (orbitWeight38 c s) (synth (orbitWeight38 c s) G) = ‖x‖
    rw [awNorm_synth hw G, hG]
    exact norm_orbitMk38 c s r σ hσ x
  · rw [hG]
    exact norm_orbitMk38 c s r σ hσ x
  · intro t
    exact synth_orbitMk38 c s r σ hσ (eCoe38 c σ x) (eCoe38_mem c σ x) t

end NlsGge.ThirdConsultation.R
