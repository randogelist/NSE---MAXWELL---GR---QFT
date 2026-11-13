import GRAssembly.NativeFourierTorus
import GRAssembly.NativeFourierDecay

/-!
Exact all-dimensional smooth Fourier literature input, assembled from actual
coordinate derivatives, physical unit-cube coefficients, and native torus
reconstruction. No literature premise occurs in this final constructor.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.NativeLiterature

open scoped ContDiff

noncomputable section

theorem fourier_partialWord_hasSumUniformly {n : ℕ} {f : LiteratureSpace n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : LiteraturePeriodic f) (w : List (Fin n)) :
    HasSumUniformly
      (fun (k : LiteratureFrequency n) (x : LiteratureSpace n) =>
        (LiteratureFourierWordMultiplier w k * LiteratureFourierCoefficient f k) *
          LiteratureCharacter k x)
      (LiteraturePartialWord w f) := by
  have hwf := partialWord_contDiff hf w
  have hwp := partialWord_periodic hp w
  have hs := summable_norm_fourierCoefficient hwf hwp
  have h := literatureFourier_hasSumUniformly_of_summable_norm
    (LiteraturePartialWord w f) hwf.continuous hwp hs
  simpa only [fourierCoefficient_partialWord hf hp w] using h

theorem literatureSmoothFourierInput_native : LiteratureSmoothFourierInput := by
  refine ⟨?_⟩
  intro n hn f hf hp w
  exact ⟨fourierCoefficient_partialWord hf hp w,
    summable_norm_fourierCoefficient_partialWord hf hp w,
    fourier_partialWord_hasSumUniformly hf hp w⟩

end

end NSEGR.NativeLiterature
