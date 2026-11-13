import SingularClosure.SixChannels
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Six orthogonal channels on the actual torus L² space

The Fourier Hilbert basis is Mathlib's concrete exponential basis on the
normalized unit three-torus. Masks are transported through its isometric
equivalence; they are not projections on an unspecified abstract Hilbert space.
This gives the infinite physical L² decomposition. Identification with the
smooth periodic lift operators and their classical derivatives is not assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory
open scoped BigOperators ENNReal lp

namespace SingularClosure

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev TorusScalarL2 :=
  MeasureTheory.Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))

abbrev TorusVectorL2 := PiLp 2 (fun _ : Fin 3 => TorusScalarL2)

abbrev FourierSequenceL2 := lp (fun _ : Frequency => ℂ) 2

/-- A channel/component mask preserves square summability by pointwise domination. -/
def l2SequenceChannel (A : Fin 6) (i : Fin 3)
    (a : FourierSequenceL2) : FourierSequenceL2 :=
  ⟨fun k => if channelOf k i = A then a k else 0,
    (lp.memℓp a).mono' (by
      intro k
      by_cases h : channelOf k i = A <;> simp [h])⟩

@[simp]
theorem l2SequenceChannel_apply (A : Fin 6) (i : Fin 3)
    (a : FourierSequenceL2) (k : Frequency) :
    l2SequenceChannel A i a k = if channelOf k i = A then a k else 0 := rfl

theorem l2SequenceChannel_sum (i : Fin 3) (a : FourierSequenceL2) :
    (∑ A : Fin 6, l2SequenceChannel A i a) = a := by
  apply lp.ext
  funext k
  change (∑ A : Fin 6, l2SequenceChannel A i a) k = a k
  simp only [lp.coeFn_sum, Finset.sum_apply, l2SequenceChannel_apply]
  simp [eq_comm]

theorem l2SequenceChannel_idempotent (A : Fin 6) (i : Fin 3)
    (a : FourierSequenceL2) :
    l2SequenceChannel A i (l2SequenceChannel A i a) = l2SequenceChannel A i a := by
  apply lp.ext
  funext k
  by_cases h : channelOf k i = A <;> simp [h]

theorem l2SequenceChannel_add (A : Fin 6) (i : Fin 3)
    (a b : FourierSequenceL2) :
    l2SequenceChannel A i (a + b) = l2SequenceChannel A i a + l2SequenceChannel A i b := by
  apply lp.ext
  funext k
  by_cases h : channelOf k i = A <;> simp [h]

theorem l2SequenceChannel_smul (A : Fin 6) (i : Fin 3)
    (z : ℂ) (a : FourierSequenceL2) :
    l2SequenceChannel A i (z • a) = z • l2SequenceChannel A i a := by
  apply lp.ext
  funext k
  by_cases h : channelOf k i = A <;> simp [h]

theorem l2SequenceChannel_norm_le (A : Fin 6) (i : Fin 3)
    (a : FourierSequenceL2) : ‖l2SequenceChannel A i a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (by norm_num)
  intro k
  by_cases h : channelOf k i = A <;> simp [h]

theorem l2SequenceChannel_disjoint (A B : Fin 6) (hAB : A ≠ B) (i : Fin 3)
    (a : FourierSequenceL2) :
    l2SequenceChannel A i (l2SequenceChannel B i a) = 0 := by
  apply lp.ext
  funext k
  by_cases hA : channelOf k i = A
  · have hB : channelOf k i ≠ B := fun h => hAB (hA.symm.trans h)
    simp [hA, hB, hAB]
  · simp [hA]

theorem l2SequenceChannel_selfAdjoint (A : Fin 6) (i : Fin 3)
    (a b : FourierSequenceL2) :
    inner ℂ (l2SequenceChannel A i a) b =
      inner ℂ a (l2SequenceChannel A i b) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  by_cases h : channelOf k i = A <;> simp [h]

theorem l2SequenceChannel_orthogonal (A B : Fin 6) (hAB : A ≠ B) (i : Fin 3)
    (a b : FourierSequenceL2) :
    inner ℂ (l2SequenceChannel A i a) (l2SequenceChannel B i b) = 0 := by
  rw [l2SequenceChannel_selfAdjoint, l2SequenceChannel_disjoint A B hAB]
  exact inner_zero_right _

/-- Componentwise physical L² projection, via the actual Fourier basis. -/
def scalarL2Channel (A : Fin 6) (i : Fin 3) (f : TorusScalarL2) : TorusScalarL2 :=
  UnitAddTorus.mFourierBasis.repr.symm
    (l2SequenceChannel A i (UnitAddTorus.mFourierBasis.repr f))

@[simp]
theorem scalarL2Channel_repr (A : Fin 6) (i : Fin 3) (f : TorusScalarL2) :
    UnitAddTorus.mFourierBasis.repr (scalarL2Channel A i f) =
      l2SequenceChannel A i (UnitAddTorus.mFourierBasis.repr f) := by
  exact UnitAddTorus.mFourierBasis.repr.apply_symm_apply _

theorem scalarL2Channel_sum (i : Fin 3) (f : TorusScalarL2) :
    (∑ A : Fin 6, scalarL2Channel A i f) = f := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  simp only [map_sum, scalarL2Channel_repr, l2SequenceChannel_sum]

theorem scalarL2Channel_idempotent (A : Fin 6) (i : Fin 3) (f : TorusScalarL2) :
    scalarL2Channel A i (scalarL2Channel A i f) = scalarL2Channel A i f := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  simp only [scalarL2Channel_repr, l2SequenceChannel_idempotent]

theorem scalarL2Channel_add (A : Fin 6) (i : Fin 3) (f g : TorusScalarL2) :
    scalarL2Channel A i (f + g) = scalarL2Channel A i f + scalarL2Channel A i g := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  simp only [map_add, scalarL2Channel_repr, l2SequenceChannel_add]

theorem scalarL2Channel_smul (A : Fin 6) (i : Fin 3) (z : ℂ) (f : TorusScalarL2) :
    scalarL2Channel A i (z • f) = z • scalarL2Channel A i f := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  simp only [map_smul, scalarL2Channel_repr, l2SequenceChannel_smul]

theorem scalarL2Channel_norm_le (A : Fin 6) (i : Fin 3) (f : TorusScalarL2) :
    ‖scalarL2Channel A i f‖ ≤ ‖f‖ := by
  calc
    ‖scalarL2Channel A i f‖ =
        ‖l2SequenceChannel A i (UnitAddTorus.mFourierBasis.repr f)‖ := by
      exact UnitAddTorus.mFourierBasis.repr.symm.norm_map _
    _ ≤ ‖UnitAddTorus.mFourierBasis.repr f‖ := l2SequenceChannel_norm_le A i _
    _ = ‖f‖ := UnitAddTorus.mFourierBasis.repr.norm_map f

theorem scalarL2Channel_disjoint (A B : Fin 6) (hAB : A ≠ B) (i : Fin 3)
    (f : TorusScalarL2) : scalarL2Channel A i (scalarL2Channel B i f) = 0 := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  simp only [scalarL2Channel_repr, l2SequenceChannel_disjoint A B hAB, map_zero]

theorem scalarL2Channel_selfAdjoint (A : Fin 6) (i : Fin 3)
    (f g : TorusScalarL2) :
    inner ℂ (scalarL2Channel A i f) g = inner ℂ f (scalarL2Channel A i g) := by
  rw [← UnitAddTorus.mFourierBasis.repr.inner_map_map (scalarL2Channel A i f) g,
    ← UnitAddTorus.mFourierBasis.repr.inner_map_map f (scalarL2Channel A i g)]
  simp only [scalarL2Channel_repr]
  exact l2SequenceChannel_selfAdjoint A i _ _

theorem scalarL2Channel_orthogonal (A B : Fin 6) (hAB : A ≠ B) (i : Fin 3)
    (f g : TorusScalarL2) :
    inner ℂ (scalarL2Channel A i f) (scalarL2Channel B i g) = 0 := by
  rw [scalarL2Channel_selfAdjoint, scalarL2Channel_disjoint A B hAB]
  exact inner_zero_right _

/-- The six actual physical vector L² projectors. -/
def torusL2Channel (A : Fin 6) (u : TorusVectorL2) : TorusVectorL2 :=
  WithLp.toLp 2 (fun i => scalarL2Channel A i (u i))

@[simp]
theorem torusL2Channel_apply (A : Fin 6) (u : TorusVectorL2) (i : Fin 3) :
    torusL2Channel A u i = scalarL2Channel A i (u i) := rfl

theorem torusVectorL2_sum_apply {ι : Type*} (s : Finset ι)
    (u : ι → TorusVectorL2) (i : Fin 3) :
    (∑ A ∈ s, u A) i = ∑ A ∈ s, u A i :=
  map_sum (PiLp.projₗ 2 (fun _ : Fin 3 => TorusScalarL2) (𝕜 := ℂ) i) u s

theorem TORUS_L2_SIX_CHANNEL_RECONSTRUCTION (u : TorusVectorL2) :
    (∑ A : Fin 6, torusL2Channel A u) = u := by
  apply PiLp.ext
  intro i
  rw [torusVectorL2_sum_apply]
  exact scalarL2Channel_sum i (u i)

theorem torusL2Channel_idempotent (A : Fin 6) (u : TorusVectorL2) :
    torusL2Channel A (torusL2Channel A u) = torusL2Channel A u := by
  apply PiLp.ext
  intro i
  exact scalarL2Channel_idempotent A i (u i)

theorem torusL2Channel_disjoint (A B : Fin 6) (hAB : A ≠ B) (u : TorusVectorL2) :
    torusL2Channel A (torusL2Channel B u) = 0 := by
  apply PiLp.ext
  intro i
  exact scalarL2Channel_disjoint A B hAB i (u i)

theorem torusL2Channel_selfAdjoint (A : Fin 6) (u v : TorusVectorL2) :
    inner ℂ (torusL2Channel A u) v = inner ℂ u (torusL2Channel A v) := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact scalarL2Channel_selfAdjoint A i (u i) (v i)

theorem TORUS_L2_SIX_CHANNEL_ORTHOGONAL (A B : Fin 6) (hAB : A ≠ B)
    (u v : TorusVectorL2) : inner ℂ (torusL2Channel A u) (torusL2Channel B v) = 0 := by
  rw [torusL2Channel_selfAdjoint, torusL2Channel_disjoint A B hAB]
  exact inner_zero_right _

theorem TORUS_L2_SIX_CHANNEL_PYTHAGORAS (u : TorusVectorL2) :
    ‖u‖ ^ 2 = ∑ A : Fin 6, ‖torusL2Channel A u‖ ^ 2 := by
  have h : inner ℂ u u =
      ∑ A : Fin 6, inner ℂ (torusL2Channel A u) (torusL2Channel A u) := by
    calc
      inner ℂ u u = inner ℂ (∑ A : Fin 6, torusL2Channel A u)
          (∑ B : Fin 6, torusL2Channel B u) := by
        simp only [TORUS_L2_SIX_CHANNEL_RECONSTRUCTION]
      _ = ∑ A : Fin 6, ∑ B : Fin 6,
          inner ℂ (torusL2Channel A u) (torusL2Channel B u) := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro A _
        rw [inner_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_eq_single A
        · intro B _ hBA
          exact TORUS_L2_SIX_CHANNEL_ORTHOGONAL A B hBA.symm u u
        · simp
  have hr := congrArg Complex.re h
  have hs (v : TorusVectorL2) : (inner ℂ v v).re = ‖v‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) v
  simpa only [Complex.re_sum, hs] using hr

/-- Actual L² Fourier coefficients, in the coefficient convention of SixChannels. -/
def torusVectorFourierCoeff (u : TorusVectorL2) : FourierCoeff :=
  fun k i => UnitAddTorus.mFourierCoeff (u i) k

theorem torusL2Channel_fourierCoeff (A : Fin 6) (u : TorusVectorL2) :
    torusVectorFourierCoeff (torusL2Channel A u) =
      spectralChannel A (torusVectorFourierCoeff u) := by
  funext k i
  simp only [torusVectorFourierCoeff, torusL2Channel_apply,
    ← UnitAddTorus.mFourierBasis_repr, scalarL2Channel_repr,
    l2SequenceChannel_apply, spectralChannel]

theorem torusL2Channel_preserves_fourierSolenoidal (A : Fin 6) (u : TorusVectorL2)
    (hu : SpectralSolenoidal (torusVectorFourierCoeff u)) :
    SpectralSolenoidal (torusVectorFourierCoeff (torusL2Channel A u)) := by
  rw [torusL2Channel_fourierCoeff]
  exact spectralChannel_preserves_solenoidal A hu

theorem torusL2Channel_preserves_fourierMeanZero (A : Fin 6) (u : TorusVectorL2)
    (hu : SpectralMeanZero (torusVectorFourierCoeff u)) :
    SpectralMeanZero (torusVectorFourierCoeff (torusL2Channel A u)) := by
  rw [torusL2Channel_fourierCoeff]
  exact spectralChannel_preserves_meanZero A hu

theorem torusVectorFourierCoeff_zero (u : TorusVectorL2) (i : Fin 3) :
    torusVectorFourierCoeff u 0 i = ∫ x, u i x := by
  simp [torusVectorFourierCoeff, UnitAddTorus.mFourierCoeff,
    UnitAddTorus.mFourier_zero]

/-- Preservation of the literal physical mean on the probability torus. -/
theorem torusL2Channel_preserves_mean (A : Fin 6) (u : TorusVectorL2)
    (hu : ∀ i : Fin 3, (∫ x, u i x) = 0) :
    ∀ i : Fin 3, (∫ x, torusL2Channel A u i x) = 0 := by
  have hspec : SpectralMeanZero (torusVectorFourierCoeff u) := by
    intro i
    rw [torusVectorFourierCoeff_zero]
    exact hu i
  intro i
  rw [← torusVectorFourierCoeff_zero (torusL2Channel A u) i]
  exact torusL2Channel_preserves_fourierMeanZero A u hspec i

theorem torusVectorFourierCoeff_injective : Function.Injective torusVectorFourierCoeff := by
  intro u v huv
  apply PiLp.ext
  intro i
  apply UnitAddTorus.mFourierBasis.repr.injective
  apply lp.ext
  funext k
  simpa only [UnitAddTorus.mFourierBasis_repr, torusVectorFourierCoeff] using
    congrArg (fun c : FourierCoeff => c k i) huv

end

end SingularClosure
