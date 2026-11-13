import GRAdapter.FourierBridge
import ML027.Endpoint
import ML028.Endpoint
import ML046.Endpoint
import ML047.Endpoint
import ML048.Endpoint

/-!
GC03/GC04: actual Fourier majorants and native Poisson uniform convergence.

The integer and three-dimensional exponential-polynomial majorants are proved
from the isolated Mathlib endpoints. The resulting convergence statements use
the literal native cosine integral series and literal Fourier coefficients.

Joint real analyticity of the inverse is NOT inferred from uniform convergence.
The real-to-complex extension, common complex tube, contour estimate and
multivariable Taylor realization remain separate native construction targets.
There are no new axioms or hidden project-law inhabitants in this module.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

noncomputable section

def coordinateExpWeight (r : ℝ) (d : ℕ) (n : ℤ) : ℝ :=
  |(n : ℝ)| ^ d * Real.exp (-r * |(n : ℝ)|)

theorem coordinateExpWeight_nonneg (r : ℝ) (d : ℕ) (n : ℤ) :
    0 ≤ coordinateExpWeight r d n := by
  unfold coordinateExpWeight
  positivity

theorem summable_coordinateExpWeight (d : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (coordinateExpWeight r d) := by
  apply GRTemp.ML047.endpoint.mpr
  constructor
  · simpa only [coordinateExpWeight, Int.cast_natCast, Nat.abs_cast] using
      (GRTemp.ML046.endpoint d hr)
  · simpa only [coordinateExpWeight, Int.cast_neg, Int.cast_natCast, abs_neg,
      Nat.abs_cast] using (GRTemp.ML046.endpoint d hr)

def frequencyTriple (k : Frequency) : ℤ × (ℤ × ℤ) :=
  (k 0, (k 1, k 2))

theorem frequencyTriple_injective : Function.Injective frequencyTriple := by
  intro a b hab
  funext i
  fin_cases i
  · exact congrArg Prod.fst hab
  · exact congrArg (fun z : ℤ × (ℤ × ℤ) => z.2.1) hab
  · exact congrArg (fun z : ℤ × (ℤ × ℤ) => z.2.2) hab

def latticeExpMajorant (r : ℝ) (d : Fin 3 → ℕ) (k : Frequency) : ℝ :=
  coordinateExpWeight r (d 0) (k 0) *
    (coordinateExpWeight r (d 1) (k 1) * coordinateExpWeight r (d 2) (k 2))

theorem latticeExpMajorant_nonneg (r : ℝ) (d : Fin 3 → ℕ) (k : Frequency) :
    0 ≤ latticeExpMajorant r d k :=
  mul_nonneg (coordinateExpWeight_nonneg r (d 0) (k 0))
    (mul_nonneg (coordinateExpWeight_nonneg r (d 1) (k 1))
      (coordinateExpWeight_nonneg r (d 2) (k 2)))

theorem summable_latticeExpMajorant (d : Fin 3 → ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (latticeExpMajorant r d) := by
  have h12 := GRTemp.ML048.endpoint
    (summable_coordinateExpWeight (d 1) hr)
    (summable_coordinateExpWeight (d 2) hr)
    (coordinateExpWeight_nonneg r (d 1)) (coordinateExpWeight_nonneg r (d 2))
  have h012 := GRTemp.ML048.endpoint
    (summable_coordinateExpWeight (d 0) hr) h12
    (coordinateExpWeight_nonneg r (d 0))
    (fun z : ℤ × ℤ => mul_nonneg
      (coordinateExpWeight_nonneg r (d 1) z.1)
      (coordinateExpWeight_nonneg r (d 2) z.2))
  change Summable (fun k : Frequency =>
    coordinateExpWeight r (d 0) (k 0) *
      (coordinateExpWeight r (d 1) (k 1) * coordinateExpWeight r (d 2) (k 2)))
  convert! h012.comp_injective frequencyTriple_injective using 1

def frequencyL1 (k : Frequency) : ℝ :=
  |(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)|

def frequencyExpWeight (r : ℝ) (k : Frequency) : ℝ :=
  Real.exp (-r * frequencyL1 k)

theorem frequencyExpWeight_eq_lattice (r : ℝ) (k : Frequency) :
    frequencyExpWeight r k = latticeExpMajorant r (fun _ => 0) k := by
  have he : -r * frequencyL1 k =
      -r * |(k 0 : ℝ)| + (-r * |(k 1 : ℝ)| + -r * |(k 2 : ℝ)|) := by
    unfold frequencyL1
    ring
  rw [frequencyExpWeight, he, Real.exp_add, Real.exp_add]
  simp only [latticeExpMajorant, coordinateExpWeight, pow_zero, one_mul]

theorem summable_frequencyExpWeight {r : ℝ} (hr : 0 < r) :
    Summable (frequencyExpWeight r) := by
  exact (summable_latticeExpMajorant (fun _ => 0) hr).congr
    (fun k => (frequencyExpWeight_eq_lattice r k).symm)

theorem summable_scaled_frequencyExpWeight (C : ℝ) {r : ℝ} (hr : 0 < r) :
    Summable (fun k : Frequency => C * frequencyExpWeight r k) :=
  (summable_frequencyExpWeight hr).mul_left C

def complexPoissonMode (f : ScalarField) (k : Frequency) (x : Vec) : ℂ :=
  (poissonSymbol k : ℂ) *
    (LiteratureCharacter k x *
      LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k)

def realPoissonMode (f : ScalarField) (k : Frequency) (x : Vec) : ℝ :=
  poissonSymbol k * (∫ y in unitCube, cosineKernel k x y * f y)

theorem complexPoissonMode_norm_le (f : ScalarField) (k : Frequency) (x : Vec) :
    ‖complexPoissonMode f k x‖ ≤
      ‖LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k‖ := by
  have hm : ‖(poissonSymbol k : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using poissonSymbol_abs_le_one k
  rw [complexPoissonMode, norm_mul, norm_mul, literatureCharacter_norm, one_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm
    (norm_nonneg (LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k))

theorem realPoissonMode_eq_re (f : ScalarField) (hf : Continuous f)
    (k : Frequency) (x : Vec) :
    realPoissonMode f k x = (complexPoissonMode f k x).re := by
  rw [realPoissonMode, cosineKernel_integral_eq_re_fourier f hf]
  simp only [complexPoissonMode, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem realPoissonMode_norm_le (f : ScalarField) (hf : Continuous f)
    (k : Frequency) (x : Vec) :
    ‖realPoissonMode f k x‖ ≤
      ‖LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k‖ := by
  rw [realPoissonMode_eq_re f hf, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (complexPoissonMode_norm_le f k x)

theorem realPoissonMode_continuous (f : ScalarField) (hf : Continuous f)
    (k : Frequency) : Continuous (realPoissonMode f k) := by
  have heq : realPoissonMode f k = fun x => (complexPoissonMode f k x).re :=
    funext (realPoissonMode_eq_re f hf k)
  rw [heq]
  exact Complex.continuous_re.comp
    (continuous_const.mul ((literatureCharacter_continuous k).mul continuous_const))

theorem poissonInverse_uniform_of_summable_coefficients
    (f : ScalarField) (hf : Continuous f)
    (hs : Summable (fun k : Frequency =>
      ‖LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k‖)) :
    TendstoUniformly
      (fun s : Finset Frequency => fun x => ∑ k ∈ s, realPoissonMode f k x)
      (poissonInverse f) atTop := by
  apply tendstoUniformlyOn_univ.mp
  exact GRTemp.ML027.endpoint hs
    (fun k x _ => realPoissonMode_norm_le f hf k x)

theorem poissonInverse_continuous_of_summable_coefficients
    (f : ScalarField) (hf : Continuous f)
    (hs : Summable (fun k : Frequency =>
      ‖LiteratureFourierCoefficient (fun y : Vec => (f y : ℂ)) k‖)) :
    Continuous (poissonInverse f) := by
  apply continuousOn_univ.mp
  exact GRTemp.ML028.endpoint
    (fun k => (realPoissonMode_continuous f hf k).continuousOn) hs
    (fun k x _ => realPoissonMode_norm_le f hf k x)

theorem poissonInverse_uniform_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    TendstoUniformly
      (fun s : Finset Frequency => fun x => ∑ k ∈ s, realPoissonMode f k x)
      (poissonInverse f) atTop :=
  poissonInverse_uniform_of_summable_coefficients f hf.continuous
    (literatureFourierCoefficient_summable_norm L f hf hp)

theorem poissonInverse_continuous_of_literature
    (L : LiteratureSmoothFourierInput) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    Continuous (poissonInverse f) :=
  poissonInverse_continuous_of_summable_coefficients f hf.continuous
    (literatureFourierCoefficient_summable_norm L f hf hp)

/-- The uniform parameter majorant is an explicit coefficient estimate,
not an analytic-preservation law or a replacement Poisson operator. -/
theorem poissonInverse_parameter_uniform
    {T : Type*} (s : Set T) (f : T → ScalarField) (M : Frequency → ℝ)
    (hf : ∀ t ∈ s, Continuous (f t)) (hM : Summable M)
    (hb : ∀ t ∈ s, ∀ k : Frequency,
      ‖LiteratureFourierCoefficient (fun y : Vec => (f t y : ℂ)) k‖ ≤ M k) :
    TendstoUniformlyOn
      (fun p : Finset Frequency => fun z : T × Vec =>
        ∑ k ∈ p, realPoissonMode (f z.1) k z.2)
      (fun z : T × Vec => poissonInverse (f z.1) z.2) atTop (s ×ˢ univ) := by
  exact GRTemp.ML027.endpoint hM (fun k z hz =>
    (realPoissonMode_norm_le (f z.1) (hf z.1 hz.1) k z.2).trans
      (hb z.1 hz.1 k))

theorem realPoissonMode_parameter_continuousOn
    {T : Type*} [TopologicalSpace T] (s : Set T) (f : T → ScalarField)
    (hf : ∀ t ∈ s, Continuous (f t))
    (hc : ∀ k : Frequency, ContinuousOn
      (fun t => LiteratureFourierCoefficient (fun y : Vec => (f t y : ℂ)) k) s)
    (k : Frequency) :
    ContinuousOn (fun z : T × Vec => realPoissonMode (f z.1) k z.2) (s ×ˢ univ) := by
  have hcoeff : ContinuousOn
      (fun z : T × Vec =>
        LiteratureFourierCoefficient (fun y : Vec => (f z.1 y : ℂ)) k) (s ×ˢ univ) :=
    (hc k).comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hchar : ContinuousOn
      (fun z : T × Vec => LiteratureCharacter k z.2) (s ×ˢ univ) :=
    ((literatureCharacter_continuous k).comp continuous_snd).continuousOn
  have hcomplex : ContinuousOn
      (fun z : T × Vec => complexPoissonMode (f z.1) k z.2) (s ×ˢ univ) :=
    continuous_const.continuousOn.mul (hchar.mul hcoeff)
  apply (Complex.continuous_re.comp_continuousOn hcomplex).congr
  intro z hz
  exact realPoissonMode_eq_re (f z.1) (hf z.1 hz.1) k z.2

theorem poissonInverse_parameter_continuousOn
    {T : Type*} [TopologicalSpace T] (s : Set T) (f : T → ScalarField)
    (M : Frequency → ℝ) (hf : ∀ t ∈ s, Continuous (f t))
    (hc : ∀ k : Frequency, ContinuousOn
      (fun t => LiteratureFourierCoefficient (fun y : Vec => (f t y : ℂ)) k) s)
    (hM : Summable M)
    (hb : ∀ t ∈ s, ∀ k : Frequency,
      ‖LiteratureFourierCoefficient (fun y : Vec => (f t y : ℂ)) k‖ ≤ M k) :
    ContinuousOn (fun z : T × Vec => poissonInverse (f z.1) z.2) (s ×ˢ univ) := by
  exact GRTemp.ML028.endpoint
    (fun k => realPoissonMode_parameter_continuousOn s f hf hc k) hM
    (fun k z hz => (realPoissonMode_norm_le (f z.1) (hf z.1 hz.1) k z.2).trans
      (hb z.1 hz.1 k))

theorem poissonInverse_parameter_continuousOn_of_exponential_bound
    {T : Type*} [TopologicalSpace T] (s : Set T) (f : T → ScalarField)
    (C r : ℝ) (hr : 0 < r) (hf : ∀ t ∈ s, Continuous (f t))
    (hc : ∀ k : Frequency, ContinuousOn
      (fun t => LiteratureFourierCoefficient (fun y : Vec => (f t y : ℂ)) k) s)
    (hb : ∀ t ∈ s, ∀ k : Frequency,
      ‖LiteratureFourierCoefficient (fun y : Vec => (f t y : ℂ)) k‖ ≤
        C * frequencyExpWeight r k) :
    ContinuousOn (fun z : T × Vec => poissonInverse (f z.1) z.2) (s ×ˢ univ) :=
  poissonInverse_parameter_continuousOn s f
    (fun k => C * frequencyExpWeight r k) hf hc
    (summable_scaled_frequencyExpWeight C hr) hb

end
end NSEGR.Assembly
