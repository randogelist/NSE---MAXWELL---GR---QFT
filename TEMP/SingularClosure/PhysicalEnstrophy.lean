import SingularClosure.Admission
import SingularClosure.PhysicalChannels

/-!
# Actual physical gradient energies

This module proves finiteness of the physical nonnegative gradient integral for
every smooth field on the fundamental cube, and physical Pythagoras for the
horizontal/vertical channel pairs.  These are integral statements about the
actual derivatives from `Contracts.lean`, rather than spectral substitutes.

Frequency-separated channel orthogonality remains a separate obligation.
Consequently these auxiliary results do not claim the complete frozen
`SIX_CHANNEL_ENSTROPHY_EQ` endpoint.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

theorem isCompact_unitCube : IsCompact unitCube := by
  have hc : IsCompact (Set.univ.pi (fun _ : Fin 3 => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hi := hc.image (PiLp.continuous_toLp (p := (2 : ENNReal))
    (β := fun _ : Fin 3 => ℝ))
  convert hi using 1
  ext x
  constructor
  · intro hx
    refine ⟨WithLp.ofLp x, ?_, ?_⟩
    · change ∀ i : Fin 3, i ∈ Set.univ →
        0 ≤ WithLp.ofLp x i ∧ WithLp.ofLp x i ≤ 1
      intro i _
      exact hx i
    · simp
  · rintro ⟨y, hy, rfl⟩
    intro i
    exact hy i (Set.mem_univ i)

theorem coordinateDerivative_continuous {v : Field}
    (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    Continuous (coordinateDerivative v i) := by
  exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const

theorem gradientSquareDensity_continuous {v : Field}
    (hv : ContDiff ℝ ∞ v) : Continuous (gradientSquareDensity v) := by
  unfold gradientSquareDensity
  exact continuous_finsetSum _ (fun i _ =>
    continuous_finsetSum _ (fun j _ =>
      ((((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).continuous).comp
        (coordinateDerivative_continuous hv i)).pow 2)))

theorem gradientSquareDensity_integrableOn {v : Field}
    (hv : ContDiff ℝ ∞ v) :
    IntegrableOn (gradientSquareDensity v) unitCube volume :=
  (gradientSquareDensity_continuous hv).continuousOn.integrableOn_compact
    isCompact_unitCube

/-- Finiteness is proved for the actual nonnegative integral, not obtained by
totalizing a divergent real integral. -/
theorem physicalEnstrophy_lt_top {v : Field} (hv : ContDiff ℝ ∞ v) :
    physicalEnstrophy v < ⊤ := by
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (gradientSquareDensity_nonneg v))).mp
      (gradientSquareDensity_integrableOn hv).hasFiniteIntegral

theorem physicalChannel_enstrophy_lt_top (N : ℕ) (A : Fin 6)
    (a : FourierCoeff) : physicalEnstrophy (physicalChannel N A a) < ⊤ :=
  physicalEnstrophy_lt_top (physicalChannel_contDiff N A a)

/-- Identically zero physical components have identically zero directional
derivatives, with differentiability of the vector field stated explicitly. -/
theorem coordinateDerivative_component_zero {v : Field}
    (hv : Differentiable ℝ v) (j : Fin 3) (hz : ∀ x : Vec, v x j = 0)
    (i : Fin 3) (x : Vec) : coordinateDerivative v i x j = 0 := by
  have hc : HasFDerivAt (fun y : Vec => v y j)
      ((EuclideanSpace.proj j).comp (fderiv ℝ v x)) x :=
    (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).hasFDerivAt.comp x (hv x).hasFDerivAt
  have he : (fun y : Vec => v y j) = (fun _ : Vec => (0 : ℝ)) :=
    funext hz
  rw [he] at hc
  have hzero := hc.unique (hasFDerivAt_const (0 : ℝ) x)
  have happ := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) hzero
  simpa [coordinateDerivative] using happ

theorem physicalChannel_v_derivative_third_zero (N : ℕ) (A : Fin 6)
    (hA : A = 0 ∨ A = 1) (a : FourierCoeff) (i : Fin 3) (x : Vec) :
    coordinateDerivative (physicalChannel N A a) i x 2 = 0 :=
  coordinateDerivative_component_zero
    ((physicalChannel_contDiff N A a).differentiable (by simp)) 2
    (physicalChannel_v_third_zero N A hA a) i x

theorem physicalChannel_w_derivative_horizontal_zero (N : ℕ) (A : Fin 6)
    (hA : A = 2 ∨ A = 3) (a : FourierCoeff) (j : Fin 3) (hj : j ≠ 2)
    (i : Fin 3) (x : Vec) :
    coordinateDerivative (physicalChannel N A a) i x j = 0 :=
  coordinateDerivative_component_zero
    ((physicalChannel_contDiff N A a).differentiable (by simp)) j
    (fun y => physicalChannel_w_horizontal_zero N A hA a y j hj) i x

/-- The vanishing cross-gradient product is pointwise; no integration or
Fourier Parseval premise occurs. -/
theorem physicalChannel_v_w_gradient_product_zero (N : ℕ) (A B : Fin 6)
    (hA : A = 0 ∨ A = 1) (hB : B = 2 ∨ B = 3)
    (a b : FourierCoeff) (i j : Fin 3) (x : Vec) :
    coordinateDerivative (physicalChannel N A a) i x j *
      coordinateDerivative (physicalChannel N B b) i x j = 0 := by
  by_cases hj : j = 2
  · subst j
    rw [physicalChannel_v_derivative_third_zero N A hA, zero_mul]
  · rw [physicalChannel_w_derivative_horizontal_zero N B hB b j hj, mul_zero]

theorem gradientSquareDensity_add_of_disjoint_components {v w : Field}
    (hv : Differentiable ℝ v) (hw : Differentiable ℝ w)
    (horth : ∀ (x : Vec) (i j : Fin 3),
      coordinateDerivative v i x j * coordinateDerivative w i x j = 0)
    (x : Vec) :
    gradientSquareDensity (v + w) x =
      gradientSquareDensity v x + gradientSquareDensity w x := by
  have hd (i : Fin 3) :
      coordinateDerivative (v + w) i x =
        coordinateDerivative v i x + coordinateDerivative w i x := by
    unfold coordinateDerivative
    rw [fderiv_add (hv x) (hw x)]
    rfl
  unfold gradientSquareDensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hd]
  change (coordinateDerivative v i x j + coordinateDerivative w i x j) ^ 2 = _
  nlinarith [horth x i j]

theorem physicalEnstrophy_add_of_disjoint_components {v w : Field}
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w)
    (horth : ∀ (x : Vec) (i j : Fin 3),
      coordinateDerivative v i x j * coordinateDerivative w i x j = 0) :
    physicalEnstrophy (v + w) = physicalEnstrophy v + physicalEnstrophy w := by
  unfold physicalEnstrophy
  simp_rw [gradientSquareDensity_add_of_disjoint_components
    (hv.differentiable (by simp)) (hw.differentiable (by simp)) horth,
    ENNReal.ofReal_add (gradientSquareDensity_nonneg v _)
      (gradientSquareDensity_nonneg w _)]
  exact lintegral_add_left
    (ENNReal.continuous_ofReal.comp (gradientSquareDensity_continuous hv)).measurable _

/-- Actual physical enstrophy Pythagoras for each horizontal/vertical channel
pair, with arbitrary independent coefficient families. -/
theorem PHYSICAL_V_W_ENSTROPHY_EQ (N : ℕ) (A B : Fin 6)
    (hA : A = 0 ∨ A = 1) (hB : B = 2 ∨ B = 3)
    (a b : FourierCoeff) :
    physicalEnstrophy (physicalChannel N A a + physicalChannel N B b) =
      physicalEnstrophy (physicalChannel N A a) +
        physicalEnstrophy (physicalChannel N B b) :=
  physicalEnstrophy_add_of_disjoint_components
    (physicalChannel_contDiff N A a) (physicalChannel_contDiff N B b)
    (fun x i j => physicalChannel_v_w_gradient_product_zero N A B hA hB a b i j x)

theorem six_square_sum_le (f : Fin 6 → ℝ) :
    (∑ A : Fin 6, f A) ^ 2 ≤ 6 * ∑ A : Fin 6, (f A) ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin 6 => (1 : ℝ)) f

/-- Reconstruction supplies a quantitative physical bound even before the
sharper integral orthogonality theorem has been proved. -/
theorem gradientSquareDensity_le_six_channels (N : ℕ) (a : FourierCoeff)
    (x : Vec) :
    gradientSquareDensity (finiteSynthesis N a) x ≤
      6 * ∑ A : Fin 6, gradientSquareDensity (physicalChannel N A a) x := by
  have hd (i j : Fin 3) : coordinateDerivative (finiteSynthesis N a) i x j =
      ∑ A : Fin 6, coordinateDerivative (physicalChannel N A a) i x j := by
    have hh := congrArg (fun v : Vec => v j)
      (SIX_CHANNEL_FINITE_DERIVATIVE_RECONSTRUCTION N a i x)
    simpa using hh
  calc
    gradientSquareDensity (finiteSynthesis N a) x =
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ A : Fin 6, coordinateDerivative (physicalChannel N A a) i x j) ^ 2 := by
            simp only [gradientSquareDensity, hd]
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        6 * ∑ A : Fin 6, (coordinateDerivative (physicalChannel N A a) i x j) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        six_square_sum_le (fun A => coordinateDerivative (physicalChannel N A a) i x j)))
    _ = 6 * ∑ A : Fin 6, gradientSquareDensity (physicalChannel N A a) x := by
      simp only [gradientSquareDensity, Finset.mul_sum]
      calc
        _ = ∑ i : Fin 3, ∑ A : Fin 6, ∑ j : Fin 3,
            6 * (coordinateDerivative (physicalChannel N A a) i x j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem PHYSICAL_ENSTROPHY_LE_SIX_BUDGET (N : ℕ) (a : FourierCoeff) :
    physicalEnstrophy (finiteSynthesis N a) ≤ 6 * sixEnstrophy N a := by
  have hmeas (A : Fin 6) : Measurable (fun x : Vec =>
      ENNReal.ofReal (gradientSquareDensity (physicalChannel N A a) x)) :=
    (ENNReal.continuous_ofReal.comp
      (gradientSquareDensity_continuous (physicalChannel_contDiff N A a))).measurable
  have hpoint (x : Vec) :
      ENNReal.ofReal (gradientSquareDensity (finiteSynthesis N a) x) ≤
        (6 : ℝ≥0∞) * ∑ A : Fin 6,
          ENNReal.ofReal (gradientSquareDensity (physicalChannel N A a) x) := by
    calc
      _ ≤ ENNReal.ofReal (6 * ∑ A : Fin 6,
          gradientSquareDensity (physicalChannel N A a) x) :=
        ENNReal.ofReal_le_ofReal (gradientSquareDensity_le_six_channels N a x)
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
          ENNReal.ofReal_sum_of_nonneg
            (fun A _ => gradientSquareDensity_nonneg (physicalChannel N A a) x)]
        norm_num
  calc
    physicalEnstrophy (finiteSynthesis N a) ≤
        ∫⁻ x in unitCube, (6 : ℝ≥0∞) * ∑ A : Fin 6,
          ENNReal.ofReal (gradientSquareDensity (physicalChannel N A a) x) :=
      lintegral_mono hpoint
    _ = (6 : ℝ≥0∞) * ∫⁻ x in unitCube, ∑ A : Fin 6,
          ENNReal.ofReal (gradientSquareDensity (physicalChannel N A a) x) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ = 6 * sixEnstrophy N a := by
      rw [lintegral_finsetSum Finset.univ (fun A _ => hmeas A)]
      rfl

/-- The frozen AX6 budget controls actual square enstrophy without requiring
the unresolved Parseval equality. The constant is explicit and cutoff-free. -/
theorem PHYSICAL_SQUARE_BUDGET_LE_AX6_BUDGET (N : ℕ)
    (c : ℝ → FourierCoeff) (T : ℝ) :
    (∫⁻ t in Icc (0 : ℝ) T,
      (physicalEnstrophy (finiteSynthesis N (c t))) ^ 2) ≤
        36 * budget6 N c T := by
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) T,
        ((6 : ℝ≥0∞) * sixEnstrophy N (c t)) ^ 2 := by
      apply lintegral_mono
      intro t
      have h := PHYSICAL_ENSTROPHY_LE_SIX_BUDGET N (c t)
      simpa only [pow_two] using mul_le_mul' h h
    _ = ∫⁻ t in Icc (0 : ℝ) T,
        (36 : ℝ≥0∞) * (sixEnstrophy N (c t)) ^ 2 := by
      congr 1
      funext t
      rw [mul_pow]
      norm_num
    _ = 36 * budget6 N c T := lintegral_const_mul' _ _ (by norm_num)

end

end SingularClosure
