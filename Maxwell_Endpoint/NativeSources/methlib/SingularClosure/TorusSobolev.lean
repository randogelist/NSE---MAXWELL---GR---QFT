import SingularClosure.GalerkinEnergy
import SingularClosure.LerayPressure
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Concrete Fourier Sobolev sequence spaces on the unit three-torus

Elements are the original Fourier coefficient functions, with square-summable
weighted coefficients. The weight is the actual unit-period Laplace multiplier
`sqrt (1 + (2*pi)^2 * |k|^2)`. The Hilbert structure is transported through the
explicit weighted-coordinate equivalence with `lp`.

The cutoff retains the zero mode as well as the existing `cutoffModes N`.
For mean-zero coefficients it is exactly the existing Galerkin cutoff.
The fixed-time tail estimate is a spatial compactness ingredient; it does not
assert a spacetime subsequence, nonlinear limit passage, or endpoint 8.
-/

set_option autoImplicit false

open Set Filter
open scoped BigOperators Topology ENNReal

namespace SingularClosure

noncomputable section

abbrev FourierIndex := Frequency × Fin 3
abbrev FourierVectorSequence := lp (fun _ : FourierIndex => ℂ) 2

/-- The square root of one plus the actual unit-period Laplace symbol. -/
def torusSobolevWeight (k : Frequency) : ℝ :=
  Real.sqrt (1 + (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ))

theorem torusSobolevWeight_one_le (k : Frequency) : 1 ≤ torusSobolevWeight k := by
  have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi)) hk]

theorem torusSobolevWeight_pos (k : Frequency) : 0 < torusSobolevWeight k :=
  lt_of_lt_of_le zero_lt_one (torusSobolevWeight_one_le k)

theorem torusSobolevWeight_ne_zero (k : Frequency) :
    (torusSobolevWeight k : ℂ) ≠ 0 := by
  exact_mod_cast (torusSobolevWeight_pos k).ne'

/-- The actual weighted Fourier coordinates. -/
def sobolevWeightedCoeff (s : ℕ) (c : FourierCoeff) (ki : FourierIndex) : ℂ :=
  (torusSobolevWeight ki.1 : ℂ) ^ s * c ki.1 ki.2

theorem sobolevWeightedCoeff_zero (s : ℕ) :
    sobolevWeightedCoeff s 0 = 0 := by
  funext ki
  simp [sobolevWeightedCoeff]

theorem sobolevWeightedCoeff_add (s : ℕ) (c d : FourierCoeff) :
    sobolevWeightedCoeff s (c + d) = sobolevWeightedCoeff s c + sobolevWeightedCoeff s d := by
  funext ki
  exact mul_add _ _ _

theorem sobolevWeightedCoeff_smul (s : ℕ) (z : ℂ) (c : FourierCoeff) :
    sobolevWeightedCoeff s (z • c) = z • sobolevWeightedCoeff s c := by
  funext ki
  exact mul_left_comm _ _ _

theorem sobolevWeightedCoeff_succ_norm (s : ℕ) (c : FourierCoeff) (ki : FourierIndex) :
    ‖sobolevWeightedCoeff (s + 1) c ki‖ =
      torusSobolevWeight ki.1 * ‖sobolevWeightedCoeff s c ki‖ := by
  have hprod : (torusSobolevWeight ki.1 : ℂ) ^ (s + 1) * c ki.1 ki.2 =
      (torusSobolevWeight ki.1 : ℂ) *
        ((torusSobolevWeight ki.1 : ℂ) ^ s * c ki.1 ki.2) := by
    rw [pow_succ]
    ring
  unfold sobolevWeightedCoeff
  rw [hprod, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (torusSobolevWeight_pos _)]

def torusSobolevSubmodule (s : ℕ) : Submodule ℂ FourierCoeff where
  carrier := {c | Memℓp (sobolevWeightedCoeff s c) 2}
  zero_mem' := by
    change Memℓp (sobolevWeightedCoeff s 0) 2
    rw [sobolevWeightedCoeff_zero]
    exact zero_memℓp
  add_mem' := by
    intro c d hc hd
    change Memℓp (sobolevWeightedCoeff s (c + d)) 2
    rw [sobolevWeightedCoeff_add]
    exact hc.add hd
  smul_mem' := by
    intro z c hc
    change Memℓp (sobolevWeightedCoeff s (z • c)) 2
    rw [sobolevWeightedCoeff_smul]
    exact hc.const_smul z

/-- Sobolev coefficient functions of integral order `s`. -/
def TorusSobolev (s : ℕ) : Type :=
  {c : FourierCoeff // Memℓp (sobolevWeightedCoeff s c) 2}

instance torusSobolevAddCommGroup (s : ℕ) : AddCommGroup (TorusSobolev s) :=
  inferInstanceAs (AddCommGroup ↥(torusSobolevSubmodule s))

instance torusSobolevModule (s : ℕ) : Module ℂ (TorusSobolev s) :=
  inferInstanceAs (Module ℂ ↥(torusSobolevSubmodule s))

def torusSobolevReprLinear (s : ℕ) : TorusSobolev s →ₗ[ℂ] FourierVectorSequence where
  toFun c := ⟨sobolevWeightedCoeff s c.val, c.property⟩
  map_add' c d := by
    apply lp.ext
    funext ki
    change (torusSobolevWeight ki.1 : ℂ) ^ s * (c.val ki.1 ki.2 + d.val ki.1 ki.2) =
      (torusSobolevWeight ki.1 : ℂ) ^ s * c.val ki.1 ki.2 +
        (torusSobolevWeight ki.1 : ℂ) ^ s * d.val ki.1 ki.2
    exact mul_add _ _ _
  map_smul' z c := by
    apply lp.ext
    funext ki
    change (torusSobolevWeight ki.1 : ℂ) ^ s * (z * c.val ki.1 ki.2) =
      z * ((torusSobolevWeight ki.1 : ℂ) ^ s * c.val ki.1 ki.2)
    exact mul_left_comm _ _ _

@[simp]
theorem torusSobolevReprLinear_apply (s : ℕ) (c : TorusSobolev s)
    (ki : FourierIndex) :
    torusSobolevReprLinear s c ki =
      (torusSobolevWeight ki.1 : ℂ) ^ s * c.val ki.1 ki.2 := rfl

theorem torusSobolevReprLinear_injective (s : ℕ) :
    Function.Injective (torusSobolevReprLinear s) := by
  intro c d h
  apply Subtype.ext
  funext k i
  have hki := congrArg (fun z : FourierVectorSequence => z (k, i)) h
  exact mul_left_cancel₀ (pow_ne_zero s (torusSobolevWeight_ne_zero k)) hki

theorem torusSobolevReprLinear_surjective (s : ℕ) :
    Function.Surjective (torusSobolevReprLinear s) := by
  intro z
  let c : FourierCoeff := fun k i => z (k, i) / (torusSobolevWeight k : ℂ) ^ s
  have hc : sobolevWeightedCoeff s c = (z : FourierIndex → ℂ) := by
    funext ki
    dsimp [sobolevWeightedCoeff, c]
    have hw : (torusSobolevWeight ki.1 : ℂ) ^ s ≠ 0 :=
      pow_ne_zero s (torusSobolevWeight_ne_zero ki.1)
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hw, mul_one]
  refine ⟨⟨c, ?_⟩, ?_⟩
  · change Memℓp (sobolevWeightedCoeff s c) 2
    rw [hc]
    exact lp.memℓp z
  · apply lp.ext
    exact hc

theorem torusSobolevInclusion_mem (s : ℕ) (c : TorusSobolev (s + 1)) :
    Memℓp (sobolevWeightedCoeff s c.val) 2 := by
  apply c.property.mono'
  intro ki
  change ‖sobolevWeightedCoeff s c.val ki‖ ≤ ‖sobolevWeightedCoeff (s + 1) c.val ki‖
  rw [sobolevWeightedCoeff_succ_norm]
  exact le_mul_of_one_le_left (norm_nonneg _) (torusSobolevWeight_one_le _)

theorem exists_torusSobolevInclusionValue (s : ℕ) (c : TorusSobolev (s + 1)) :
    ∃ v : TorusSobolev s, v.val = c.val :=
  ⟨⟨c.val, torusSobolevInclusion_mem s c⟩, Eq.refl c.val⟩

def torusSobolevInclusionValue (s : ℕ) (c : TorusSobolev (s + 1)) : TorusSobolev s :=
  (exists_torusSobolevInclusionValue s c).choose

@[simp]
theorem torusSobolevInclusionValue_coeff (s : ℕ) (c : TorusSobolev (s + 1)) :
    (torusSobolevInclusionValue s c).val = c.val :=
  (exists_torusSobolevInclusionValue s c).choose_spec

theorem torusSobolevInclusionValue_add (s : ℕ) (c d : TorusSobolev (s + 1)) :
    torusSobolevInclusionValue s (c + d) =
      torusSobolevInclusionValue s c + torusSobolevInclusionValue s d := by
  apply Subtype.ext
  change (torusSobolevInclusionValue s (c + d)).val =
    (torusSobolevInclusionValue s c).val + (torusSobolevInclusionValue s d).val
  rw [torusSobolevInclusionValue_coeff, torusSobolevInclusionValue_coeff,
    torusSobolevInclusionValue_coeff] <;> rfl

theorem torusSobolevInclusionValue_smul (s : ℕ) (z : ℂ) (c : TorusSobolev (s + 1)) :
    torusSobolevInclusionValue s (z • c) = z • torusSobolevInclusionValue s c := by
  apply Subtype.ext
  change (torusSobolevInclusionValue s (z • c)).val =
    z • (torusSobolevInclusionValue s c).val
  rw [torusSobolevInclusionValue_coeff, torusSobolevInclusionValue_coeff] <;> rfl

/-- Inclusion of the actual coefficient functions drops one Sobolev order. -/
def torusSobolevInclusionLinear (s : ℕ) : TorusSobolev (s + 1) →ₗ[ℂ] TorusSobolev s where
  toFun := torusSobolevInclusionValue s
  map_add' := torusSobolevInclusionValue_add s
  map_smul' := torusSobolevInclusionValue_smul s

@[simp]
theorem torusSobolevInclusionLinear_coeff (s : ℕ) (c : TorusSobolev (s + 1)) :
    (torusSobolevInclusionLinear s c).val = c.val :=
  torusSobolevInclusionValue_coeff s c

instance torusSobolevNormedAddCommGroup (s : ℕ) : NormedAddCommGroup (TorusSobolev s) :=
  NormedAddCommGroup.induced _ _ (torusSobolevReprLinear s)
    (torusSobolevReprLinear_injective s)

instance torusSobolevInnerProductSpace (s : ℕ) : InnerProductSpace ℂ (TorusSobolev s) :=
  InnerProductSpace.induced (torusSobolevReprLinear s)

/-- Explicit isometric weighted-coordinate representation. -/
def torusSobolevRepr (s : ℕ) : TorusSobolev s ≃ₗᵢ[ℂ] FourierVectorSequence where
  __ := LinearEquiv.ofBijective (torusSobolevReprLinear s)
    ⟨torusSobolevReprLinear_injective s, torusSobolevReprLinear_surjective s⟩
  norm_map' _ := rfl

@[simp]
theorem torusSobolevRepr_apply (s : ℕ) (c : TorusSobolev s) (ki : FourierIndex) :
    torusSobolevRepr s c ki =
      (torusSobolevWeight ki.1 : ℂ) ^ s * c.val ki.1 ki.2 := rfl

instance torusSobolevCompleteSpace (s : ℕ) : CompleteSpace (TorusSobolev s) :=
  (torusSobolevRepr s).toIsometryEquiv.completeSpace_iff.mpr inferInstance

theorem torusSobolev_norm_sq (s : ℕ) (c : TorusSobolev s) :
    ‖c‖ ^ 2 = ∑' ki : FourierIndex,
      (torusSobolevWeight ki.1 ^ s * ‖c.val ki.1 ki.2‖) ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (torusSobolevRepr s c)
  simpa [torusSobolevRepr_apply, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (torusSobolevWeight_pos _), Real.rpow_natCast] using h

theorem torusSobolevInclusion_repr_norm_le (s : ℕ) (c : TorusSobolev (s + 1)) :
    ‖torusSobolevRepr s (torusSobolevInclusionLinear s c)‖ ≤
      ‖torusSobolevRepr (s + 1) c‖ := by
  apply lp.norm_mono (by norm_num)
  intro ki
  simp only [torusSobolevRepr_apply, torusSobolevInclusionLinear_coeff]
  change ‖sobolevWeightedCoeff s c.val ki‖ ≤ ‖sobolevWeightedCoeff (s + 1) c.val ki‖
  rw [sobolevWeightedCoeff_succ_norm]
  exact le_mul_of_one_le_left (norm_nonneg _) (torusSobolevWeight_one_le _)

theorem torusSobolevInclusion_norm_le (s : ℕ) (c : TorusSobolev (s + 1)) :
    ‖torusSobolevInclusionLinear s c‖ ≤ ‖c‖ := by
  calc
    _ = ‖torusSobolevRepr s (torusSobolevInclusionLinear s c)‖ :=
      ((torusSobolevRepr s).norm_map _).symm
    _ ≤ ‖torusSobolevRepr (s + 1) c‖ := torusSobolevInclusion_repr_norm_le s c
    _ = ‖c‖ := (torusSobolevRepr (s + 1)).norm_map c

theorem torusSobolevInclusion_bound (s : ℕ) (c : TorusSobolev (s + 1)) :
    ‖torusSobolevInclusionLinear s c‖ ≤ 1 * ‖c‖ := by
  simpa only [one_mul] using torusSobolevInclusion_norm_le s c

def torusSobolevInclusion (s : ℕ) : TorusSobolev (s + 1) →L[ℂ] TorusSobolev s :=
  (torusSobolevInclusionLinear s).mkContinuous 1 (torusSobolevInclusion_bound s)

@[simp]
theorem torusSobolevInclusion_coeff (s : ℕ) (c : TorusSobolev (s + 1)) :
    (torusSobolevInclusion s c).val = c.val := by
  unfold torusSobolevInclusion
  exact (congrArg (fun v : TorusSobolev s => v.val)
    ((torusSobolevInclusionLinear s).mkContinuous_apply 1
      (torusSobolevInclusion_bound s) c)).trans (torusSobolevInclusionLinear_coeff s c)

/-- Zero mode plus exactly the existing nonzero Galerkin cutoff. -/
def sobolevCutoffModes (N : ℕ) : Finset Frequency := insert 0 (cutoffModes N)

theorem mem_cutoffModes_of_freqSq_le {N : ℕ} {k : Frequency}
    (hk : k ≠ 0) (hsq : galerkinFreqSq k ≤ (N : ℤ) ^ 2) : k ∈ cutoffModes N := by
  apply (mem_cutoffModes_iff N k).mpr
  refine ⟨?_, hk, hsq⟩
  intro i
  have hi : (k i) ^ 2 ≤ galerkinFreqSq k :=
    Finset.single_le_sum (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i)
  have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  exact abs_le.mp (abs_le_of_sq_le_sq (hi.trans hsq) hN)

theorem freqSq_gt_of_not_mem_sobolevCutoff {N : ℕ} {k : Frequency}
    (hk : k ∉ sobolevCutoffModes N) : (N : ℤ) ^ 2 < galerkinFreqSq k := by
  have hzero : k ≠ 0 := by
    intro h
    apply hk
    simp [sobolevCutoffModes, h]
  by_contra h
  exact hk (Finset.mem_insert_of_mem (mem_cutoffModes_of_freqSq_le hzero (le_of_not_gt h)))

theorem torusSobolevWeight_ge_cutoff {N : ℕ} {k : Frequency}
    (hk : k ∉ sobolevCutoffModes N) : (N : ℝ) ≤ torusSobolevWeight k := by
  have hfreq : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg k
  have hsq : (N : ℝ) ^ 2 < (galerkinFreqSq k : ℝ) := by
    exact_mod_cast freqSq_gt_of_not_mem_sobolevCutoff hk
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  apply (Real.le_sqrt (Nat.cast_nonneg N) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hpi hfreq]

def torusSobolevCutoffLinear (s N : ℕ) : TorusSobolev s →ₗ[ℂ] TorusSobolev s where
  toFun c := ⟨fun k i => if k ∈ sobolevCutoffModes N then c.val k i else 0, by
    apply c.property.mono'
    intro ki
    by_cases h : ki.1 ∈ sobolevCutoffModes N <;>
      simp [sobolevWeightedCoeff, h] <;> positivity⟩
  map_add' c d := by
    apply Subtype.ext
    funext k i
    change (if k ∈ sobolevCutoffModes N then c.val k i + d.val k i else 0) =
      (if k ∈ sobolevCutoffModes N then c.val k i else 0) +
        (if k ∈ sobolevCutoffModes N then d.val k i else 0)
    by_cases h : k ∈ sobolevCutoffModes N <;> simp [h]
  map_smul' z c := by
    apply Subtype.ext
    funext k i
    change (if k ∈ sobolevCutoffModes N then z * c.val k i else 0) =
      z * (if k ∈ sobolevCutoffModes N then c.val k i else 0)
    by_cases h : k ∈ sobolevCutoffModes N <;> simp [h]

theorem torusSobolevCutoff_norm_le (s N : ℕ) (c : TorusSobolev s) :
    ‖torusSobolevCutoffLinear s N c‖ ≤ ‖c‖ := by
  change ‖torusSobolevReprLinear s (torusSobolevCutoffLinear s N c)‖ ≤
    ‖torusSobolevReprLinear s c‖
  apply lp.norm_mono (by norm_num)
  intro ki
  change ‖(torusSobolevWeight ki.1 : ℂ) ^ s *
      (if ki.1 ∈ sobolevCutoffModes N then c.val ki.1 ki.2 else 0)‖ ≤
    ‖(torusSobolevWeight ki.1 : ℂ) ^ s * c.val ki.1 ki.2‖
  by_cases h : ki.1 ∈ sobolevCutoffModes N
  · rw [if_pos h]
  · rw [if_neg h, mul_zero, norm_zero]
    exact norm_nonneg _

def torusSobolevCutoff (s N : ℕ) : TorusSobolev s →L[ℂ] TorusSobolev s :=
  (torusSobolevCutoffLinear s N).mkContinuous 1
    (fun c => by simpa using torusSobolevCutoff_norm_le s N c)

@[simp]
theorem torusSobolevCutoff_coeff (s N : ℕ) (c : TorusSobolev s) (k : Frequency)
    (i : Fin 3) :
    (torusSobolevCutoff s N c).val k i =
      if k ∈ sobolevCutoffModes N then c.val k i else 0 := rfl

theorem torusSobolevCutoff_eq_galerkinCutoff (s N : ℕ) (c : TorusSobolev s)
    (hc : ∀ i : Fin 3, c.val 0 i = 0) :
    (torusSobolevCutoff s N c).val = cutoffCoeff N c.val := by
  funext k i
  by_cases hk : k = 0
  · subst k
    simp [cutoffCoeff, torusSobolevCutoff_coeff, hc]
  · simp [torusSobolevCutoff_coeff, cutoffCoeff, sobolevCutoffModes, hk]

/-- Quantitative uniform high-frequency tail: one Sobolev derivative gains `N⁻¹`. -/
theorem torusSobolevInclusion_tail (s N : ℕ) (hN : 0 < N)
    (c : TorusSobolev (s + 1)) :
    ‖torusSobolevInclusion s c - torusSobolevCutoff s N (torusSobolevInclusion s c)‖ ≤
      (N : ℝ)⁻¹ * ‖c‖ := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNreal.le
  calc
    _ ≤ ‖(N : ℝ)⁻¹ • torusSobolevRepr (s + 1) c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      change ‖(torusSobolevWeight ki.1 : ℂ) ^ s *
          ((torusSobolevInclusion s c).val ki.1 ki.2 -
            (torusSobolevCutoff s N (torusSobolevInclusion s c)).val ki.1 ki.2)‖ ≤
        ‖(N : ℝ)⁻¹ • (torusSobolevRepr (s + 1) c ki)‖
      rw [torusSobolevCutoff_coeff, torusSobolevInclusion_coeff]
      by_cases hk : ki.1 ∈ sobolevCutoffModes N
      · rw [if_pos hk, sub_self, mul_zero, norm_zero]
        exact norm_nonneg _
      · have hw := torusSobolevWeight_ge_cutoff hk
        rw [if_neg hk, sub_zero]
        change ‖sobolevWeightedCoeff s c.val ki‖ ≤
          ‖(N : ℝ)⁻¹ • sobolevWeightedCoeff (s + 1) c.val ki‖
        rw [norm_smul, Real.norm_of_nonneg hNinv, sobolevWeightedCoeff_succ_norm]
        have hfactor : 1 ≤ (N : ℝ)⁻¹ * torusSobolevWeight ki.1 := by
          calc
            1 = (N : ℝ)⁻¹ * (N : ℝ) := (inv_mul_cancel₀ hNreal.ne').symm
            _ ≤ (N : ℝ)⁻¹ * torusSobolevWeight ki.1 :=
              mul_le_mul_of_nonneg_left hw hNinv
        calc
          _ = 1 * ‖sobolevWeightedCoeff s c.val ki‖ := (one_mul _).symm
          _ ≤ ((N : ℝ)⁻¹ * torusSobolevWeight ki.1) *
              ‖sobolevWeightedCoeff s c.val ki‖ :=
            mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
          _ = _ := mul_assoc _ _ _
    _ = (N : ℝ)⁻¹ * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hNinv,
        (torusSobolevRepr (s + 1)).norm_map]

def sobolevCutoffIndices (N : ℕ) : Finset FourierIndex :=
  (sobolevCutoffModes N).product Finset.univ

/-- A single coordinate projection, conjugated by the actual weighted isometry. -/
def torusSobolevRankOne (s : ℕ) (ki : FourierIndex) :
    TorusSobolev s →L[ℂ] TorusSobolev s :=
  (((torusSobolevRepr s).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (lp.singleContinuousLinearMap ℂ (fun _ : FourierIndex => ℂ) 2 ki)).comp
      ((lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 ki).comp
        (torusSobolevRepr s).toContinuousLinearEquiv.toContinuousLinearMap)

theorem torusSobolevRankOne_repr (s : ℕ) (ki : FourierIndex) (c : TorusSobolev s) :
    torusSobolevRepr s (torusSobolevRankOne s ki c) =
      lp.single 2 ki (torusSobolevRepr s c ki) := by
  change torusSobolevRepr s
      ((torusSobolevRepr s).symm (lp.single 2 ki (torusSobolevRepr s c ki))) = _
  exact (torusSobolevRepr s).apply_symm_apply _

theorem torusSobolevRankOne_compact (s : ℕ) (ki : FourierIndex) :
    IsCompactOperator (torusSobolevRankOne s ki) := by
  let A : ℂ →L[ℂ] TorusSobolev s :=
    ((torusSobolevRepr s).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (lp.singleContinuousLinearMap ℂ (fun _ : FourierIndex => ℂ) 2 ki)
  let B : TorusSobolev s →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 ki).comp
      (torusSobolevRepr s).toContinuousLinearEquiv.toContinuousLinearMap
  have hA : IsCompactOperator A := isCompactOperator_of_locallyCompactSpace_rng A
  simpa only [torusSobolevRankOne, A, B, ContinuousLinearMap.coe_comp] using hA.comp_clm B

theorem torusSobolevCutoff_eq_sum_rankOne (s N : ℕ) :
    torusSobolevCutoff s N = ∑ ki ∈ sobolevCutoffIndices N, torusSobolevRankOne s ki := by
  apply ContinuousLinearMap.ext
  intro c
  apply (torusSobolevRepr s).injective
  simp only [ContinuousLinearMap.sum_apply, map_sum, torusSobolevRankOne_repr]
  apply lp.ext
  funext ki
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  change (torusSobolevWeight ki.1 : ℂ) ^ s *
      (if ki.1 ∈ sobolevCutoffModes N then c.val ki.1 ki.2 else 0) =
    if ki ∈ sobolevCutoffIndices N then
      (torusSobolevWeight ki.1 : ℂ) ^ s * c.val ki.1 ki.2 else 0
  by_cases h : ki.1 ∈ sobolevCutoffModes N <;> simp [sobolevCutoffIndices, h]

theorem torusSobolevCutoff_compact (s N : ℕ) :
    IsCompactOperator (torusSobolevCutoff s N) := by
  rw [torusSobolevCutoff_eq_sum_rankOne]
  generalize sobolevCutoffIndices N = I
  induction I using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero :
      IsCompactOperator (0 : TorusSobolev s →L[ℂ] TorusSobolev s))
  | @insert ki I hki ih =>
    rw [Finset.sum_insert hki]
    exact (torusSobolevRankOne_compact s ki).add ih

/-- Uniform convergence in operator norm of the finite cutoffs of the inclusion. -/
theorem torusSobolevInclusion_cutoff_tendsto (s : ℕ) :
    Tendsto (fun n : ℕ => (torusSobolevCutoff s (n + 1)).comp (torusSobolevInclusion s))
      atTop (𝓝 (torusSobolevInclusion s)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hballs : (𝓝 (0 : TorusSobolev s)).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => Metric.ball (0 : TorusSobolev s) ε) := Metric.nhds_basis_ball
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis hballs).tendsto_right_iff.mpr
  rintro ⟨S, ε⟩ ⟨hS, hε⟩
  obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp hS
  let B : ℝ := max R 0 + 1
  have hRB : R ≤ B := le_trans (le_max_left R 0) (by dsimp [B]; linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
  filter_upwards [eventually_ge_atTop M] with n hn
  intro c hc
  change dist (((torusSobolevCutoff s (n + 1)).comp (torusSobolevInclusion s) -
    torusSobolevInclusion s) c) 0 < ε
  rw [dist_zero_right, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, norm_sub_rev]
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlarge : B / ε < ((n + 1 : ℕ) : ℝ) := by
    have hmn : (M : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  have hprod : B < ((n + 1 : ℕ) : ℝ) * ε := (div_lt_iff₀ hε).mp hlarge
  calc
    _ ≤ (((n + 1 : ℕ) : ℝ))⁻¹ * ‖c‖ :=
      torusSobolevInclusion_tail s (n + 1) (Nat.succ_pos n) c
    _ ≤ (((n + 1 : ℕ) : ℝ))⁻¹ * B :=
      mul_le_mul_of_nonneg_left ((hR c hc).trans hRB) (inv_nonneg.mpr hN.le)
    _ = B / ((n + 1 : ℕ) : ℝ) := by rw [div_eq_mul_inv, mul_comm]
    _ < ε := (div_lt_iff₀ hN).mpr (by simpa only [mul_comm] using hprod)

/-- Compact inclusion of the actual Fourier Sobolev spaces, in every integral order. -/
theorem torusSobolevInclusion_compact (s : ℕ) :
    IsCompactOperator (torusSobolevInclusion s) := by
  apply isCompactOperator_of_tendsto (torusSobolevInclusion_cutoff_tendsto s)
  exact Filter.Eventually.of_forall fun n =>
    (torusSobolevCutoff_compact s (n + 1)).comp_clm (torusSobolevInclusion s)

/-- Bounded H² sets have relatively compact images in H¹, at fixed time. -/
theorem torusSobolev_H2_H1_compact_closedBall (R : ℝ) :
    IsCompact (closure ((torusSobolevInclusion 1) ''
      Metric.closedBall (0 : TorusSobolev 2) R)) := by
  exact (torusSobolevInclusion_compact 1).isCompact_closure_image_closedBall R

end

end SingularClosure
