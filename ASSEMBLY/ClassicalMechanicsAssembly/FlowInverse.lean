import ClassicalMechanics.Material
import ClassicalMechanicsAssembly.PiolaTransport
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

/-!
Closed-set inverse regularity from an actual smooth forward map, a continuous
inverse, and an invertible derivative. No flow-existence axiom is imported.
The finite-slab adapters retain the inverse laws and derivative geometry.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set Filter ClassicalMechanics NSEMaxwell.Classical
open scoped Topology ContDiff NNReal BigOperators

noncomputable section

section GeneralInverse

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set E} {t : Set F} {f : E → F} {g : F → E}

/-- The inverse derivative uses continuity and the inverse identity on the set. -/
theorem hasFDerivWithinAt_inverse_of_contDiffOn
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContinuousOn g t)
    (hmap : MapsTo g t s) (hfg : ∀ y ∈ t, f (g y) = y)
    (hinv : ∀ x ∈ s, (fderivWithin ℝ f s x).IsInvertible)
    {y : F} (hy : y ∈ t) :
    HasFDerivWithinAt g
      (ContinuousLinearMap.inverse (fderivWithin ℝ f s (g y))) t y := by
  obtain ⟨e, he⟩ := hinv (g y) (hmap hy)
  have hdf : HasFDerivWithinAt f (e : E →L[ℝ] F) s (g y) := by
    rw [he]
    exact (hf.differentiableOn (by simp) (g y) (hmap hy)).hasFDerivWithinAt
  have hright : ∀ᶠ z in 𝓝[t] y, f (g z) = z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hfg z hz
  have hdg := HasFDerivWithinAt.of_local_left_inverse
    ((hg y hy).tendsto_nhdsWithin hmap) hdf hy hright
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact hdg

/-- Joint smoothness of a continuous inverse, directly on unique-differentiability sets. -/
theorem contDiffOn_inverse_of_contDiffOn
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContinuousOn g t)
    (hmap : MapsTo g t s) (hfg : ∀ y ∈ t, f (g y) = y)
    (hinv : ∀ x ∈ s, (fderivWithin ℝ f s x).IsInvertible) :
    ContDiffOn ℝ ∞ g t := by
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hg
  | succ n ih =>
      have hdf_infty : ContDiffOn ℝ ∞ (fderivWithin ℝ f s) s :=
        hf.fderivWithin hs (by simp)
      have hdf : ContDiffOn ℝ (n : ℕ∞ω) (fderivWithin ℝ f s) s :=
        (contDiffOn_infty.mp hdf_infty) n
      have hcomp := hdf.comp ih hmap
      have hderiv : ContDiffOn ℝ (n : ℕ∞ω)
          (fun y => ContinuousLinearMap.inverse (fderivWithin ℝ f s (g y))) t := by
        intro y hy
        exact (hinv (g y) (hmap hy)).contDiffAt_map_inverse.comp_contDiffWithinAt
          y (hcomp y hy)
      have hsucc : ContDiffOn ℝ ((n : ℕ∞ω) + 1) g t := by
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ht).mpr
        refine ⟨by simp, _, hderiv, ?_⟩
        intro y hy
        exact hasFDerivWithinAt_inverse_of_contDiffOn hf hg hmap hfg hinv hy
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hsucc

end GeneralInverse

/-- The map on spacetime associated to a material configuration. -/
def flowSpacetimeMap (η : Velocity) : (ℝ × Vec) → (ℝ × Vec) :=
  fun z => (z.1, η z.1 z.2)

/-- The spatial matrix used by the material record is the actual derivative matrix. -/
theorem spatial_fderiv_isInvertible_of_det_one (v : Field) (a : Vec)
    (hdet : (materialGradientMatrix v a).det = 1) :
    (fderiv ℝ v a).IsInvertible := by
  have heq : Matrix.toEuclideanLin (materialGradientMatrix v a) =
      (fderiv ℝ v a).toLinearMap := by
    apply LinearMap.ext
    intro w
    apply PiLp.ext
    intro i
    change (∑ j : Fin 3, coordinateDerivative v j a i * w j) =
      fderiv ℝ v a w i
    rw [vector_fderiv_coordinate_expansion]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hd : (fderiv ℝ v a).det = 1 := by
    change LinearMap.det (fderiv ℝ v a).toLinearMap = 1
    rw [← heq, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
    exact hdet
  have hne : (fderiv ℝ v a).det ≠ 0 := by
    rw [hd]
    exact one_ne_zero
  exact ⟨(fderiv ℝ v a).toContinuousLinearEquivOfDetNeZero hne,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hne⟩

/-- An identity time component and invertible spatial restriction form an invertible block map. -/
theorem triangular_spacetime_isInvertible
    (D : (ℝ × Vec) →L[ℝ] Vec) (F : Vec →L[ℝ] Vec)
    (hF : F.IsInvertible) (hD : ∀ h : Vec, D (0, h) = F h) :
    ((ContinuousLinearMap.fst ℝ ℝ Vec).prod D).IsInvertible := by
  obtain ⟨e, he⟩ := hF
  have hsum (r : ℝ) (v : Vec) : D (r, v) = r • D (1, 0) + e v := by
    calc
      D (r, v) = D (r • ((1 : ℝ), (0 : Vec)) + (0, v)) := by
        congr 1
        simp
      _ = r • D (1, 0) + D (0, v) := by rw [map_add, map_smul]
      _ = r • D (1, 0) + e v := by
        rw [hD, ← he]
        rfl
  let L : (ℝ × Vec) →L[ℝ] (ℝ × Vec) :=
    (ContinuousLinearMap.fst ℝ ℝ Vec).prod D
  have hbij : Function.Bijective L := by
    constructor
    · intro z w h
      have ht := congrArg Prod.fst h
      have hx := congrArg Prod.snd h
      change z.1 = w.1 at ht
      change D z = D w at hx
      apply Prod.ext ht
      apply e.injective
      rw [hsum z.1 z.2, hsum w.1 w.2, ht] at hx
      exact add_left_cancel hx
    · intro z
      refine ⟨(z.1, e.symm (z.2 - z.1 • D (1, 0))), ?_⟩
      change (z.1, D (z.1, e.symm (z.2 - z.1 • D (1, 0)))) = z
      apply Prod.ext rfl
      rw [hsum, e.apply_symm_apply]
      abel
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  rfl

/-- Unit spatial Jacobian discharges invertibility of the actual spacetime within derivative. -/
theorem flowSpacetimeMap_fderivWithin_isInvertible {T : ℝ} (hT : 0 < T)
    {η : Velocity} (hη : SmoothVelocityOn T η)
    (hdet : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, (deformationGradient η t a).det = 1)
    (z : ℝ × Vec) (hz : z ∈ finiteSpacetime T) :
    (fderivWithin ℝ (flowSpacetimeMap η) (finiteSpacetime T) z).IsInvertible := by
  let D : (ℝ × Vec) →L[ℝ] Vec :=
    fderivWithin ℝ (fun w : ℝ × Vec => η w.1 w.2) (finiteSpacetime T) z
  have hD : ∀ h : Vec, D (0, h) = fderiv ℝ (η z.1) z.2 h := by
    intro h
    exact (finite_spatial_restriction_fderiv hη hz z.2 h).symm
  have hF := spatial_fderiv_isInvertible_of_det_one (η z.1) z.2 (hdet z.1 hz z.2)
  have hdη := (hη.differentiableOn (by simp) z hz).hasFDerivWithinAt
  have hdH := (hasFDerivWithinAt_fst (𝕜 := ℝ) (p := z)).prodMk hdη
  have heq : fderivWithin ℝ (flowSpacetimeMap η) (finiteSpacetime T) z =
      (ContinuousLinearMap.fst ℝ ℝ Vec).prod D :=
    hdH.fderivWithin (uniqueDiffOn_finiteSpacetime hT z hz)
  rw [heq]
  exact triangular_spacetime_isInvertible D (fderiv ℝ (η z.1) z.2) hF hD

/-- Stability of inverse slices and bounded motion imply a joint inverse estimate. -/
theorem inverse_flow_dist_le {T : ℝ} {η ρ : Velocity} {B C : ℝ≥0}
    (hleft : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, ρ t (η t a) = a)
    (hright : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, η t (ρ t x) = x)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith C (ρ t))
    (htime : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      dist (η t a) (η s a) ≤ (B : ℝ) * dist t s)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hs : s ∈ Icc (0 : ℝ) T)
    (x y : Vec) :
    dist (ρ t x) (ρ s y) ≤ (C : ℝ) * (dist x y + (B : ℝ) * dist t s) := by
  have hmotion : dist y (η t (ρ s y)) ≤ (B : ℝ) * dist t s := by
    calc
      dist y (η t (ρ s y)) = dist (η s (ρ s y)) (η t (ρ s y)) := by
        rw [hright s hs y]
      _ ≤ (B : ℝ) * dist s t := htime s hs t ht (ρ s y)
      _ = (B : ℝ) * dist t s := by rw [dist_comm s t]
  calc
    dist (ρ t x) (ρ s y) = dist (ρ t x) (ρ t (η t (ρ s y))) := by
      rw [hleft t ht (ρ s y)]
    _ ≤ (C : ℝ) * dist x (η t (ρ s y)) :=
      (hlip t ht).dist_le_mul x (η t (ρ s y))
    _ ≤ (C : ℝ) * (dist x y + dist y (η t (ρ s y))) :=
      mul_le_mul_of_nonneg_left (dist_triangle x y (η t (ρ s y))) C.coe_nonneg
    _ ≤ (C : ℝ) * (dist x y + (B : ℝ) * dist t s) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl (dist x y)) hmotion) C.coe_nonneg

/-- The quantitative inverse estimate supplies joint continuity on the closed slab. -/
theorem continuousOn_inverse_flow_of_estimate {T : ℝ} {ρ : Velocity} {B C : ℝ≥0}
    (hestimate : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T, ∀ x y : Vec,
      dist (ρ t x) (ρ s y) ≤ (C : ℝ) * (dist x y + (B : ℝ) * dist t s)) :
    ContinuousOn (fun z : ℝ × Vec => ρ z.1 z.2) (finiteSpacetime T) := by
  have hlip : LipschitzOnWith (C * (1 + B))
      (fun z : ℝ × Vec => ρ z.1 z.2) (finiteSpacetime T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hfst : dist z.1 w.1 ≤ dist z w := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have hsnd : dist z.2 w.2 ≤ dist z w := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    calc
      dist (ρ z.1 z.2) (ρ w.1 w.2) ≤
          (C : ℝ) * (dist z.2 w.2 + (B : ℝ) * dist z.1 w.1) :=
        hestimate z.1 hz w.1 hw z.2 w.2
      _ ≤ (C : ℝ) * (dist z w + (B : ℝ) * dist z w) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hsnd (mul_le_mul_of_nonneg_left hfst B.coe_nonneg)) C.coe_nonneg
      _ = (↑(C * (1 + B)) : ℝ) * dist z w := by
        simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one]
        ring
  exact hlip.continuousOn

/-- No off-slab extension is needed to transfer forward smoothness to the inverse. -/
theorem smoothVelocityOn_inverse_of_isInvertible {T : ℝ} (hT : 0 < T) {η ρ : Velocity}
    (hη : SmoothVelocityOn T η)
    (hρ : ContinuousOn (fun z : ℝ × Vec => ρ z.1 z.2) (finiteSpacetime T))
    (hright : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, η t (ρ t x) = x)
    (hinv : ∀ z ∈ finiteSpacetime T,
      (fderivWithin ℝ (flowSpacetimeMap η) (finiteSpacetime T) z).IsInvertible) :
    SmoothVelocityOn T ρ := by
  have hs := uniqueDiffOn_finiteSpacetime hT
  have hforward : ContDiffOn ℝ ∞ (flowSpacetimeMap η) (finiteSpacetime T) :=
    contDiff_fst.contDiffOn.prodMk hη
  have hbackward : ContinuousOn (flowSpacetimeMap ρ) (finiteSpacetime T) :=
    continuous_fst.continuousOn.prodMk hρ
  have hmap : MapsTo (flowSpacetimeMap ρ) (finiteSpacetime T) (finiteSpacetime T) :=
    fun _ hz => hz
  have hidentity : ∀ z ∈ finiteSpacetime T,
      flowSpacetimeMap η (flowSpacetimeMap ρ z) = z := by
    intro z hz
    exact Prod.ext rfl (hright z.1 hz z.2)
  exact (contDiffOn_inverse_of_contDiffOn hs hs hforward hbackward hmap
    hidentity hinv).snd

/-- The inverse is jointly smooth from the forward path, continuity, inverse law and unit Jacobian. -/
theorem smoothVelocityOn_inverse {T : ℝ} (hT : 0 < T) {η ρ : Velocity}
    (hη : SmoothVelocityOn T η)
    (hρ : ContinuousOn (fun z : ℝ × Vec => ρ z.1 z.2) (finiteSpacetime T))
    (hright : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, η t (ρ t x) = x)
    (hdet : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, (deformationGradient η t a).det = 1) :
    SmoothVelocityOn T ρ :=
  smoothVelocityOn_inverse_of_isInvertible hT hη hρ hright
    (flowSpacetimeMap_fderivWithin_isInvertible hT hη hdet)

/-- Assembly of the path record after deriving inverse regularity. -/
theorem materialPathOn_of_smooth_inverse_data {T : ℝ} (hT : 0 < T) {η ρ : Velocity}
    (hη : SmoothVelocityOn T η)
    (hρ : ContinuousOn (fun z : ℝ × Vec => ρ z.1 z.2) (finiteSpacetime T))
    (hleft : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, ρ t (η t a) = a)
    (hright : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, η t (ρ t x) = x)
    (hlattice : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, ∀ i : Fin 3,
      η t (a + unitVector i) = η t a + unitVector i)
    (hinitial : η 0 = fun a => a)
    (hdet : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec, (deformationGradient η t a).det = 1) :
    MaterialPathOn T η ρ where
  smooth := hη
  inverse_smooth := smoothVelocityOn_inverse hT hη hρ hright hdet
  left_inverse := hleft
  right_inverse := hright
  lattice_equivariant := hlattice
  initial_configuration := hinitial
  determinant_one := hdet

end

end ClassicalMechanicsAssembly
