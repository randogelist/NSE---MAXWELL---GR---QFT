import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Abel

/-!
Banach-space edges of the finite-slab flow construction.

The factorial estimate is an explicit hypothesis: this module does not identify
an arbitrary operator with the Volterra operator. Likewise, the superposition
smoothness and residual derivative needed by the implicit-function step remain
explicit until the concrete path-space estimates are discharged.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open scoped Topology ContDiff NNReal
open Filter Set

noncomputable section

section OperatorSeries

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Factorial power bounds imply convergence in the operator norm. -/
theorem summable_operator_powers_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    Summable (fun n : ℕ => L ^ n) := by
  exact (Real.summable_pow_div_factorial C).of_norm_bounded hbound

/-- The convergent power series is a two-sided inverse; no smallness condition is used. -/
theorem operator_series_inverse_identities_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    (1 - L) * (∑' n : ℕ, L ^ n) = 1 ∧
      (∑' n : ℕ, L ^ n) * (1 - L) = 1 := by
  have hs := summable_operator_powers_of_factorial_bound L C hbound
  exact ⟨hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩

/-- The actual operator `1 - L` is a Banach-space isomorphism. -/
theorem one_sub_operator_isInvertible_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    (1 - L).IsInvertible := by
  obtain ⟨hleft, hright⟩ :=
    operator_series_inverse_identities_of_factorial_bound L C hbound
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := ∑' n : ℕ, L ^ n)
  · change (1 - L) * (∑' n : ℕ, L ^ n) = 1
    exact hleft
  · change (∑' n : ℕ, L ^ n) * (1 - L) = 1
    exact hright

/-- Identification of the library's total inverse with the convergent series. -/
theorem operator_inverse_eq_tsum_of_factorial_bound
    (L : B →L[ℝ] B) (C : ℝ)
    (hbound : ∀ n : ℕ, ‖L ^ n‖ ≤ C ^ n / (n.factorial : ℝ)) :
    (1 - L).inverse = ∑' n : ℕ, L ^ n := by
  obtain ⟨hleft, hright⟩ :=
    operator_series_inverse_identities_of_factorial_bound L C hbound
  apply ContinuousLinearMap.inverse_eq
  · change (1 - L) * (∑' n : ℕ, L ^ n) = 1
    exact hleft
  · change (∑' n : ℕ, L ^ n) * (1 - L) = 1
    exact hright

end OperatorSeries

section ImplicitBranch

variable {E B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- A chosen unique root agrees locally with the smooth implicit branch.
No continuity or differentiability of the chosen root is assumed. -/
theorem contDiff_of_unique_implicit_branch
    (Φ : E × B → B) (Γ : E → B)
    (hΦ : ContDiff ℝ ∞ Φ)
    (hroot : ∀ a, Φ (a, Γ a) = 0)
    (hunique : ∀ a b, Φ (a, b) = 0 → b = Γ a)
    (hinv : ∀ a, (fderiv ℝ Φ (a, Γ a) ∘L
      ContinuousLinearMap.inr ℝ E B).IsInvertible) :
    ContDiff ℝ ∞ Γ := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  have hc : ContDiffAt ℝ ∞ Φ (a, Γ a) := hΦ.contDiffAt
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hψ := hc.contDiffAt_implicitFunction hn (hinv a)
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hc.eventually_apply_implicitFunction hn (hinv a)] with b hb
  exact (hunique b _ (by simpa only [hroot a] using hb)).symm

/-- Volterra/IFT composition with the actual residual partial derivative exposed.
The two unresolved analytic inputs are residual smoothness and factorial bounds. -/
theorem contDiff_of_unique_volterra_residual
    (Φ : E × B → B) (Γ : E → B) (L : E → B →L[ℝ] B) (C : E → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ)
    (hroot : ∀ a, Φ (a, Γ a) = 0)
    (hunique : ∀ a b, Φ (a, b) = 0 → b = Γ a)
    (hpartial : ∀ a, fderiv ℝ Φ (a, Γ a) ∘L
      ContinuousLinearMap.inr ℝ E B = 1 - L a)
    (hbound : ∀ a (n : ℕ), ‖L a ^ n‖ ≤ C a ^ n / (n.factorial : ℝ)) :
    ContDiff ℝ ∞ Γ := by
  apply contDiff_of_unique_implicit_branch Φ Γ hΦ hroot hunique
  intro a
  rw [hpartial a]
  exact one_sub_operator_isInvertible_of_factorial_bound (L a) (C a) (hbound a)

end ImplicitBranch

section Superposition

variable {I E : Type*} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual path superposition on a compact time domain. -/
def flowPathSuperposition (u : C(I × E, E)) (γ : C(I, E)) : C(I, E) :=
  u.comp ((ContinuousMap.id I).prodMk γ)

@[simp]
theorem flowPathSuperposition_apply (u : C(I × E, E)) (γ : C(I, E)) (t : I) :
    flowPathSuperposition u γ t = u (t, γ t) := rfl

/-- Uniform spatial Lipschitz control passes to the actual sup-norm path map. -/
theorem flowPathSuperposition_lipschitz (u : C(I × E, E)) (K : ℝ≥0)
    (hu : ∀ t : I, LipschitzWith K (fun x => u (t, x))) :
    LipschitzWith K (flowPathSuperposition u) := by
  apply LipschitzWith.of_dist_le_mul
  intro γ δ
  apply (ContinuousMap.dist_le (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro t
  exact ((hu t).dist_le_mul (γ t) (δ t)).trans
    (mul_le_mul_of_nonneg_left
      (ContinuousMap.dist_apply_le_dist (f := γ) (g := δ) t) K.coe_nonneg)

end Superposition

section SuperpositionCalculus

variable {I E F : Type*} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A globally Lipschitz spatial derivative gives a uniform quadratic Taylor bound.
The constant is deliberately non-sharp; no time differentiability is required. -/
theorem flow_quadratic_remainder_of_lipschitz_derivative
    (u : E → F) (A : E → E →L[ℝ] F) (K : ℝ≥0)
    (hder : ∀ x, HasFDerivAt u (A x) x) (hLip : LipschitzWith K A) (x h : E) :
    ‖u (x + h) - u x - A x h‖ ≤ (K : ℝ) * ‖h‖ ^ 2 := by
  have hd : ∀ y ∈ segment ℝ x (x + h),
      HasFDerivWithinAt (fun z => u z - A x z) (A y - A x)
        (segment ℝ x (x + h)) y := by
    intro y hy
    exact ((hder y).sub (A x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ y ∈ segment ℝ x (x + h), ‖A y - A x‖ ≤ (K : ℝ) * ‖h‖ := by
    intro y hy
    have hnorm : ‖y - x‖ ≤ ‖h‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le_of_mem_segment hy
    exact (hLip.norm_sub_le y x).trans
      (mul_le_mul_of_nonneg_left hnorm K.coe_nonneg)
  have hb := (convex_segment x (x + h)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hbound (left_mem_segment ℝ x (x + h)) (right_mem_segment ℝ x (x + h))
  have heq : (u (x + h) - A x (x + h)) - (u x - A x x) =
      u (x + h) - u x - A x h := by
    rw [map_add]
    abel
  rw [heq, add_sub_cancel_left] at hb
  simpa only [pow_two, mul_assoc] using hb

/-- Pointwise multiplication by a continuous operator-valued coefficient. -/
def flowPathMultiplicationLinear (A : C(I, E →L[ℝ] F)) :
    C(I, E) →ₗ[ℝ] C(I, F) where
  toFun h := ⟨fun t => A t (h t), A.continuous.clm_apply h.continuous⟩
  map_add' h k := by
    ext t
    exact (A t).map_add (h t) (k t)
  map_smul' c h := by
    ext t
    exact (A t).map_smul c (h t)

theorem flowPathMultiplicationLinear_bound (A : C(I, E →L[ℝ] F)) (h : C(I, E)) :
    ‖flowPathMultiplicationLinear A h‖ ≤ ‖A‖ * ‖h‖ := by
  apply ((flowPathMultiplicationLinear A h).norm_le
    (mul_nonneg (norm_nonneg A) (norm_nonneg h))).mpr
  intro t
  exact ((A t).le_opNorm (h t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

/-- Multiplication is a bounded linear operator on the sup-norm path spaces. -/
def flowPathMultiplication (A : C(I, E →L[ℝ] F)) :
    C(I, E) →L[ℝ] C(I, F) :=
  (flowPathMultiplicationLinear A).mkContinuous ‖A‖
    (flowPathMultiplicationLinear_bound A)

@[simp]
theorem flowPathMultiplication_apply (A : C(I, E →L[ℝ] F)) (h : C(I, E)) (t : I) :
    flowPathMultiplication A h t = A t (h t) := rfl

theorem flowPathMultiplication_norm_le (A : C(I, E →L[ℝ] F)) :
    ‖flowPathMultiplication A‖ ≤ ‖A‖ :=
  (flowPathMultiplicationLinear A).mkContinuous_norm_le (norm_nonneg A)
    (flowPathMultiplicationLinear_bound A)

/-- The coefficient-to-operator construction is itself linear. -/
def flowPathMultiplicationLiftLinear :
    C(I, E →L[ℝ] F) →ₗ[ℝ] (C(I, E) →L[ℝ] C(I, F)) where
  toFun := flowPathMultiplication
  map_add' A B := by
    ext h t
    rfl
  map_smul' c A := by
    ext h t
    rfl

/-- Continuous dependence of the multiplication operator on its coefficient. -/
def flowPathMultiplicationLift :
    C(I, E →L[ℝ] F) →L[ℝ] (C(I, E) →L[ℝ] C(I, F)) :=
  (flowPathMultiplicationLiftLinear (I := I) (E := E) (F := F)).mkContinuous 1
    (fun (A : C(I, E →L[ℝ] F)) => by
      change ‖flowPathMultiplication A‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact flowPathMultiplication_norm_le A)

@[simp]
theorem flowPathMultiplicationLift_apply (A : C(I, E →L[ℝ] F)) :
    flowPathMultiplicationLift A = flowPathMultiplication A := rfl

/-- Postcomposition expressed directly in the sup-norm path-space structures. -/
def flowPathPostcomposition (L : E →L[ℝ] F) : C(I, E) →L[ℝ] C(I, F) :=
  flowPathMultiplication (ContinuousMap.const I L)

@[simp]
theorem flowPathPostcomposition_apply (L : E →L[ℝ] F) (γ : C(I, E)) (t : I) :
    flowPathPostcomposition L γ t = L (γ t) := rfl

/-- Superposition with different source and target Banach spaces. -/
def flowPathSuperpositionTo (u : C(I × E, F)) (γ : C(I, E)) : C(I, F) :=
  u.comp ((ContinuousMap.id I).prodMk γ)

@[simp]
theorem flowPathSuperpositionTo_apply (u : C(I × E, F)) (γ : C(I, E)) (t : I) :
    flowPathSuperpositionTo u γ t = u (t, γ t) := rfl

/-- The actual pointwise derivative candidate, acting on continuous paths. -/
def flowPathSuperpositionDerivative (A : C(I × E, E →L[ℝ] F)) (γ : C(I, E)) :
    C(I, E) →L[ℝ] C(I, F) :=
  flowPathMultiplication (flowPathSuperpositionTo A γ)

@[simp]
theorem flowPathSuperpositionDerivative_apply
    (A : C(I × E, E →L[ℝ] F)) (γ h : C(I, E)) (t : I) :
    flowPathSuperpositionDerivative A γ h t = A (t, γ t) (h t) := rfl

/-- A uniform pointwise quadratic remainder gives a sup-norm quadratic remainder. -/
theorem flowPathSuperposition_remainder_bound
    (u : C(I × E, F)) (A : C(I × E, E →L[ℝ] F)) (M : ℝ) (hM : 0 ≤ M)
    (htaylor : ∀ (t : I) (x h : E),
      ‖u (t, x + h) - u (t, x) - A (t, x) h‖ ≤ M * ‖h‖ ^ 2)
    (γ h : C(I, E)) :
    ‖flowPathSuperpositionTo u (γ + h) - flowPathSuperpositionTo u γ -
      flowPathSuperpositionDerivative A γ h‖ ≤ M * ‖h‖ ^ 2 := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hM (sq_nonneg _))).mpr
  intro t
  change ‖u (t, γ t + h t) - u (t, γ t) - A (t, γ t) (h t)‖ ≤ M * ‖h‖ ^ 2
  exact (htaylor t (γ t) (h t)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (h.norm_coe_le_norm t) 2) hM)

/-- Differentiability of the actual path superposition, without a path derivative assumption. -/
theorem flowPathSuperposition_hasFDerivAt
    (u : C(I × E, F)) (A : C(I × E, E →L[ℝ] F)) (M : ℝ) (hM : 0 ≤ M)
    (htaylor : ∀ (t : I) (x h : E),
      ‖u (t, x + h) - u (t, x) - A (t, x) h‖ ≤ M * ‖h‖ ^ 2)
    (γ : C(I, E)) :
    HasFDerivAt (flowPathSuperpositionTo u) (flowPathSuperpositionDerivative A γ) γ := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  have hb : (fun h : C(I, E) =>
      flowPathSuperpositionTo u (γ + h) - flowPathSuperpositionTo u γ -
        flowPathSuperpositionDerivative A γ h) =O[𝓝 0]
      (fun h : C(I, E) => ‖h‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound M
    apply Filter.Eventually.of_forall
    intro h
    simpa only [norm_pow, norm_norm] using
      flowPathSuperposition_remainder_bound u A M hM htaylor γ h
  exact hb.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by decide : 1 < 2))

/-- Actual superposition differentiation from spatial derivatives and uniform Lipschitz control. -/
theorem flowPathSuperposition_hasFDerivAt_of_lipschitz_derivative
    (u : C(I × E, F)) (A : C(I × E, E →L[ℝ] F)) (K : ℝ≥0)
    (hder : ∀ (t : I) (x : E), HasFDerivAt (fun y => u (t, y)) (A (t, x)) x)
    (hLip : ∀ t : I, LipschitzWith K (fun x => A (t, x)))
    (γ : C(I, E)) :
    HasFDerivAt (flowPathSuperpositionTo u) (flowPathSuperpositionDerivative A γ) γ := by
  apply flowPathSuperposition_hasFDerivAt u A K K.coe_nonneg
  intro t x h
  exact flow_quadratic_remainder_of_lipschitz_derivative
    (fun y => u (t, y)) (fun y => A (t, y)) K (hder t) (hLip t) x h

/-- One full smoothness step: regular coefficient superposition yields a regular derivative. -/
theorem flowPathSuperposition_contDiff_succ
    (u : C(I × E, F)) (A : C(I × E, E →L[ℝ] F)) (M : ℝ) (hM : 0 ≤ M)
    (htaylor : ∀ (t : I) (x h : E),
      ‖u (t, x + h) - u (t, x) - A (t, x) h‖ ≤ M * ‖h‖ ^ 2)
    (n : ℕ) (hA : ContDiff ℝ n (flowPathSuperpositionTo A)) :
    ContDiff ℝ (n + 1) (flowPathSuperpositionTo u) := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨flowPathSuperpositionDerivative A, ?_, ?_⟩
  · have heq : flowPathSuperpositionDerivative A =
        (flowPathMultiplicationLift (I := I) (E := E) (F := F)) ∘
          flowPathSuperpositionTo A := by
      funext γ
      ext h t
      rfl
    rw [heq]
    exact (flowPathMultiplicationLift (I := I) (E := E) (F := F)).contDiff.comp hA
  · exact flowPathSuperposition_hasFDerivAt u A M hM htaylor

end SuperpositionCalculus

section SuperpositionTower

variable {I E : Type*} [TopologicalSpace I] [CompactSpace I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform spatial Taylor data of every order imply smoothness of the actual
superposition map. The tower may use multilinear tensors and their currying maps;
no differentiability of any path-space map is an input. -/
theorem flowPathSuperposition_contDiff_of_taylor_tower
    (F : ℕ → Type*) [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    (u : ∀ n, C(I × E, F n))
    (curry : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (M : ℕ → ℝ≥0)
    (htaylor : ∀ (n : ℕ) (t : I) (x h : E),
      ‖u n (t, x + h) - u n (t, x) - curry n (u (n + 1) (t, x)) h‖ ≤
        (M n : ℝ) * ‖h‖ ^ 2) :
    ∀ n, ContDiff ℝ ∞ (flowPathSuperpositionTo (u n)) := by
  let A : ∀ n, C(I × E, E →L[ℝ] F n) := fun n =>
    (curry n).compLeftContinuous ℝ (I × E) (u (n + 1))
  have hd : ∀ (n : ℕ) (γ : C(I, E)),
      HasFDerivAt (flowPathSuperpositionTo (u n))
        (flowPathSuperpositionDerivative (A n) γ) γ := by
    intro n γ
    exact flowPathSuperposition_hasFDerivAt (u n) (A n) (M n) (M n).coe_nonneg
      (htaylor n) γ
  have hfinite : ∀ m : ℕ, ∀ n : ℕ, ContDiff ℝ m (flowPathSuperpositionTo (u n)) := by
    intro m
    induction m with
    | zero =>
      intro n
      apply contDiff_zero.mpr
      exact (show Differentiable ℝ (flowPathSuperpositionTo (u n)) from
        fun γ => (hd n γ).differentiableAt).continuous
    | succ m ih =>
      intro n
      apply flowPathSuperposition_contDiff_succ (u n) (A n) (M n) (M n).coe_nonneg
        (htaylor n) m
      change ContDiff ℝ m (fun γ =>
        flowPathPostcomposition (curry n) (flowPathSuperpositionTo (u (n + 1)) γ))
      exact (flowPathPostcomposition (I := I) (curry n)).contDiff.comp (ih (n + 1))
  intro n
  exact contDiff_infty.mpr (fun m => hfinite m n)

/-- A jointly continuous spatial derivative tower with uniform Lipschitz
coefficient bounds supplies the Taylor data and hence the full C-infinity map. -/
theorem flowPathSuperposition_contDiff_of_spatial_tower
    (F : ℕ → Type*) [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    (u : ∀ n, C(I × E, F n))
    (curry : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (K : ℕ → ℝ≥0)
    (hder : ∀ (n : ℕ) (t : I) (x : E), HasFDerivAt (fun y => u n (t, y))
      (curry n (u (n + 1) (t, x))) x)
    (hLip : ∀ (n : ℕ) (t : I),
      LipschitzWith (K n) (fun x => curry n (u (n + 1) (t, x)))) :
    ∀ n, ContDiff ℝ ∞ (flowPathSuperpositionTo (u n)) := by
  apply flowPathSuperposition_contDiff_of_taylor_tower F u curry K
  intro n t x h
  exact flow_quadratic_remainder_of_lipschitz_derivative
    (fun y => u n (t, y)) (fun y => curry n (u (n + 1) (t, y)))
    (K n) (hder n t) (hLip n t) x h

end SuperpositionTower

end

end ClassicalMechanicsAssembly
