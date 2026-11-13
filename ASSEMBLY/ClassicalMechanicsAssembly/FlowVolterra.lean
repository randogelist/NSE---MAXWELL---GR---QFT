import ClassicalMechanicsAssembly.FlowBanach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Concrete Volterra operator on continuous paths

The integral is the actual Bochner interval integral. Factorial bounds are
proved from a uniform bound on the continuous coefficient, and are not an
operator-theoretic admission. All statements hold on an arbitrary finite
interval, without a smallness condition on K*T.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set MeasureTheory intervalIntegral
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : ℝ}

/-- Total extension used only to write an ordinary real interval integral. -/
def flowPathExtend (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E)) : ℝ → E :=
  fun t => γ (projIcc 0 T hT t)

theorem flowPathExtend_continuous (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E)) :
    Continuous (flowPathExtend hT γ) :=
  γ.continuous.comp continuous_projIcc

@[simp]
theorem flowPathExtend_of_mem (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    flowPathExtend hT γ t = γ ⟨t, ht⟩ := by
  simp only [flowPathExtend, projIcc_of_mem hT ht]

def flowPathPrimitiveMap (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E)) :
    C(Icc (0 : ℝ) T, E) :=
  ⟨fun t => ∫ r in (0 : ℝ)..(t : ℝ), flowPathExtend hT γ r,
    (intervalIntegral.continuous_primitive
      (fun a b => (flowPathExtend_continuous hT γ).intervalIntegrable a b) 0).comp
      continuous_subtype_val⟩

@[simp]
theorem flowPathPrimitiveMap_apply (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E))
    (t : Icc (0 : ℝ) T) :
    flowPathPrimitiveMap hT γ t = ∫ r in (0 : ℝ)..(t : ℝ), flowPathExtend hT γ r := rfl

def flowPathPrimitiveLinear (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, E) →ₗ[ℝ] C(Icc (0 : ℝ) T, E) where
  toFun := flowPathPrimitiveMap hT
  map_add' γ δ := by
    ext t
    exact intervalIntegral.integral_add
      ((flowPathExtend_continuous hT γ).intervalIntegrable 0 t)
      ((flowPathExtend_continuous hT δ).intervalIntegrable 0 t)
  map_smul' c γ := by
    ext t
    exact intervalIntegral.integral_smul c (flowPathExtend hT γ)

theorem flowPathPrimitiveLinear_bound (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E)) :
    ‖flowPathPrimitiveLinear hT γ‖ ≤ T * ‖γ‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg _))).mpr
  intro t
  have hb : ‖∫ r in (0 : ℝ)..(t : ℝ), flowPathExtend hT γ r‖ ≤ ‖γ‖ * |(t : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun r _ => γ.norm_coe_le_norm (projIcc 0 T hT r))
  change ‖∫ r in (0 : ℝ)..(t : ℝ), flowPathExtend hT γ r‖ ≤ T * ‖γ‖
  rw [sub_zero, abs_of_nonneg t.property.1] at hb
  exact hb.trans (by nlinarith [t.property.2, norm_nonneg γ])

/-- Actual bounded linear time integration on continuous paths. -/
def flowPathPrimitive (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, E) →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  (flowPathPrimitiveLinear hT).mkContinuous T (flowPathPrimitiveLinear_bound hT)

@[simp]
theorem flowPathPrimitive_apply (hT : 0 ≤ T) (γ : C(Icc (0 : ℝ) T, E))
    (t : Icc (0 : ℝ) T) :
    flowPathPrimitive hT γ t = ∫ r in (0 : ℝ)..(t : ℝ), flowPathExtend hT γ r := rfl

theorem flowPathPrimitive_norm_le (hT : 0 ≤ T) :
    ‖flowPathPrimitive (E := E) hT‖ ≤ T :=
  (flowPathPrimitiveLinear hT).mkContinuous_norm_le hT (flowPathPrimitiveLinear_bound hT)

/-- Volterra linearization with its actual continuous coefficient. -/
def flowVolterra (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    C(Icc (0 : ℝ) T, E) →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  flowPathPrimitive hT ∘L flowPathMultiplication A

@[simp]
theorem flowVolterra_apply (hT : 0 ≤ T) (A : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (γ : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T) :
    flowVolterra hT A γ t =
      ∫ r in (0 : ℝ)..(t : ℝ),
        A (projIcc 0 T hT r) (γ (projIcc 0 T hT r)) := rfl

/-- The factorial estimate is proved pointwise before taking the supremum norm. -/
theorem flowVolterra_pow_apply_bound (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (K : ℝ≥0)
    (hA : ∀ t : Icc (0 : ℝ) T, ‖A t‖ ≤ K)
    (γ : C(Icc (0 : ℝ) T, E)) (n : ℕ) (t : Icc (0 : ℝ) T) :
    ‖((flowVolterra hT A) ^ n) γ t‖ ≤
      (((K : ℝ) * (t : ℝ)) ^ n / (n.factorial : ℝ)) * ‖γ‖ := by
  induction n generalizing t with
  | zero => simpa using γ.norm_coe_le_norm t
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, flowVolterra_apply]
    let g : ℝ → ℝ := fun r => (K : ℝ) ^ (n + 1) * r ^ n / (n.factorial : ℝ) * ‖γ‖
    have hg : IntervalIntegrable g volume 0 (t : ℝ) :=
      (show Continuous g by fun_prop).intervalIntegrable 0 t
    have hb :
        ‖∫ r in (0 : ℝ)..(t : ℝ), A (projIcc 0 T hT r)
          (((flowVolterra hT A) ^ n) γ (projIcc 0 T hT r))‖ ≤
          ∫ r in (0 : ℝ)..(t : ℝ), g r := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.property.1 _ hg
      apply Filter.Eventually.of_forall
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.trans t.property.2⟩
      rw [projIcc_of_mem hT hrT]
      calc
        ‖A ⟨r, hrT⟩ (((flowVolterra hT A) ^ n) γ ⟨r, hrT⟩)‖
            ≤ ‖A ⟨r, hrT⟩‖ * ‖((flowVolterra hT A) ^ n) γ ⟨r, hrT⟩‖ :=
          (A ⟨r, hrT⟩).le_opNorm _
        _ ≤ (K : ℝ) * ((((K : ℝ) * r) ^ n / (n.factorial : ℝ)) * ‖γ‖) :=
          mul_le_mul (hA _) (ih ⟨r, hrT⟩) (norm_nonneg _) K.coe_nonneg
        _ = g r := by dsimp [g]; rw [mul_pow, pow_succ]; ring
    apply hb.trans_eq
    dsimp [g]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring

/-- Concrete operator-norm factorial estimate, with no smallness assumption. -/
theorem flowVolterra_pow_norm_bound (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (K : ℝ≥0)
    (hA : ∀ t : Icc (0 : ℝ) T, ‖A t‖ ≤ K) (n : ℕ) :
    ‖(flowVolterra hT A) ^ n‖ ≤ ((K : ℝ) * T) ^ n / (n.factorial : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro γ
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  apply (flowVolterra_pow_apply_bound hT A K hA γ n t).trans
  gcongr
  exact t.property.2

/-- The actual Volterra residual derivative is invertible on every finite slab. -/
theorem one_sub_flowVolterra_isInvertible (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (K : ℝ≥0)
    (hA : ∀ t : Icc (0 : ℝ) T, ‖A t‖ ≤ K) :
    (1 - flowVolterra hT A).IsInvertible :=
  one_sub_operator_isInvertible_of_factorial_bound (flowVolterra hT A) ((K : ℝ) * T)
    (flowVolterra_pow_norm_bound hT A K hA)

/-- Compactness supplies the coefficient bound; continuity alone suffices. -/
theorem one_sub_flowVolterra_isInvertible_of_continuous_coefficient (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    (1 - flowVolterra hT A).IsInvertible :=
  one_sub_flowVolterra_isInvertible hT A ‖A‖₊ (fun t => A.norm_coe_le_norm t)

end

end ClassicalMechanicsAssembly
