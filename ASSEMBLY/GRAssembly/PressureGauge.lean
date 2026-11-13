import GRAdapter.ScalarCompatibility
import GRAdapter.FourierInversion
import GRAssembly.GaugePrimitive

/-!
GC21. Actual cancellation of a time-only pressure gauge against a double
primitive in the scalar completion. No scalar existence or Gaussian
uniqueness conclusion is inferred from this local calculation.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace NSEGR.Assembly
noncomputable section

theorem scalarHessian_sub_constant (f : ScalarField) (c : ℝ) :
    scalarHessian (fun x => f x - c) = scalarHessian f := by
  funext x i j
  simp only [scalarHessian, fderiv_sub_const]

theorem scalarLaplacian_sub_constant (f : ScalarField) (c : ℝ) :
    scalarLaplacian (fun x => f x - c) = scalarLaplacian f := by
  funext x
  simp only [scalarLaplacian, fderiv_sub_const]

theorem analytic_second_deriv_sub {f a : ℝ → ℝ} {t : ℝ}
    (hf : AnalyticAt ℝ f t) (ha : AnalyticAt ℝ a t) :
    deriv (deriv (fun s => f s - a s)) t =
      deriv (deriv f) t - deriv (deriv a) t := by
  have he : deriv (fun s => f s - a s) =ᶠ[𝓝 t]
      (fun s => deriv f s - deriv a s) := by
    filter_upwards [hf.eventually_analyticAt, ha.eventually_analyticAt] with s hfs has
    exact deriv_fun_sub hfs.differentiableAt has.differentiableAt
  rw [he.deriv_eq]
  exact deriv_fun_sub hf.deriv.differentiableAt ha.deriv.differentiableAt

theorem scalarLocalTimeDerivative_gauge_germ {ψ : Pressure} {a : ℝ → ℝ}
    {t : ℝ} {x : Vec} (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t, x))
    (ha : AnalyticAt ℝ a t) :
    (fun y => scalarLocalTimeDerivative (fun s z => ψ s z - a s) t y)
      =ᶠ[𝓝 x] (fun y => scalarLocalTimeDerivative ψ t y - deriv a t) := by
  have hs : ∀ᶠ y in 𝓝 x,
      AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t, y) :=
    (continuous_const.prodMk continuous_id).continuousAt.tendsto.eventually
      hψ.eventually_analyticAt
  filter_upwards [hs] with y hy
  exact deriv_fun_sub hy.curry_left.differentiableAt ha.differentiableAt

theorem gradient_scalarLocalTimeDerivative_gauge {ψ : Pressure} {a : ℝ → ℝ}
    {t : ℝ} {x : Vec} (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t, x))
    (ha : AnalyticAt ℝ a t) :
    gradient (scalarLocalTimeDerivative (fun s z => ψ s z - a s) t) x =
      gradient (scalarLocalTimeDerivative ψ t) x := by
  have he := (scalarLocalTimeDerivative_gauge_germ hψ ha).fderiv_eq (𝕜 := ℝ)
  unfold gradient
  rw [he, fderiv_sub_const]

theorem scalarSecondTimeDerivative_gauge {ψ : Pressure} {a : ℝ → ℝ}
    {t : ℝ} {x : Vec} (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t, x))
    (ha : AnalyticAt ℝ a t) :
    scalarLocalTimeDerivative (scalarLocalTimeDerivative
      (fun s z => ψ s z - a s)) t x =
      scalarLocalTimeDerivative (scalarLocalTimeDerivative ψ) t x -
        deriv (deriv a) t := by
  exact analytic_second_deriv_sub hψ.curry_left ha

/-- Pointwise cancellation in the actual full four-tensor, before trace reversal. -/
theorem source_plus_completion_pressure_gauge {ν ρ t : ℝ} {u : Velocity}
    {p ψ : Pressure} {a γ : ℝ → ℝ} {x : Vec}
    (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t, x))
    (ha : AnalyticAt ℝ a t) (ha2 : deriv (deriv a) t = γ t) :
    conservedSourceUpper ν ρ u (fun s y => p s y + γ s) t x +
      scalarCompletionUpper (fun s y => ψ s y - a s) t x =
    conservedSourceUpper ν ρ u p t x + scalarCompletionUpper ψ t x := by
  have hg := gradient_scalarLocalTimeDerivative_gauge hψ ha
  have ht := scalarSecondTimeDerivative_gauge hψ ha
  rw [ha2] at ht
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals
    simp only [Pi.add_apply, conservedSourceUpper, scalarCompletionUpper,
      boundaryBlock_time_time, boundaryBlock_time_space, boundaryBlock_space_time,
      boundaryBlock_space_space, scalarLaplacian_sub_constant,
      scalarHessian_sub_constant, hg, ht]
  all_goals ring

/-- GC21: the native completed boundary tensor is invariant under the gauge. -/
theorem completedBoundary_pressure_gauge {ν ρ t : ℝ} {u : Velocity}
    {p ψ : Pressure} {a γ : ℝ → ℝ} {x : Vec}
    (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t, x))
    (ha : AnalyticAt ℝ a t) (ha2 : deriv (deriv a) t = γ t) :
    completedBoundary ν ρ u (fun s y => p s y + γ s)
      (fun s y => ψ s y - a s) t x = completedBoundary ν ρ u p ψ t x := by
  unfold completedBoundary
  rw [source_plus_completion_pressure_gauge hψ ha ha2]

/-- The pressure-gauge correction exists from LI01 and preserves the actual
completed four-tensor as a joint germ. -/
theorem normalized_pressure_gauge_completion
    (input : LiteratureAnalyticCKInput) {ν ρ t0 : ℝ} {u : Velocity}
    {p ψ : Pressure} {γ : ℝ → ℝ} {x0 : Vec}
    (hψ : AnalyticAt ℝ (fun z : ℝ × Vec => ψ z.1 z.2) (t0, x0))
    (hγ : AnalyticAt ℝ γ t0) :
    ∃ a : ℝ → ℝ, AnalyticAt ℝ a t0 ∧ a t0 = 0 ∧ deriv a t0 = 0 ∧
      ∀ᶠ z in 𝓝 (t0, x0),
        completedBoundary ν ρ u (fun s y => p s y + γ s)
          (fun s y => ψ s y - a s) z.1 z.2 =
            completedBoundary ν ρ u p ψ z.1 z.2 := by
  obtain ⟨a, ha, ha0, ha1, ha2⟩ := analytic_double_primitive_of_literatureCK input hγ
  refine ⟨a, ha, ha0, ha1, ?_⟩
  have ht : ∀ᶠ z : ℝ × Vec in 𝓝 (t0, x0),
      AnalyticAt ℝ a z.1 ∧ deriv (deriv a) z.1 = γ z.1 :=
    continuous_fst.continuousAt.tendsto.eventually (ha.eventually_analyticAt.and ha2)
  filter_upwards [hψ.eventually_analyticAt, ht] with z hz hzt
  exact completedBoundary_pressure_gauge hz hzt.1 hzt.2

end
end NSEGR.Assembly
