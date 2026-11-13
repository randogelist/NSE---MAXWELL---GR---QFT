import QuantumAdapter.Obligations.EnergyConvection
import QuantumAdapter.Obligations.TensorInterpolation

/-! Absolute physical estimates for the actual trilinear phase pairing. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem synthesis_trilinear_pointwise (N : ℕ) (q a b : Phase N) (x : Vec) :
    |inner ℝ (synthesis q x) (mixedConvection (synthesis a) (synthesis b) x)| ≤
      ‖synthesis q x‖ * ‖synthesis a x‖ * Real.sqrt (gradientSquare b x) := by
  have hd := synthesis_directionalDerivative_norm_le_pointwise N b x (synthesis a x)
  change ‖mixedConvection (synthesis a) (synthesis b) x‖ ≤ _ at hd
  calc
    _ ≤ ‖synthesis q x‖ * ‖mixedConvection (synthesis a) (synthesis b) x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖synthesis q x‖ * (Real.sqrt (gradientSquare b x) * ‖synthesis a x‖) :=
      mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = _ := by ring

theorem abs_inner_bilinearConvection_le_integral (N : ℕ) (q a b : Phase N) :
    |inner ℝ q (bilinearConvection N a b)| ≤
      ∫ x in unitCube,
        ‖synthesis q x‖ * ‖synthesis a x‖ * Real.sqrt (gradientSquare b x) := by
  have hq := (synthesis_contDiff N q).continuous
  have ha := (synthesis_contDiff N a).continuous
  have hb := synthesis_contDiff N b
  have hm := mixedConvection_continuous _ _ ha hb
  have hi : IntegrableOn (fun x => |inner ℝ (synthesis q x)
      (mixedConvection (synthesis a) (synthesis b) x)|) unitCube :=
    (hq.inner hm).abs.continuousOn.integrableOn_compact isCompact_unitCube
  have hr := ((hq.norm.mul ha.norm).mul (synthesis_gradientSquare_continuous N b).sqrt).continuousOn.integrableOn_compact isCompact_unitCube
  rw [inner_bilinearConvection_eq_integral, abs_neg]
  calc
    _ ≤ ∫ x in unitCube,
        |inner ℝ (synthesis q x) (mixedConvection (synthesis a) (synthesis b) x)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x =>
          inner ℝ (synthesis q x) (mixedConvection (synthesis a) (synthesis b) x))
          (μ := volume.restrict unitCube))
    _ ≤ _ := integral_mono hi hr (fun x => synthesis_trilinear_pointwise N q a b x)

/-- Pointwise bounds on the three actual factors may be integrated directly. -/
theorem inner_bilinearConvection_le_of_pointwise (N : ℕ) (q a b : Phase N)
    (H : Vec → ℝ) (hH : Continuous H)
    (hbound : ∀ x, ‖synthesis q x‖ * ‖synthesis a x‖ *
      Real.sqrt (gradientSquare b x) ≤ H x) :
    inner ℝ q (bilinearConvection N a b) ≤ ∫ x in unitCube, H x := by
  have hq := (synthesis_contDiff N q).continuous
  have ha := (synthesis_contDiff N a).continuous
  have hr := ((hq.norm.mul ha.norm).mul (synthesis_gradientSquare_continuous N b).sqrt).continuousOn.integrableOn_compact isCompact_unitCube
  exact (le_abs_self _).trans ((abs_inner_bilinearConvection_le_integral N q a b).trans
    (integral_mono hr (hH.continuousOn.integrableOn_compact isCompact_unitCube) hbound))

end
end QuantumAdapter.Obligations
