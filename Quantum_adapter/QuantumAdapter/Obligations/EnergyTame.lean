import QuantumAdapter.Obligations.EnergyCommutator
import QuantumAdapter.Obligations.EnergyViscous
import QuantumAdapter.Obligations.ScalarGrowth
import QuantumAdapter.Assembly.PacketEstimates

/-! Exact native H3 growth, with no analytic certificate premise. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem h3Pairing_drift_le {ν : ℝ} (hν : 0 ≤ ν) (N : ℕ) (q : Phase N) :
    h3Pairing N q (drift ν N q) ≤ 512 * gradientObservable q * energy3 N q := by
  rw [drift_eq_inviscid_sub_laplacian, ← bilinearConvection_self,
    sub_eq_add_neg, ← neg_smul, h3Pairing_add_right, h3Pairing_smul_right]
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hν)
    (h3Pairing_laplacian_nonneg N q)
  have hbound := h3Pairing_convection_le N q
  linarith

/-- P5: the exact native norm, prefactor one, and a uniform explicit constant. -/
theorem phaseFlow_h3_tame {ν : ℝ} (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (energy3 N (F.map N t q)) ≤ Real.sqrt (energy3 N q) *
      Real.exp (512 * Assembly.orbitGradientCost F N q t) := by
  let y : ℝ → ℝ := fun s => energy3 N (F.map N s q)
  let dy : ℝ → ℝ := fun s => 2 * h3Pairing N (F.map N s q) (drift ν N (F.map N s q))
  let g : ℝ → ℝ := fun s => gradientObservable (F.map N s q)
  have hg : Continuous g := (Assembly.continuous_gradientObservable N).comp
    (Assembly.phaseFlow_orbit_continuous F N q)
  have hd (s : ℝ) : HasDerivAt y (dy s) s := phaseFlow_energy3_hasDerivAt F N q s
  have hb := sqrt_energy_growth_bound y dy g 512 hg hd
    (fun s hs => energy3_nonneg N (F.map N s q)) (by
      intro s hs
      have hh := h3Pairing_drift_le hν N (F.map N s q)
      change 2 * h3Pairing N _ _ ≤ (2 * 512) * g s * y s
      dsimp [g, y]
      linarith) ht
  simpa only [y, g, F.map_zero, Assembly.orbitGradientCost] using hb

end
end QuantumAdapter.Obligations
