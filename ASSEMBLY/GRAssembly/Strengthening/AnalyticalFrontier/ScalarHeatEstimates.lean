import GRAssembly.Strengthening.AnalyticalFrontier.FixedSectorGeometry

/-!
Scalar completion-of-the-square estimates used by the weighted heat
semigroup bound. No Fourier summation or NSE premise occurs here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped Topology

namespace NSEGR.Strengthening
noncomputable section

theorem analyticalHeatExponent_le_quarter
    {ν T y : ℝ} {z : ℂ}
    (hν : 0 < ν) (hz : z ∈ analyticalFixedSector T) (hy : 0 ≤ y) :
    Real.sqrt (ν * z.re) * y - ν * z.re * y ^ 2 ≤ (1 : ℝ) / 4 := by
  have hzre : 0 ≤ z.re := (analyticalFixedSector_re_pos hz).le
  have hνz : 0 ≤ ν * z.re := mul_nonneg hν.le hzre
  have hsqrt : (Real.sqrt (ν * z.re)) ^ 2 = ν * z.re :=
    Real.sq_sqrt hνz
  have hsq : 0 ≤ (Real.sqrt (ν * z.re) * y - (1 : ℝ) / 2) ^ 2 :=
    sq_nonneg _
  nlinarith

theorem analyticalHeatExp_le_exp_quarter
    {ν T y : ℝ} {z : ℂ}
    (hν : 0 < ν) (hz : z ∈ analyticalFixedSector T) (hy : 0 ≤ y) :
    Real.exp (Real.sqrt (ν * z.re) * y - ν * z.re * y ^ 2) ≤
      Real.exp ((1 : ℝ) / 4) :=
  Real.exp_le_exp.mpr (analyticalHeatExponent_le_quarter hν hz hy)

/-- The exact scalar heat estimate required by the weighted Fourier sum. -/
def ANALYTICAL_SCALAR_HEAT_CHECKPOINT : Prop :=
  ∀ (ν T y : ℝ) (z : ℂ),
    0 < ν → z ∈ analyticalFixedSector T → 0 ≤ y →
      Real.exp (Real.sqrt (ν * z.re) * y - ν * z.re * y ^ 2) ≤
        Real.exp ((1 : ℝ) / 4)

theorem ANALYTICAL_SCALAR_HEAT_CHECKPOINT_NATIVE :
    ANALYTICAL_SCALAR_HEAT_CHECKPOINT := by
  intro ν T y z hν hz hy
  exact analyticalHeatExp_le_exp_quarter hν hz hy

end
end NSEGR.Strengthening
