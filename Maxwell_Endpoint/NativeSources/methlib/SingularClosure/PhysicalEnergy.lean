import SingularClosure.FiniteParseval
import SingularClosure.GalerkinEnergyIntegral

/-!
# Frozen endpoint 4: literal physical Galerkin energy identity

Both spatial energies and dissipation are integrals over the physical unit
cube. The initial field is the actual Fourier cutoff of the input datum.
Finite-time integrability is proved from the concrete coefficient trajectory.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

def physicalDissipation (v : Field) : ℝ :=
  ∫ x in unitCube, gradientSquareDensity v x

theorem GalerkinSolution.physicalDissipation_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    physicalDissipation (g.velocity t) = coefficientDissipation N (g.coeff t) :=
  FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N (g.coeff t) (g.real_symmetry t ht)

theorem GalerkinSolution.physicalEnergy_eq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    physicalEnergy (g.velocity t) = coefficientEnergy N (g.coeff t) :=
  FINITE_PHYSICAL_ENERGY_PARSEVAL N (g.coeff t) (g.real_symmetry t ht)

theorem GalerkinSolution.velocity_initial
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    g.velocity 0 = finiteSynthesis N (datumFourierCoeff a) := by
  have hc : g.coeff 0 = cutoffCoeff N (datumFourierCoeff a) := by
    funext k i
    exact g.initial k i
  change finiteSynthesis N (g.coeff 0) = _
  rw [hc, finiteSynthesis_cutoffCoeff]

theorem GALERKIN_ENERGY_IDENTITY
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => physicalDissipation (g.velocity t)) volume 0 T ∧
      physicalEnergy (g.velocity T) +
        2 * ν * (∫ t in (0 : ℝ)..T, physicalDissipation (g.velocity t)) =
          physicalEnergy (finiteSynthesis N (datumFourierCoeff a)) := by
  have hD : EqOn (fun t => physicalDissipation (g.velocity t))
      (fun t => coefficientDissipation N (g.coeff t)) (Icc 0 T) := by
    intro t ht
    exact g.physicalDissipation_eq ht.1
  have hI : (∫ t in (0 : ℝ)..T, physicalDissipation (g.velocity t)) =
      ∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t) := by
    apply intervalIntegral.integral_congr
    simpa only [uIcc_of_le hT] using hD
  constructor
  · apply (g.coefficientDissipation_intervalIntegrable hT).congr
    intro t ht
    have hh : t ∈ Ioc (0 : ℝ) T := by simpa only [uIoc_of_le hT] using ht
    exact (g.physicalDissipation_eq hh.1.le).symm
  · rw [g.physicalEnergy_eq hT, hI, g.coefficientEnergy_integral_identity hT]
    rw [← g.physicalEnergy_eq (le_refl (0 : ℝ)), g.velocity_initial]

end

end SingularClosure
