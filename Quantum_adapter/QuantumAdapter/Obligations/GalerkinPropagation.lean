import QuantumAdapter.Obligations.GalerkinEnergyEstimates
import QuantumAdapter.Obligations.GalerkinWeightedPairing
import QuantumAdapter.Obligations.FiniteGrowth
import QuantumAdapter.Assembly.Galerkin

/-! Uniform H3 bounds propagate every Sobolev order along the actual Galerkin flow. -/
set_option autoImplicit false
set_option Elab.async true
open Set
open scoped BigOperators
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

def sobolevViscousConstant (m : ℕ) : ℝ :=
  108*((2:ℝ)^m)^2*latticeSobolevConstant

theorem sobolevViscousConstant_pos (m : ℕ) : 0 < sobolevViscousConstant m := by
  unfold sobolevViscousConstant
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by positivity)))
    latticeSobolevConstant_pos

theorem sobolevEnergy_drift_rate_le (ν : ℝ) (hν : 0 < ν)
    (m N : ℕ) (q : Phase N) :
    2*inner ℝ (sobolevWeightedPhaseCLM m N q)
        (sobolevWeightedPhaseCLM m N (drift 0 N q)) -
      2*ν*sobolevDissipation m N q ≤
      (ν+sobolevViscousConstant m/ν*sobolevEnergy 2 N q)*sobolevEnergy m N q := by
  have h := weightedTransportPairing_young m N q q q (ν/3) (by positivity)
  have hi := sobolevWeighted_inner_bilinearConvection m N q q q
  rw [bilinearConvection_self] at hi
  change inner ℝ (sobolevWeightedPhaseCLM m N q)
    (sobolevWeightedPhaseCLM m N (drift 0 N q)) = -weightedTransportPairing m N q q q at hi
  have hp : 2*inner ℝ (sobolevWeightedPhaseCLM m N q)
        (sobolevWeightedPhaseCLM m N (drift 0 N q)) ≤
      ν*sobolevEnergy (m+1) N q +
        (sobolevViscousConstant m/ν)*sobolevEnergy 2 N q*sobolevEnergy m N q := by
    calc
      _ ≤ 2*|weightedTransportPairing m N q q q| := by
        rw [hi]
        exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by norm_num)
      _ ≤ _ := h
      _ = _ := by unfold sobolevViscousConstant; field_simp; ring
  rw [sobolevDissipation_eq_energy_succ_sub]
  have hm := sobolevEnergy_mono (Nat.le_succ m) N q
  nlinarith [mul_nonneg hν.le (sub_nonneg.mpr hm)]

theorem sobolevEnergy_drift_rate_le_of_h3_bound (ν C : ℝ) (hν : 0 < ν)
    (m N : ℕ) (q : Phase N) (hC : energy3 N q ≤ C) :
    2*inner ℝ (sobolevWeightedPhaseCLM m N q)
        (sobolevWeightedPhaseCLM m N (drift 0 N q)) -
      2*ν*sobolevDissipation m N q ≤
      (ν+sobolevViscousConstant m/ν*C)*sobolevEnergy m N q := by
  have h2 : sobolevEnergy 2 N q ≤ C :=
    (by simpa only [sobolevEnergy_three] using
      sobolevEnergy_mono (by omega : 2 ≤ 3) N q).trans hC
  exact (sobolevEnergy_drift_rate_le ν hν m N q).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left h2
        (div_nonneg (sobolevViscousConstant_pos m).le hν.le)) ν)
      (sobolevEnergy_nonneg m N q))

/-- All Sobolev orders are propagated on the given finite horizon from its actual H3 bound. -/
theorem central_all_order_bound_of_h3 {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (m : ℕ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      centralEnergy F N a ha t ≤ C) :
    ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      sobolevEnergy m N (F.map N t (initialPhaseData N a ha)) ≤
        initialSobolevMajorant m a *
          Real.exp ((ν+sobolevViscousConstant m/ν*C)*T) := by
  intro N hN t ht htT
  let q0 := initialPhaseData N a ha
  let A := ν+sobolevViscousConstant m/ν*C
  have hA : 0 ≤ A := add_nonneg hν.le
    (mul_nonneg (div_nonneg (sobolevViscousConstant_pos m).le hν.le) hC)
  have hg := scalar_constant_growth_on_Icc
    (fun s => sobolevEnergy m N (F.map N s q0))
    (fun s => 2*inner ℝ (sobolevWeightedPhaseCLM m N (F.map N s q0))
      (sobolevWeightedPhaseCLM m N (drift 0 N (F.map N s q0))) -
        2*ν*sobolevDissipation m N (F.map N s q0)) A T hT
    (fun s => phaseFlow_sobolevEnergy_dissipation_identity F m N q0 s)
    (fun s hs => sobolevEnergy_drift_rate_le_of_h3_bound ν C hν m N _
      (hbound N hN s hs.1 hs.2)) ⟨ht,htT⟩
  rw [F.map_zero] at hg
  exact hg.trans (mul_le_mul
    (initialPhaseData_sobolevEnergy_le_majorant m N a ha)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hA))
    (Real.exp_nonneg _) (initialSobolevMajorant_nonneg m a))

/-- The exact P7 H3 premise supplies every finite-horizon, all-order Galerkin bound. -/
theorem galerkin_all_sobolev_bounds {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (h3 : ∀ T : ℝ, 0 < T → GalerkinBoundAt F a ha T) :
    ∀ m : ℕ, ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
        sobolevEnergy m N (F.map N t (initialPhaseData N a ha)) ≤ C := by
  intro m T hT
  obtain ⟨C,hC,hbound⟩ := h3 T hT
  refine ⟨initialSobolevMajorant m a *
      Real.exp ((ν+sobolevViscousConstant m/ν*C)*T),
    mul_nonneg (initialSobolevMajorant_nonneg m a) (Real.exp_nonneg _), ?_⟩
  exact central_all_order_bound_of_h3 hν F a ha m T C hT.le hC hbound

end
end QuantumAdapter.Obligations
