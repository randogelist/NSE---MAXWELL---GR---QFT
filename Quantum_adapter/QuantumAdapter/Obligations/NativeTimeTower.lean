import QuantumAdapter.Obligations.GalerkinJetBounds
import QuantumAdapter.Obligations.ClosedTimeLimits
import QuantumAdapter.Obligations.FourierTimeTower

/-! An actual all-order coefficient derivative tower extracted from the native Galerkin flow. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter
open scoped BigOperators Topology
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

abbrev JetCoefficientIndex := ℕ × FourierIndex

def nativeJetCoefficient {ν : ℝ} (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (N : ℕ) (α : JetCoefficientIndex) (t : ℝ) : ℂ :=
  phaseCoeff (phaseTimeJet F (N+1) (initialPhaseData (N+1) a ha) α.1 t) α.2.1 α.2.2

theorem nativeJetCoefficient_hasDerivAt {ν : ℝ} (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (N : ℕ) (α : JetCoefficientIndex) (t : ℝ) :
    HasDerivAt (nativeJetCoefficient F a ha N α)
      (nativeJetCoefficient F a ha N (α.1+1,α.2) t) t := by
  simpa only [nativeJetCoefficient, Function.comp_def, phaseCoordinate_apply] using
    (phaseCoordinate (N+1) α.2.1 α.2.2).hasFDerivAt.comp_hasDerivAt t
      (phaseTimeJet_hasDerivAt F (N+1) (initialPhaseData (N+1) a ha) α.1 t)

theorem nativeJetCoefficient_continuous {ν : ℝ} (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (N : ℕ) (α : JetCoefficientIndex) : Continuous (nativeJetCoefficient F a ha N α) :=
  continuous_iff_continuousAt.mpr
    (fun t => (nativeJetCoefficient_hasDerivAt F a ha N α t).continuousAt)

theorem nativeJetCoefficient_bound_of_energy {ν : ℝ} (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (N : ℕ) (α : JetCoefficientIndex) (t C : ℝ)
    (hb : sobolevEnergy 0 (N+1)
      (phaseTimeJet F (N+1) (initialPhaseData (N+1) a ha) α.1 t) ≤ C) :
    ‖nativeJetCoefficient F a ha N α t‖ ≤ Real.sqrt C := by
  have h := weighted_coordinate_le_sqrt_sobolevEnergy 0 (N+1)
    (phaseTimeJet F (N+1) (initialPhaseData (N+1) a ha) α.1 t) α.2.1 α.2.2
  simp only [pow_zero,one_mul] at h
  exact h.trans (Real.sqrt_le_sqrt hb)

theorem nativeJetCoefficient_time_modulus {ν : ℝ} (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (N : ℕ) (α : JetCoefficientIndex) (H : ℕ) (C : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) (H:ℝ), sobolevEnergy 0 (N+1)
      (phaseTimeJet F (N+1) (initialPhaseData (N+1) a ha) (α.1+1) t) ≤ C)
    (s t : ℝ) (hs : s ∈ Icc (0:ℝ) (H:ℝ)) (ht : t ∈ Icc (0:ℝ) (H:ℝ)) :
    ‖nativeJetCoefficient F a ha N α s-nativeJetCoefficient F a ha N α t‖ ≤
      Real.sqrt C*‖s-t‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (0:ℝ) (H:ℝ))
    (f' := nativeJetCoefficient F a ha N (α.1+1,α.2))
  · intro r hr
    exact (nativeJetCoefficient_hasDerivAt F a ha N α r).hasDerivWithinAt
  · intro r hr
    exact nativeJetCoefficient_bound_of_energy F a ha N (α.1+1,α.2) r C (hb r hr)
  · exact convex_Icc _ _
  · exact ht
  · exact hs

/-- Actual uniform jets give one global coefficient tower with the closed-boundary derivatives. -/
theorem native_time_tower_exists {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (h3 : ∀ T : ℝ, 0 < T → GalerkinBoundAt F a ha T) :
    ∃ (d : ℕ → ℝ → FourierCoeff) (φ : ℕ → ℕ), StrictMono φ ∧
      FourierTimeTowerDerivative d ∧ FourierTimeTowerBounds d ∧
      (∀ n t, 0 ≤ t → SpectralReality (d n t) ∧ SpectralSolenoidal (d n t)) ∧
      ∀ n k i H, TendstoUniformlyOn
        (fun j t => phaseCoeff (phaseTimeJet F (φ j+1)
          (initialPhaseData (φ j+1) a ha) n t) k i)
        (fun t => d n t k i) atTop (Icc (0:ℝ) (H:ℝ)) := by
  have hbase (n m H : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ (H:ℝ)+1 →
        sobolevEnergy m N (phaseTimeJet F N (initialPhaseData N a ha) n t) ≤ C :=
    galerkin_all_timeJet_sobolev_bounds hν F a ha h3 n m ((H:ℝ)+1) (by positivity)
  choose C hC hCB using hbase
  have hR (α : JetCoefficientIndex) (H N : ℕ) (t : ℝ)
      (ht : t ∈ Icc (0:ℝ) (H:ℝ)) :
      ‖nativeJetCoefficient F a ha N α t‖ ≤ Real.sqrt (C α.1 0 H) := by
    apply nativeJetCoefficient_bound_of_energy
    exact hCB α.1 0 H (N+1) (by omega) t ht.1 (by linarith [ht.2])
  have hL (α : JetCoefficientIndex) (H N : ℕ) (s t : ℝ)
      (hs : s ∈ Icc (0:ℝ) (H:ℝ)) (ht : t ∈ Icc (0:ℝ) (H:ℝ)) :
      ‖nativeJetCoefficient F a ha N α s-nativeJetCoefficient F a ha N α t‖ ≤
        Real.sqrt (C (α.1+1) 0 H)*‖s-t‖ := by
    apply nativeJetCoefficient_time_modulus F a ha N α H _ _ s t hs ht
    intro r hr
    exact hCB (α.1+1) 0 H (N+1) (by omega) r hr.1 (by linarith [hr.2])
  obtain ⟨g,φ,hφ,hcont,hlim⟩ := countable_compact_time_subsequence_continuous
    (nativeJetCoefficient F a ha) (nativeJetCoefficient_continuous F a ha)
    (fun α H => Real.sqrt (C α.1 0 H)) (fun α H => Real.sqrt (C (α.1+1) 0 H)) hR hL
  let d : ℕ → ℝ → FourierCoeff := fun n t k i => g (n,(k,i)) t
  have hpoint (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
      Tendsto (fun j => phaseCoeff (phaseTimeJet F (φ j+1)
        (initialPhaseData (φ j+1) a ha) n t) k i) atTop (𝓝 (d n t k i)) := by
    obtain ⟨H,hH⟩ := exists_nat_ge t
    exact (hlim (n,(k,i)) H).tendsto_at ⟨ht,hH⟩
  refine ⟨d,φ,hφ,?_,?_,?_,?_⟩
  · intro n t ht k i
    exact derivative_limit_on_closed_halfline
      (fun j => nativeJetCoefficient F a ha (φ j) (n,(k,i)))
      (fun j => nativeJetCoefficient F a ha (φ j) (n+1,(k,i)))
      (g (n,(k,i))) (g (n+1,(k,i)))
      (fun j s => nativeJetCoefficient_hasDerivAt F a ha (φ j) (n,(k,i)) s)
      (fun j => nativeJetCoefficient_continuous F a ha (φ j) (n+1,(k,i)))
      (hcont (n+1,(k,i))) (hlim (n,(k,i))) (hlim (n+1,(k,i))) t ht
  · intro n m T hT
    obtain ⟨H,hH⟩ := exists_nat_ge T
    refine ⟨C n m H,hC n m H,?_⟩
    intro t ht htT I
    have hfinite : Tendsto (fun j => ∑ ki ∈ I,
        ‖sobolevWeightedCoeff m
          (phaseCoeff (phaseTimeJet F (φ j+1) (initialPhaseData (φ j+1) a ha) n t)) ki‖^2)
        atTop (𝓝 (∑ ki ∈ I, ‖sobolevWeightedCoeff m (d n t) ki‖^2)) := by
      apply tendsto_finset_sum
      intro ki hki
      simpa only [sobolevWeightedCoeff] using
        (((hpoint n t ht ki.1 ki.2).const_mul ((torusSobolevWeight ki.1:ℂ)^m)).norm.pow 2)
    apply le_of_tendsto hfinite
    exact Filter.Eventually.of_forall (fun j =>
      (finite_sum_weightedCoeff_sq_le_energy m (φ j+1)
        (phaseTimeJet F (φ j+1) (initialPhaseData (φ j+1) a ha) n t) I).trans
        (hCB n m H (φ j+1) (by omega) t ht (by linarith)))
  · intro n t ht
    exact ⟨coefficient_limit_reality (fun j => φ j+1)
      (fun j => phaseTimeJet F (φ j+1) (initialPhaseData (φ j+1) a ha) n t)
      (d n t) (hpoint n t ht),
      coefficient_limit_solenoidal (fun j => φ j+1)
      (fun j => phaseTimeJet F (φ j+1) (initialPhaseData (φ j+1) a ha) n t)
      (d n t) (hpoint n t ht)⟩
  · intro n k i H
    exact hlim (n,(k,i)) H

end
end QuantumAdapter.Obligations
