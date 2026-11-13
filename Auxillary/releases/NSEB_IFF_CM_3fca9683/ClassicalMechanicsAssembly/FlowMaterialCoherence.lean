import ClassicalMechanicsAssembly.FlowTrajectories

/-!
# Coherence of material paths on overlapping finite slabs

The actual flow equation and identity initial configuration determine every
material path uniquely on common nonnegative times. Both inverse maps then
agree by the literal two-sided inverse identities. No equation of motion,
divergence assumption, or pressure gauge is required for this uniqueness step.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical

noncomputable section

/-- Smoothness turns the stated material-velocity identity into the actual ODE. -/
theorem material_path_hasDerivWithinAt {T : ℝ} (hT : 0 < T)
    {u η ρ : Velocity} (hη : MaterialPathOn T η ρ)
    (hflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    HasDerivWithinAt (fun s => η s a) (u t (η t a)) (Icc (0 : ℝ) T) t := by
  have hd := finite_time_hasDerivWithinAt hT hη.smooth ht a
  change HasDerivWithinAt (fun s => η s a)
    (materialVelocity T η t a) (Icc (0 : ℝ) T) t at hd
  rw [hflow t ht a] at hd
  exact hd

/-- Identity-normalized material paths coincide on every common positive subslab. -/
theorem material_flows_eq_on_subslab {R T S : ℝ} (hR : 0 < R)
    (hRT : R ≤ T) (hRS : R ≤ S)
    {u η ρ θ σ : Velocity} (hu : SmoothVelocityOn R u)
    (hp : ∀ t ∈ Icc (0 : ℝ) R, SpatialPeriodic (u t))
    (hη : MaterialPathOn T η ρ) (hθ : MaterialPathOn S θ σ)
    (hηflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    (hθflow : ∀ t ∈ Icc (0 : ℝ) S, ∀ a : Vec,
      materialVelocity S θ t a = u t (θ t a)) :
    ∀ t ∈ Icc (0 : ℝ) R, ∀ a : Vec, η t a = θ t a := by
  obtain ⟨B, K, h⟩ := Flow.smooth_periodic_slabODEData hR hu hp
  intro t ht a
  apply Flow.solution_unique h ⟨0, ⟨le_rfl, hR.le⟩⟩
    (f := fun s => η s a) (g := fun s => θ s a) ?_ ?_ ?_ ht
  · intro s hs
    exact (material_path_hasDerivWithinAt (hR.trans_le hRT) hη hηflow
      ⟨hs.1, hs.2.trans hRT⟩ a).mono (Icc_subset_Icc_right hRT)
  · intro s hs
    exact (material_path_hasDerivWithinAt (hR.trans_le hRS) hθ hθflow
      ⟨hs.1, hs.2.trans hRS⟩ a).mono (Icc_subset_Icc_right hRS)
  · rw [hη.initial_configuration, hθ.initial_configuration]

/-- The inverse maps of coinciding material paths coincide on the same subslab. -/
theorem material_inverses_eq_on_subslab {R T S : ℝ}
    (hRT : R ≤ T) (hRS : R ≤ S)
    {η ρ θ σ : Velocity}
    (hη : MaterialPathOn T η ρ) (hθ : MaterialPathOn S θ σ)
    (hforward : ∀ t ∈ Icc (0 : ℝ) R, ∀ a : Vec, η t a = θ t a) :
    ∀ t ∈ Icc (0 : ℝ) R, ∀ x : Vec, ρ t x = σ t x := by
  intro t ht x
  have he : η t (σ t x) = x :=
    (hforward t ht (σ t x)).trans (hθ.right_inverse t ⟨ht.1, ht.2.trans hRS⟩ x)
  have hi := hη.left_inverse t ⟨ht.1, ht.2.trans hRT⟩ (σ t x)
  rw [he] at hi
  exact hi

/-- Both charts and inverse charts agree on the complete closed overlap. -/
theorem material_paths_coherent_on_overlap {T S : ℝ}
    (hT : 0 < T) (hS : 0 < S)
    {u η ρ θ σ : Velocity} (hu : SmoothVelocityOn (min T S) u)
    (hp : ∀ t ∈ Icc (0 : ℝ) (min T S), SpatialPeriodic (u t))
    (hη : MaterialPathOn T η ρ) (hθ : MaterialPathOn S θ σ)
    (hηflow : ∀ t ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      materialVelocity T η t a = u t (η t a))
    (hθflow : ∀ t ∈ Icc (0 : ℝ) S, ∀ a : Vec,
      materialVelocity S θ t a = u t (θ t a)) :
    (∀ t ∈ Icc (0 : ℝ) (min T S), ∀ a : Vec, η t a = θ t a) ∧
    (∀ t ∈ Icc (0 : ℝ) (min T S), ∀ x : Vec, ρ t x = σ t x) := by
  have hf := material_flows_eq_on_subslab (lt_min hT hS)
    (min_le_left T S) (min_le_right T S) hu hp hη hθ hηflow hθflow
  exact ⟨hf, material_inverses_eq_on_subslab
    (min_le_left T S) (min_le_right T S) hη hθ hf⟩

end

end ClassicalMechanicsAssembly
