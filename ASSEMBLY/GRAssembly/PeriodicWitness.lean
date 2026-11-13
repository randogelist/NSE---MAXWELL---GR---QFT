import GRAssembly.PeriodicGluing

/-!
GC09: the complete constructive passage from compact overlap germs to an
actual periodic field on one open parameter neighborhood.  `S = ℝ` gives
the scalar time parameter; `S = ℝ × ℝ` gives the Gaussian radial/time pair.
The source germs, finite atlas, and domain margins remain explicit inputs.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace NSEGR.Assembly
noncomputable section

/-- A translated atlas with compatible local functions constructs a periodic
field.  The output joint germ equality retains every local differential law. -/
theorem periodic_witness_of_compatible_atlas
    {S Y ι : Type*} [TopologicalSpace S]
    (U : ι → Set Vec) (f : ι → S → Vec → Y)
    (W : Set S) (hW : IsOpen W) (hU : ∀ i, IsOpen (U i))
    (hcover : unitCube ⊆ ⋃ i, U i)
    (hcompat : ∀ s ∈ W, ∀ a b : ι × Frequency, ∀ x,
      x ∈ latticePatch U a → x ∈ latticePatch U b →
        latticeLocal f a s x = latticeLocal f b s x)
    (outside : Y) :
    ∃ g : S → Vec → Y,
      (∀ s ∈ W, SpatialPeriodic (g s)) ∧
      (∀ a : ι × Frequency, ∀ s ∈ W, ∀ x ∈ latticePatch U a,
        (fun z : S × Vec => g z.1 z.2) =ᶠ[𝓝 (s, x)]
          (fun z => latticeLocal f a z.1 z.2)) := by
  let D : Set (S × Vec) := W ×ˢ univ
  let P : (ι × Frequency) → Set (S × Vec) := fun a => W ×ˢ latticePatch U a
  let F : (ι × Frequency) → (S × Vec) → Y := fun a z => latticeLocal f a z.1 z.2
  have hD : IsOpen D := hW.prod isOpen_univ
  have hP : ∀ a, IsOpen (P a) := fun a => hW.prod (latticePatch_isOpen U hU a)
  have hcoverD : D ⊆ ⋃ a, P a := by
    intro z hz
    obtain ⟨a, ha⟩ := latticePatch_cover U hcover z.2
    exact mem_iUnion_of_mem a ⟨hz.1, ha⟩
  have hcompatD : ∀ a b z, z ∈ P a → z ∈ P b → F a z = F b z := by
    intro a b z ha hb
    exact hcompat z.1 ha.1 a b z.2 ha.2 hb.2
  let G := overlapGlue P F D hcoverD hcompatD outside
  have hvalue (a : ι × Frequency) {s : S} (hs : s ∈ W) {x : Vec}
      (hx : x ∈ latticePatch U a) : G (s, x) = latticeLocal f a s x := by
    exact overlapGlue_eq P F D hcoverD hcompatD outside ⟨hs, mem_univ x⟩ ⟨hs, hx⟩
  have htranslate {s : S} (hs : s ∈ W) (x : Vec) (k : Frequency) :
      G (s, x + integerSpatialShift k) = G (s, x) := by
    obtain ⟨a, ha⟩ := latticePatch_cover U hcover x
    have hresidual : x + integerSpatialShift k - integerSpatialShift (a.2 + k) =
        x - integerSpatialShift a.2 := by
      rw [integerSpatialShift_add]
      abel
    have hnext : x + integerSpatialShift k ∈ latticePatch U (a.1, a.2 + k) := by
      change x + integerSpatialShift k - integerSpatialShift (a.2 + k) ∈ U a.1
      rwa [hresidual]
    rw [hvalue (a.1, a.2 + k) hs hnext, hvalue a hs ha]
    simp only [latticeLocal, hresidual]
  refine ⟨fun s x => G (s, x), ?_, ?_⟩
  · intro s hs x j
    simpa only [integerSpatialShift_single] using htranslate hs x (Pi.single j (1 : ℤ))
  · intro a s hs x hx
    exact overlapGlue_eventuallyEq P F D hcoverD hcompatD outside hD hP
      ⟨hs, mem_univ x⟩ ⟨hs, hx⟩

/-- Compact overlap uniqueness, finite atlas size, and neighborhood source
domains produce the common parameter domain and the actual periodic field. -/
theorem periodic_witness_of_compact_overlap_germs
    {S Y ι : Type*} [TopologicalSpace S] [Finite ι] {s0 : S}
    (U : ι → Set Vec) (V : ι → Set S) (f : ι → S → Vec → Y)
    (hU : ∀ i, IsOpen (U i))
    (hV : ∀ i, V i ∈ 𝓝 s0)
    (hcover : unitCube ⊆ ⋃ i, U i)
    (hcompact : ∀ i, IsCompact (closure (U i)))
    (hbox : ∀ i, ∀ y ∈ U i, ∀ j, (-1 : ℝ) < y j ∧ y j < 2)
    (hlocal : ∀ i j (a : BoundedLatticeShift), ∀ x ∈ compactLatticeOverlap U i j a,
      ∀ᶠ z : S × Vec in 𝓝 (s0, x),
        f i z.1 z.2 = f j z.1 (z.2 - integerSpatialShift (boundedShiftVector a)))
    (outside : Y) :
    ∃ W : Set S, IsOpen W ∧ s0 ∈ W ∧ (∀ i, W ⊆ V i) ∧
      ∃ g : S → Vec → Y,
        (∀ s ∈ W, SpatialPeriodic (g s)) ∧
        (∀ a : ι × Frequency, ∀ s ∈ W, ∀ x ∈ latticePatch U a,
          (fun z : S × Vec => g z.1 z.2) =ᶠ[𝓝 (s, x)]
            (fun z => latticeLocal f a z.1 z.2)) := by
  have hgerms := lattice_overlap_germs_uniform U f hcompact hbox hlocal
  have hdomains : ∀ᶠ s in 𝓝 s0, ∀ i, s ∈ V i := Filter.eventually_all.2 hV
  obtain ⟨W, hsub, hW, hs0⟩ := mem_nhds_iff.1 (hgerms.and hdomains)
  have hcompat : ∀ s ∈ W, ∀ a b : ι × Frequency, ∀ x,
      x ∈ latticePatch U a → x ∈ latticePatch U b →
        latticeLocal f a s x = latticeLocal f b s x := by
    intro s hs
    exact (hsub hs).1
  obtain ⟨g, hperiodic, hglued⟩ :=
    periodic_witness_of_compatible_atlas U f W hW hU hcover hcompat outside
  exact ⟨W, hW, hs0, fun i s hs => (hsub hs).2 i, g, hperiodic, hglued⟩

/-- Analyticity transfers from a local field through the translated germ. -/
theorem analyticAt_of_lattice_local_germ
    {S Y ι : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ι → S → Vec → Y) (g : S → Vec → Y)
    (a : ι × Frequency) (s : S) (x : Vec)
    (hf : AnalyticAt ℝ (fun z : S × Vec => f a.1 z.1 z.2)
      (s, x - integerSpatialShift a.2))
    (hglued : (fun z : S × Vec => g z.1 z.2) =ᶠ[𝓝 (s, x)]
      (fun z => latticeLocal f a z.1 z.2)) :
    AnalyticAt ℝ (fun z : S × Vec => g z.1 z.2) (s, x) := by
  have hshift : AnalyticAt ℝ
      (fun z : S × Vec => (z.1, z.2 - integerSpatialShift a.2)) (s, x) :=
    analyticAt_fst.prod (analyticAt_snd.sub analyticAt_const)
  have htranslated : AnalyticAt ℝ
      (fun z : S × Vec => latticeLocal f a z.1 z.2) (s, x) := by
    exact hf.comp
      (f := fun z : S × Vec => (z.1, z.2 - integerSpatialShift a.2))
      (x := (s, x)) hshift
  exact htranslated.congr hglued.symm

/-- A germ-local differential law is inherited by the constructed field.
The locality premise can be proved by the first/iterated derivative congruences
and contains no existence or gluing assertion. -/
theorem germ_local_law_of_lattice_local_germ
    {S Y ι : Type*} [TopologicalSpace S]
    (f : ι → S → Vec → Y) (g : S → Vec → Y)
    (a : ι × Frequency) (s : S) (x : Vec)
    (Law : ((S × Vec) → Y) → (S × Vec) → Prop)
    (hlocality : ∀ h k z, h =ᶠ[𝓝 z] k → (Law h z ↔ Law k z))
    (hsource : Law (fun z => latticeLocal f a z.1 z.2) (s, x))
    (hglued : (fun z : S × Vec => g z.1 z.2) =ᶠ[𝓝 (s, x)]
      (fun z => latticeLocal f a z.1 z.2)) :
    Law (fun z => g z.1 z.2) (s, x) :=
  (hlocality _ _ _ hglued).2 hsource

/-- Analytic compact-germ assembly, with no global function supplied as input. -/
theorem periodic_analytic_witness_of_compact_overlap_germs
    {S Y ι : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Finite ι] {s0 : S}
    (U : ι → Set Vec) (V : ι → Set S) (f : ι → S → Vec → Y)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, V i ∈ 𝓝 s0)
    (hcover : unitCube ⊆ ⋃ i, U i)
    (hcompact : ∀ i, IsCompact (closure (U i)))
    (hbox : ∀ i, ∀ y ∈ U i, ∀ j, (-1 : ℝ) < y j ∧ y j < 2)
    (hlocal : ∀ i j (a : BoundedLatticeShift), ∀ x ∈ compactLatticeOverlap U i j a,
      ∀ᶠ z : S × Vec in 𝓝 (s0, x),
        f i z.1 z.2 = f j z.1 (z.2 - integerSpatialShift (boundedShiftVector a)))
    (hanalytic : ∀ i, ∀ s ∈ V i, ∀ x ∈ U i,
      AnalyticAt ℝ (fun z : S × Vec => f i z.1 z.2) (s, x))
    (outside : Y) :
    ∃ W : Set S, IsOpen W ∧ s0 ∈ W ∧ (∀ i, W ⊆ V i) ∧
      ∃ g : S → Vec → Y,
        (∀ s ∈ W, SpatialPeriodic (g s)) ∧
        (∀ s ∈ W, ∀ x, AnalyticAt ℝ (fun z : S × Vec => g z.1 z.2) (s, x)) ∧
        (∀ a : ι × Frequency, ∀ s ∈ W, ∀ x ∈ latticePatch U a,
          (fun z : S × Vec => g z.1 z.2) =ᶠ[𝓝 (s, x)]
            (fun z => latticeLocal f a z.1 z.2)) := by
  obtain ⟨W, hW, hs0, hdomains, g, hperiodic, hglued⟩ :=
    periodic_witness_of_compact_overlap_germs U V f hU hV hcover hcompact hbox hlocal outside
  refine ⟨W, hW, hs0, hdomains, g, hperiodic, ?_, hglued⟩
  intro s hs x
  obtain ⟨a, ha⟩ := latticePatch_cover U hcover x
  exact analyticAt_of_lattice_local_germ f g a s x
    (hanalytic a.1 s (hdomains a.1 hs) _ ha) (hglued a s hs x ha)

end
end NSEGR.Assembly
