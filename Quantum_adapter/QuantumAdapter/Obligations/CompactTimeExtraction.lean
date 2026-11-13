import QuantumAdapter.Obligations.GalerkinAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! A common subsequence on every compact time interval for a countable family. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace QuantumAdapter.Obligations
noncomputable section

abbrev TimeWindow (H : ℕ) := Set.Icc (0:ℝ) (H:ℝ)

def compactTimeFunction {α : Type*} (f : ℕ → α → ℝ → ℂ)
    (hf : ∀ n a, Continuous (f n a)) (n : ℕ) (a : α) (H : ℕ) :
    TimeWindow H →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => f n a t.val, (hf n a).comp continuous_subtype_val⟩

@[simp] theorem compactTimeFunction_apply {α : Type*} (f : ℕ → α → ℝ → ℂ)
    (hf : ∀ n a, Continuous (f n a)) (n : ℕ) (a : α) (H : ℕ) (t : TimeWindow H) :
    compactTimeFunction f hf n a H t = f n a t.val := rfl

theorem compactTimeFunction_equicontinuous {α : Type*}
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (a : α) (H : ℕ) (L : ℝ)
    (hL : ∀ n s t, s ∈ Icc (0:ℝ) (H:ℝ) → t ∈ Icc (0:ℝ) (H:ℝ) →
      ‖f n a s-f n a t‖ ≤ L*‖s-t‖) :
    Equicontinuous (fun n : ℕ => fun t : TimeWindow H => compactTimeFunction f hf n a H t) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun x : ℝ => L*x)
    (by simpa using (continuous_const.mul continuous_id).tendsto (0:ℝ))
  intro s t n
  simpa only [compactTimeFunction_apply, dist_eq_norm, Subtype.dist_eq] using
    hL n s.val t.val s.property t.property

/-- The compact-window limits share the same subsequence, including all countable jets. -/
theorem compact_time_window_subsequence {α : Type*} [Countable α]
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (R L : α → ℕ → ℝ)
    (hR : ∀ (a : α) (H n : ℕ) (t : ℝ), t ∈ Icc (0:ℝ) (H:ℝ) → ‖f n a t‖ ≤ R a H)
    (hL : ∀ (a : α) (H n : ℕ) (s t : ℝ), s ∈ Icc (0:ℝ) (H:ℝ) → t ∈ Icc (0:ℝ) (H:ℝ) →
      ‖f n a s-f n a t‖ ≤ L a H*‖s-t‖) :
    ∃ (g : ∀ a : α, ∀ H : ℕ, TimeWindow H →ᵇ ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ (a : α) (H : ℕ), Tendsto (fun n => compactTimeFunction f hf (φ n) a H) atTop (𝓝 (g a H)) := by
  obtain ⟨g,φ,hφ,hg⟩ := countable_bounded_equicontinuous_subsequence
    (fun aH : α×ℕ => TimeWindow aH.2)
    (fun n aH => compactTimeFunction f hf n aH.1 aH.2)
    (fun aH => R aH.1 aH.2)
    (fun aH n t => hR aH.1 aH.2 n t.val t.property)
    (fun aH => compactTimeFunction_equicontinuous f hf aH.1 aH.2
      (L aH.1 aH.2) (hL aH.1 aH.2))
  exact ⟨fun a H => g (a,H),φ,hφ,fun a H => hg (a,H)⟩

/-- Limits on overlapping time windows agree at every common time. -/
theorem compact_time_limits_compatible {α : Type*}
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (g : ∀ a : α, ∀ H : ℕ, TimeWindow H →ᵇ ℂ) (φ : ℕ → ℕ)
    (hg : ∀ (a : α) (H : ℕ), Tendsto (fun n => compactTimeFunction f hf (φ n) a H)
      atTop (𝓝 (g a H)))
    (a : α) (H K : ℕ) (t : ℝ) (hH : t ∈ Icc (0:ℝ) (H:ℝ))
    (hK : t ∈ Icc (0:ℝ) (K:ℝ)) : g a H ⟨t,hH⟩ = g a K ⟨t,hK⟩ := by
  have h1 := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hg a H)).tendsto_at
    (⟨t,hH⟩ : TimeWindow H)
  have h2 := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hg a K)).tendsto_at
    (⟨t,hK⟩ : TimeWindow K)
  exact tendsto_nhds_unique h1 h2

def gluedTimeLimit {α : Type*}
    (g : ∀ a : α, ∀ H : ℕ, TimeWindow H →ᵇ ℂ) (a : α) (t : ℝ) : ℂ :=
  if ht : 0 ≤ t then
    g a (Classical.choose (exists_nat_ge t))
      ⟨t,ht,Classical.choose_spec (exists_nat_ge t)⟩
  else 0

theorem gluedTimeLimit_eq_window {α : Type*}
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (g : ∀ a : α, ∀ H : ℕ, TimeWindow H →ᵇ ℂ) (φ : ℕ → ℕ)
    (hg : ∀ (a : α) (H : ℕ), Tendsto (fun n => compactTimeFunction f hf (φ n) a H)
      atTop (𝓝 (g a H))) (a : α) (H : ℕ) (t : TimeWindow H) :
    gluedTimeLimit g a t.val = g a H t := by
  rw [gluedTimeLimit, dif_pos t.property.1]
  exact compact_time_limits_compatible f hf g φ hg a _ H t.val _ t.property

/-- The glued global limit is approached uniformly on each actual finite horizon. -/
theorem gluedTimeLimit_tendstoUniformlyOn {α : Type*}
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (g : ∀ a : α, ∀ H : ℕ, TimeWindow H →ᵇ ℂ) (φ : ℕ → ℕ)
    (hg : ∀ (a : α) (H : ℕ), Tendsto (fun n => compactTimeFunction f hf (φ n) a H)
      atTop (𝓝 (g a H))) (a : α) (H : ℕ) :
    TendstoUniformlyOn (fun n => f (φ n) a) (gluedTimeLimit g a) atTop (Icc (0:ℝ) (H:ℝ)) := by
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hg a H)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h := (Metric.tendstoUniformly_iff.mp hu) ε hε
  filter_upwards [h] with n hn t ht
  have he := gluedTimeLimit_eq_window f hf g φ hg a H (⟨t,ht⟩ : TimeWindow H)
  rw [he]
  exact hn ⟨t,ht⟩

theorem countable_compact_time_subsequence {α : Type*} [Countable α]
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (R L : α → ℕ → ℝ)
    (hR : ∀ (a : α) (H n : ℕ) (t : ℝ), t ∈ Icc (0:ℝ) (H:ℝ) → ‖f n a t‖ ≤ R a H)
    (hL : ∀ (a : α) (H n : ℕ) (s t : ℝ), s ∈ Icc (0:ℝ) (H:ℝ) → t ∈ Icc (0:ℝ) (H:ℝ) →
      ‖f n a s-f n a t‖ ≤ L a H*‖s-t‖) :
    ∃ (g : α → ℝ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ (a : α) (H : ℕ), TendstoUniformlyOn (fun n => f (φ n) a) (g a) atTop (Icc (0:ℝ) (H:ℝ)) := by
  obtain ⟨g,φ,hφ,hg⟩ := compact_time_window_subsequence f hf R L hR hL
  exact ⟨gluedTimeLimit g,φ,hφ,fun a H => gluedTimeLimit_tendstoUniformlyOn f hf g φ hg a H⟩

theorem continuousOn_Ici_of_compact_windows (g : ℝ → ℂ)
    (hg : ∀ H : ℕ, ContinuousOn g (Icc (0:ℝ) (H:ℝ))) :
    ContinuousOn g (Ici (0:ℝ)) := by
  intro t ht
  obtain ⟨H,hH⟩ := exists_nat_gt t
  have h := hg H t ⟨ht,hH.le⟩
  change ContinuousWithinAt g (Ici (0:ℝ) ∩ Iic (H:ℝ)) t at h
  exact (continuousWithinAt_inter (Iic_mem_nhds hH)).mp h

theorem gluedTimeLimit_continuousOn {α : Type*}
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (g : ∀ a : α, ∀ H : ℕ, TimeWindow H →ᵇ ℂ) (φ : ℕ → ℕ)
    (hg : ∀ (a : α) (H : ℕ), Tendsto (fun n => compactTimeFunction f hf (φ n) a H)
      atTop (𝓝 (g a H))) (a : α) : ContinuousOn (gluedTimeLimit g a) (Ici (0:ℝ)) := by
  apply continuousOn_Ici_of_compact_windows
  intro H
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (fun t : TimeWindow H => gluedTimeLimit g a t.val) = g a H := by
    funext t
    exact gluedTimeLimit_eq_window f hf g φ hg a H t
  change Continuous (fun t : TimeWindow H => gluedTimeLimit g a t.val)
  rw [he]
  exact (g a H).continuous

theorem countable_compact_time_subsequence_continuous {α : Type*} [Countable α]
    (f : ℕ → α → ℝ → ℂ) (hf : ∀ n a, Continuous (f n a))
    (R L : α → ℕ → ℝ)
    (hR : ∀ (a : α) (H n : ℕ) (t : ℝ), t ∈ Icc (0:ℝ) (H:ℝ) → ‖f n a t‖ ≤ R a H)
    (hL : ∀ (a : α) (H n : ℕ) (s t : ℝ), s ∈ Icc (0:ℝ) (H:ℝ) → t ∈ Icc (0:ℝ) (H:ℝ) →
      ‖f n a s-f n a t‖ ≤ L a H*‖s-t‖) :
    ∃ (g : α → ℝ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ a, ContinuousOn (g a) (Ici (0:ℝ))) ∧
      ∀ (a : α) (H : ℕ), TendstoUniformlyOn (fun n => f (φ n) a) (g a) atTop (Icc (0:ℝ) (H:ℝ)) := by
  obtain ⟨g,φ,hφ,hg⟩ := compact_time_window_subsequence f hf R L hR hL
  exact ⟨gluedTimeLimit g,φ,hφ,fun a => gluedTimeLimit_continuousOn f hf g φ hg a,
    fun a H => gluedTimeLimit_tendstoUniformlyOn f hf g φ hg a H⟩

end
end QuantumAdapter.Obligations
