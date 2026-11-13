import QuantumAdapter.Obligations.CompactTimeExtraction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Passing actual derivative towers to a uniform limit, including the t=0 endpoint. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter MeasureTheory
open scoped Topology
namespace QuantumAdapter.Obligations
noncomputable section

theorem integral_tendsto_of_uniform_on_interval
    (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hf : ∀ n, ContinuousOn (f n) (Icc 0 t)) (hg : ContinuousOn g (Icc 0 t))
    (hlim : TendstoUniformlyOn f g atTop (Icc 0 t)) :
    Tendsto (fun n => ∫ s in (0:ℝ)..t, f n s) atTop (𝓝 (∫ s in (0:ℝ)..t, g s)) := by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  · exact Filter.Eventually.of_forall (fun n => by
      simpa only [uIcc_of_le ht] using hf n)
  · simpa only [uIcc_of_le ht] using hlim

theorem derivative_limit_integral_identity
    (f f' : ℕ → ℝ → ℂ) (g g' : ℝ → ℂ)
    (hf : ∀ n t, HasDerivAt (f n) (f' n t) t)
    (hf' : ∀ n, Continuous (f' n))
    (hg' : ContinuousOn g' (Ici (0:ℝ)))
    (hlim : ∀ H : ℕ, TendstoUniformlyOn f g atTop (Icc (0:ℝ) (H:ℝ)))
    (hlim' : ∀ H : ℕ, TendstoUniformlyOn f' g' atTop (Icc (0:ℝ) (H:ℝ)))
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, g' s) = g t-g 0 := by
  obtain ⟨H,hH⟩ := exists_nat_ge t
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) (H:ℝ) := fun s hs => ⟨hs.1,hs.2.trans hH⟩
  have hI := integral_tendsto_of_uniform_on_interval f' g' t ht
    (fun n => (hf' n).continuousOn) (hg'.mono (fun s hs => hs.1)) ((hlim' H).mono hsub)
  have hF := ((hlim H).tendsto_at ⟨ht,hH⟩).sub
    ((hlim H).tendsto_at ⟨le_rfl,by positivity⟩)
  have he (n : ℕ) : (∫ s in (0:ℝ)..t, f' n s) = f n t-f n 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hf n s)
      ((hf' n).intervalIntegrable _ _)
  simp_rw [he] at hI
  exact tendsto_nhds_unique hI hF

/-- No negative-time derivative assumption is imposed on the limiting function. -/
theorem derivative_limit_on_closed_halfline
    (f f' : ℕ → ℝ → ℂ) (g g' : ℝ → ℂ)
    (hf : ∀ n t, HasDerivAt (f n) (f' n t) t)
    (hf' : ∀ n, Continuous (f' n))
    (hg' : ContinuousOn g' (Ici (0:ℝ)))
    (hlim : ∀ H : ℕ, TendstoUniformlyOn f g atTop (Icc (0:ℝ) (H:ℝ)))
    (hlim' : ∀ H : ℕ, TendstoUniformlyOn f' g' atTop (Icc (0:ℝ) (H:ℝ)))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt g (g' t) (Ici (0:ℝ)) t := by
  let G : ℝ → ℂ := fun s => g' (max 0 s)
  have hG : Continuous G := hg'.comp_continuous
    (continuous_const.max continuous_id) (fun s => le_max_left 0 s)
  have he (s : ℝ) (hs : 0 ≤ s) :
      g s = g 0 + ∫ r in (0:ℝ)..s, G r := by
    have hI := derivative_limit_integral_identity f f' g g' hf hf' hg' hlim hlim' s hs
    have hEq : (∫ r in (0:ℝ)..s, G r) = ∫ r in (0:ℝ)..s, g' r := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := (show r ∈ Icc (0:ℝ) s from by
        simpa only [uIcc_of_le hs] using hr).1
      simp only [G, max_eq_right hr0]
    rw [hEq,hI]
    abel
  have hd := ((hG.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (g 0)).hasDerivWithinAt
  have htG : G t=g' t := by simp only [G,max_eq_right ht]
  rw [htG] at hd
  exact hd.congr_of_mem (fun s hs => he s hs) ht

end
end QuantumAdapter.Obligations
