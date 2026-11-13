import QuantumAdapter.L2Norm

/-!
The half-density pullback descends to the actual complex L2 quotient.
Almost-everywhere compatibility is derived from the existing integral and
MemLp pullback laws. The group equations then provide the inverse of the
complex linear isometry. No strong continuity or generator is asserted.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory

namespace QuantumAdapter

noncomputable section

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
  {κ : ℝ} {Φ : ℝ → E → E}

theorem halfDensityPullback_congr_ae
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    {ψ χ : Wave E} (hψ : MemLp ψ 2 μ) (hχ : MemLp χ 2 μ)
    (hψχ : ψ =ᵐ[μ] χ) (t : ℝ) :
    halfDensityPullback κ Φ t ψ =ᵐ[μ] halfDensityPullback κ Φ t χ := by
  have hzero : (hψ.sub hχ).toLp (ψ - χ) = 0 := by
    rw [MemLp.toLp_sub, hψ.toLp_congr hχ hψχ, sub_self]
  have hnorm :
      ‖(hLp t (ψ - χ) (hψ.sub hχ)).toLp
        (halfDensityPullback κ Φ t (ψ - χ))‖ = 0 := by
    rw [halfDensityPullback_toLp_norm hI hLp (hψ.sub hχ) t, hzero, norm_zero]
  have htranszero :
      (hLp t (ψ - χ) (hψ.sub hχ)).toLp
        (halfDensityPullback κ Φ t (ψ - χ)) = 0 := norm_eq_zero.mp hnorm
  have hae : halfDensityPullback κ Φ t (ψ - χ) =ᵐ[μ] 0 :=
    (hLp t (ψ - χ) (hψ.sub hχ)).coeFn_toLp.symm.trans
      (Lp.eq_zero_iff_ae_eq_zero.mp htranszero)
  filter_upwards [hae] with q hq
  apply sub_eq_zero.mp
  simpa only [halfDensityPullback, Pi.sub_apply, Pi.zero_apply, mul_sub] using hq

def l2Pullback (hLp : MemLpPullbackLaw μ κ Φ) (t : ℝ)
    (ψ : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (hLp t ψ (Lp.memLp ψ)).toLp (halfDensityPullback κ Φ t ψ)

theorem l2Pullback_coe (hLp : MemLpPullbackLaw μ κ Φ) (t : ℝ)
    (ψ : Lp ℂ 2 μ) :
    (l2Pullback hLp t ψ : Wave E) =ᵐ[μ] halfDensityPullback κ Φ t ψ :=
  (hLp t ψ (Lp.memLp ψ)).coeFn_toLp

theorem l2Pullback_toLp
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    {ψ : Wave E} (hψ : MemLp ψ 2 μ) (t : ℝ) :
    l2Pullback hLp t (hψ.toLp ψ) =
      (hLp t ψ hψ).toLp (halfDensityPullback κ Φ t ψ) := by
  apply MemLp.toLp_congr
  exact halfDensityPullback_congr_ae hI hLp
    (Lp.memLp (hψ.toLp ψ)) hψ hψ.coeFn_toLp t

theorem l2Pullback_norm
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (t : ℝ) (ψ : Lp ℂ 2 μ) : ‖l2Pullback hLp t ψ‖ = ‖ψ‖ := by
  simpa only [l2Pullback, Lp.toLp_coeFn] using
    halfDensityPullback_toLp_norm hI hLp (Lp.memLp ψ) t

theorem l2Pullback_add_vectors
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (t : ℝ) (ψ χ : Lp ℂ 2 μ) :
    l2Pullback hLp t (ψ + χ) = l2Pullback hLp t ψ + l2Pullback hLp t χ := by
  apply Lp.ext
  have hsum := halfDensityPullback_congr_ae hI hLp
    (Lp.memLp (ψ + χ)) ((Lp.memLp ψ).add (Lp.memLp χ))
    (Lp.coeFn_add ψ χ) t
  filter_upwards [l2Pullback_coe hLp t (ψ + χ), hsum,
    Lp.coeFn_add (l2Pullback hLp t ψ) (l2Pullback hLp t χ),
    l2Pullback_coe hLp t ψ, l2Pullback_coe hLp t χ] with q h₁ h₂ h₃ h₄ h₅
  calc
    l2Pullback hLp t (ψ + χ) q =
      halfDensityPullback κ Φ t ((ψ + χ : Lp ℂ 2 μ) : Wave E) q := h₁
    _ = halfDensityPullback κ Φ t ((ψ : Wave E) + (χ : Wave E)) q := h₂
    _ = halfDensityPullback κ Φ t ψ q + halfDensityPullback κ Φ t χ q :=
      mul_add _ _ _
    _ = (l2Pullback hLp t ψ + l2Pullback hLp t χ) q := by
      simpa only [Pi.add_apply, h₄, h₅] using h₃.symm

theorem l2Pullback_smul
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (t : ℝ) (c : ℂ) (ψ : Lp ℂ 2 μ) :
    l2Pullback hLp t (c • ψ) = c • l2Pullback hLp t ψ := by
  apply Lp.ext
  have hsmul := halfDensityPullback_congr_ae hI hLp
    (Lp.memLp (c • ψ)) ((Lp.memLp ψ).const_smul c)
    (Lp.coeFn_smul c ψ) t
  filter_upwards [l2Pullback_coe hLp t (c • ψ), hsmul,
    Lp.coeFn_smul c (l2Pullback hLp t ψ), l2Pullback_coe hLp t ψ]
      with q h₁ h₂ h₃ h₄
  calc
    l2Pullback hLp t (c • ψ) q =
      halfDensityPullback κ Φ t ((c • ψ : Lp ℂ 2 μ) : Wave E) q := h₁
    _ = halfDensityPullback κ Φ t (c • (ψ : Wave E)) q := h₂
    _ = c • halfDensityPullback κ Φ t ψ q := by
      simp only [halfDensityPullback, Pi.smul_apply, smul_eq_mul]
      ring
    _ = (c • l2Pullback hLp t ψ) q := by
      simpa only [Pi.smul_apply, h₄] using h₃.symm

def l2PullbackIsometry
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (t : ℝ) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := l2Pullback hLp t
  map_add' := l2Pullback_add_vectors hI hLp t
  map_smul' := l2Pullback_smul hI hLp t
  norm_map' := l2Pullback_norm hI hLp t

theorem l2Pullback_zero (hLp : MemLpPullbackLaw μ κ Φ)
    (hzero : ∀ q, Φ 0 q = q) (ψ : Lp ℂ 2 μ) :
    l2Pullback hLp 0 ψ = ψ := by
  apply Lp.ext
  simpa only [halfDensityPullback_zero κ Φ hzero] using l2Pullback_coe hLp 0 ψ

theorem l2Pullback_add_times
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (hadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (s t : ℝ) (ψ : Lp ℂ 2 μ) :
    l2Pullback hLp s (l2Pullback hLp t ψ) = l2Pullback hLp (s + t) ψ := by
  apply Lp.ext
  have hrep := halfDensityPullback_congr_ae hI hLp
    (Lp.memLp (l2Pullback hLp t ψ)) (hLp t ψ (Lp.memLp ψ))
    (l2Pullback_coe hLp t ψ) s
  filter_upwards [l2Pullback_coe hLp s (l2Pullback hLp t ψ), hrep,
    l2Pullback_coe hLp (s + t) ψ] with q h₁ h₂ h₃
  exact h₁.trans (h₂.trans
    ((congrFun (halfDensityPullback_add κ Φ hadd s t ψ) q).trans h₃.symm))

def l2PullbackEquiv
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (hzero : ∀ q, Φ 0 q = q)
    (hadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (t : ℝ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofLinearIsometry (l2PullbackIsometry hI hLp t)
    (l2PullbackIsometry hI hLp (-t)).toLinearMap
    (by
      apply LinearMap.ext
      intro ψ
      change l2Pullback hLp t (l2Pullback hLp (-t) ψ) = ψ
      rw [l2Pullback_add_times hI hLp hadd, add_neg_cancel, l2Pullback_zero hLp hzero])
    (by
      apply LinearMap.ext
      intro ψ
      change l2Pullback hLp (-t) (l2Pullback hLp t ψ) = ψ
      rw [l2Pullback_add_times hI hLp hadd, neg_add_cancel, l2Pullback_zero hLp hzero])

theorem l2PullbackEquiv_apply
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (hzero : ∀ q, Φ 0 q = q)
    (hadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (t : ℝ) (ψ : Lp ℂ 2 μ) :
    l2PullbackEquiv hI hLp hzero hadd t ψ = l2Pullback hLp t ψ := rfl

theorem l2PullbackEquiv_symm_apply
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    (hzero : ∀ q, Φ 0 q = q)
    (hadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (t : ℝ) (ψ : Lp ℂ 2 μ) :
    (l2PullbackEquiv hI hLp hzero hadd t).symm ψ = l2Pullback hLp (-t) ψ := rfl

end

end QuantumAdapter
