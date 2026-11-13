import GRAssembly.BoundaryConstraintsJets

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

namespace NSEGR.Assembly
open Set Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
noncomputable section

-- Closed finite-index decisions avoid recursive extensionality normalization.
private theorem boundary_fin4_ne_01 : (0 : Fin 4) ≠ 1 := by decide
private theorem boundary_fin4_ne_02 : (0 : Fin 4) ≠ 2 := by decide
private theorem boundary_fin4_ne_03 : (0 : Fin 4) ≠ 3 := by decide
private theorem boundary_fin4_ne_10 : (1 : Fin 4) ≠ 0 := by decide
private theorem boundary_fin4_ne_12 : (1 : Fin 4) ≠ 2 := by decide
private theorem boundary_fin4_ne_13 : (1 : Fin 4) ≠ 3 := by decide
private theorem boundary_fin4_ne_20 : (2 : Fin 4) ≠ 0 := by decide
private theorem boundary_fin4_ne_21 : (2 : Fin 4) ≠ 1 := by decide
private theorem boundary_fin4_ne_23 : (2 : Fin 4) ≠ 3 := by decide
private theorem boundary_fin4_ne_30 : (3 : Fin 4) ≠ 0 := by decide
private theorem boundary_fin4_ne_31 : (3 : Fin 4) ≠ 1 := by decide
private theorem boundary_fin4_ne_32 : (3 : Fin 4) ≠ 2 := by decide

attribute [local simp]
  boundary_fin4_ne_01 boundary_fin4_ne_02 boundary_fin4_ne_03
  boundary_fin4_ne_10 boundary_fin4_ne_12 boundary_fin4_ne_13
  boundary_fin4_ne_20 boundary_fin4_ne_21 boundary_fin4_ne_23
  boundary_fin4_ne_30 boundary_fin4_ne_31 boundary_fin4_ne_32

theorem bulkPartial_mul {f q : Bulk → ℝ} {z : Bulk}
    (hf : AnalyticAt ℝ f z) (hq : AnalyticAt ℝ q z) (i : Fin 5) :
    bulkPartial (fun y => f y * q y) i z =
      bulkPartial f i z * q z + f z * bulkPartial q i z := by
  unfold bulkPartial
  rw [fderiv_fun_mul hf.differentiableAt hq.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem bulkPartial_sum {n : ℕ} {f : Fin n → Bulk → ℝ} {z : Bulk}
    (hf : ∀ a, AnalyticAt ℝ (f a) z) (i : Fin 5) :
    bulkPartial (fun y => ∑ a, f a y) i z = ∑ a, bulkPartial (f a) i z := by
  unfold bulkPartial
  rw [fderiv_fun_sum (fun a _ => (hf a).differentiableAt)]
  simp only [ContinuousLinearMap.sum_apply]

theorem bulkPartial_shape_at_flat {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : IsUnit (h z).det) (he : h z = eta4Matrix)
    (a b : Fin 4) :
    bulkPartial (fun y => gaussianShapeOperator h y a b) 0 z =
      lorentzSign4 a * bulkPartial (fun y => gaussianSecondForm h y a b) 0 z -
        2 * ∑ c : Fin 4, lorentzSign4 a * lorentzSign4 c *
          gaussianSecondForm h z a c * gaussianSecondForm h z c b := by
  have hi := analyticAt_matrix_inverse hh hn
  have hk := analyticAt_gaussianSecondForm hh
  change bulkPartial (fun y => ∑ c : Fin 4,
    (h y)⁻¹ a c * gaussianSecondForm h y c b) 0 z = _
  rw [bulkPartial_sum
    (f := fun c y => (h y)⁻¹ a c * gaussianSecondForm h y c b)
    (fun c => (analyticAt_matrix_entry hi a c).mul
      (analyticAt_matrix_entry hk c b)) 0]
  have hprod (c : Fin 4) :
      bulkPartial (fun y => (h y)⁻¹ a c * gaussianSecondForm h y c b) 0 z =
        bulkPartial (fun y => (h y)⁻¹ a c) 0 z * gaussianSecondForm h z c b +
        (h z)⁻¹ a c * bulkPartial (fun y => gaussianSecondForm h y c b) 0 z :=
    bulkPartial_mul (analyticAt_matrix_entry hi a c) (analyticAt_matrix_entry hk c b) 0
  simp_rw [hprod, bulkPartial_inverse_at_flat hh hn he]
  rw [he, eta4_inverse]
  rw [Finset.sum_add_distrib]
  have heval :
      (∑ c : Fin 4, eta4Matrix a c *
        bulkPartial (fun y => gaussianSecondForm h y c b) 0 z) =
      lorentzSign4 a * bulkPartial (fun y => gaussianSecondForm h y a b) 0 z := by
    classical
    rw [Finset.sum_eq_single a]
    · simp only [eta4Matrix, eta4, ite_true]
    · intro c hc hca
      simp only [eta4Matrix, eta4, if_neg (Ne.symm hca), zero_mul]
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  rw [heval]
  have hquad :
      (∑ c : Fin 4, (-2 * lorentzSign4 a * lorentzSign4 c *
        gaussianSecondForm h z a c) * gaussianSecondForm h z c b) =
      -2 * ∑ c : Fin 4, lorentzSign4 a * lorentzSign4 c *
        gaussianSecondForm h z a c * gaussianSecondForm h z c b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  rw [hquad]
  ring

theorem gaussian_normal_flat {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : IsUnit (h z).det) (he : h z = eta4Matrix)
    (hs : (gaussianSecondForm h z).IsSymm) :
    ricci (gaussianMetric h) z 0 0 =
      -(∑ a : Fin 4, lorentzSign4 a *
        bulkPartial (fun y => gaussianSecondForm h y a a) 0 z) +
      lorentzSquare4 (gaussianSecondForm h z) := by
  rw [ricci_gaussian_normal]
  unfold gaussianNormalRicciComponent
  simp_rw [bulkPartial_shape_at_flat hh hn he, gaussianShape_at_flat he]
  have hs01 := hs.apply 0 1
  have hs02 := hs.apply 0 2
  have hs03 := hs.apply 0 3
  have hs12 := hs.apply 1 2
  have hs13 := hs.apply 1 3
  have hs23 := hs.apply 2 3
  norm_num [lorentzSquare4, Fin.sum_univ_four, lorentzSign4]
  simp only [hs01, hs02, hs03, hs12, hs13, hs23]
  ring

theorem gaussian_tangential_flat {h : Bulk → Tensor4} {z : Bulk}
    (hn : ∀ᶠ y in 𝓝 z, IsUnit (h y).det) (he : h z = eta4Matrix)
    (hs : (gaussianSecondForm h z).IsSymm)
    (hc : ∀ a b c : Fin 4, gaussianTangentialChristoffel h z a b c = 0)
    (hdc : ∀ a b c d : Fin 4,
      bulkPartial (fun y => gaussianTangentialChristoffel h y a b c) d.succ z = 0)
    (a b : Fin 4) :
    ricci (gaussianMetric h) z a.succ b.succ =
      -bulkPartial (fun y => gaussianSecondForm h y a b) 0 z -
      lorentzTrace4 (gaussianSecondForm h z) * gaussianSecondForm h z a b +
      2 * ∑ c : Fin 4, lorentzSign4 c *
        gaussianSecondForm h z a c * gaussianSecondForm h z c b := by
  rw [ricci_gaussian_tangential h z hn]
  unfold gaussianTangentialRicciComponent
  simp only [hc, hdc, sub_self, Finset.sum_const_zero, add_zero,
    zero_mul, mul_zero, gaussianShape_at_flat he]
  have hsym (i j : Fin 4) : gaussianSecondForm h z j i = gaussianSecondForm h z i j :=
    hs.apply i j
  simp_rw [hsym b, hsym a]
  simp only [lorentzTrace4, Fin.sum_univ_four, lorentzSign4]
  norm_num
  ring

theorem gaussian_hamiltonian_flat {h : Bulk → Tensor4} {z : Bulk}
    (hh : AnalyticAt ℝ h z) (hn : ∀ᶠ y in 𝓝 z, IsUnit (h y).det)
    (he : h z = eta4Matrix) (hs : (gaussianSecondForm h z).IsSymm)
    (hc : ∀ a b c : Fin 4, gaussianTangentialChristoffel h z a b c = 0)
    (hdc : ∀ a b c d : Fin 4,
      bulkPartial (fun y => gaussianTangentialChristoffel h y a b c) d.succ z = 0)
    (hv : ricci (gaussianMetric h) z = 0) :
    lorentzSquare4 (gaussianSecondForm h z) -
      (lorentzTrace4 (gaussianSecondForm h z)) ^ 2 = 0 := by
  have hr := gaussian_normal_flat hh hn.self_of_nhds he hs
  have ht (a : Fin 4) := gaussian_tangential_flat hn he hs hc hdc a a
  rw [hv] at hr
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  have ht3 := ht 3
  rw [hv] at ht0 ht1 ht2 ht3
  have hs01 := hs.apply 0 1
  have hs02 := hs.apply 0 2
  have hs03 := hs.apply 0 3
  have hs12 := hs.apply 1 2
  have hs13 := hs.apply 1 3
  have hs23 := hs.apply 2 3
  norm_num [lorentzTrace4, lorentzSquare4, Fin.sum_univ_four, lorentzSign4]
    at hr ht0 ht1 ht2 ht3 ⊢
  simp only [hs01, hs02, hs03, hs12, hs13, hs23] at hr ht0 ht1 ht2 ht3 ⊢
  linear_combination ht0 - ht1 - ht2 - ht3 + hr

def boundaryDirection (a : Fin 4) : ℝ × Vec :=
  Fin.cases (1, 0) (fun i : Fin 3 => (0, unitVector i)) a

theorem boundaryPartial_eq_joint {f : Pressure} {t : ℝ} {x : Vec}
    (hf : AnalyticAt ℝ (fun z : ℝ × Vec => f z.1 z.2) (t, x)) (a : Fin 4) :
    boundaryPartial f a t x =
      fderiv ℝ (fun z : ℝ × Vec => f z.1 z.2) (t, x) (boundaryDirection a) := by
  refine Fin.cases ?_ (fun i => ?_) a
  · exact scalar_timeDerivative_eq_joint hf
  · exact scalar_spatialDerivative_eq_joint hf i

theorem boundaryPartial_sub {f q : Pressure} {t : ℝ} {x : Vec}
    (hf : AnalyticAt ℝ (fun z : ℝ × Vec => f z.1 z.2) (t, x))
    (hq : AnalyticAt ℝ (fun z : ℝ × Vec => q z.1 z.2) (t, x)) (a : Fin 4) :
    boundaryPartial (fun s y => f s y - q s y) a t x =
      boundaryPartial f a t x - boundaryPartial q a t x := by
  rw [boundaryPartial_eq_joint (f := fun s y => f s y - q s y) (hf.sub hq),
    boundaryPartial_eq_joint (f := f) hf, boundaryPartial_eq_joint (f := q) hq]
  simp only [fderiv_fun_sub hf.differentiableAt hq.differentiableAt,
    ContinuousLinearMap.sub_apply]

theorem boundaryPartial_const_mul {f : Pressure} {t : ℝ} {x : Vec}
    (hf : AnalyticAt ℝ (fun z : ℝ × Vec => f z.1 z.2) (t, x)) (c : ℝ) (a : Fin 4) :
    boundaryPartial (fun s y => c * f s y) a t x = c * boundaryPartial f a t x := by
  rw [boundaryPartial_eq_joint (f := fun s y => c * f s y) (analyticAt_const.mul hf),
    boundaryPartial_eq_joint (f := f) hf]
  rw [fderiv_fun_mul (differentiableAt_const c) hf.differentiableAt]
  simp

theorem boundaryPartial_sum {n : ℕ} {f : Fin n → Pressure} {t : ℝ} {x : Vec}
    (hf : ∀ b, AnalyticAt ℝ (fun z : ℝ × Vec => f b z.1 z.2) (t, x)) (a : Fin 4) :
    boundaryPartial (fun s y => ∑ b, f b s y) a t x =
      ∑ b, boundaryPartial (f b) a t x := by
  have ha : AnalyticAt ℝ (fun z : ℝ × Vec => ∑ b, f b z.1 z.2) (t, x) := by
    apply Finset.analyticAt_fun_sum
    intro b hb
    exact hf b
  rw [boundaryPartial_eq_joint (f := fun s y => ∑ b, f b s y) ha]
  rw [fderiv_fun_sum (fun b _ => (hf b).differentiableAt)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  exact (boundaryPartial_eq_joint (f := f b) (hf b) a).symm

theorem lorentzTrace4_eq_sum (K : Tensor4) :
    lorentzTrace4 K = ∑ a : Fin 4, lorentzSign4 a * K a a := by
  norm_num [lorentzTrace4, Fin.sum_univ_four, lorentzSign4] <;> ring

theorem analyticAt_boundaryTrace {K : BoundaryTensor} {t : ℝ} {x : Vec}
    (hK : AnalyticAt ℝ (fun z : ℝ × Vec => K z.1 z.2) (t, x)) :
    AnalyticAt ℝ (fun z : ℝ × Vec => lorentzTrace4 (K z.1 z.2)) (t, x) := by
  exact (((analyticAt_matrix_entry hK 0 0).neg.add
    (analyticAt_matrix_entry hK 1 1)).add (analyticAt_matrix_entry hK 2 2)).add
      (analyticAt_matrix_entry hK 3 3)

theorem boundaryCodazzi_expanded {K : BoundaryTensor} {t : ℝ} {x : Vec}
    (hK : AnalyticAt ℝ (fun z : ℝ × Vec => K z.1 z.2) (t, x)) (a : Fin 4) :
    boundaryCodazzi K t x a =
      (∑ b : Fin 4, lorentzSign4 b * boundaryPartial (fun s y => K s y b a) b t x) -
      ∑ b : Fin 4, lorentzSign4 b * boundaryPartial (fun s y => K s y b b) a t x := by
  have ht := analyticAt_boundaryTrace hK
  have hd (b : Fin 4) :
      boundaryPartial (fun s y => K s y b a - lorentzTrace4 (K s y) * eta4 b a) b t x =
        boundaryPartial (fun s y => K s y b a) b t x -
          eta4 b a * boundaryPartial (fun s y => lorentzTrace4 (K s y)) b t x := by
    have he : (fun s y => K s y b a - lorentzTrace4 (K s y) * eta4 b a) =
        (fun s y => K s y b a - eta4 b a * lorentzTrace4 (K s y)) := by
      funext s y
      ring
    rw [he, boundaryPartial_sub
      (f := fun s y => K s y b a)
      (q := fun s y => eta4 b a * lorentzTrace4 (K s y))
      (analyticAt_matrix_entry hK b a) (analyticAt_const.mul ht),
      boundaryPartial_const_mul (f := fun s y => lorentzTrace4 (K s y)) ht]
  unfold boundaryCodazzi
  simp_rw [hd]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  have htrace : (fun s y => lorentzTrace4 (K s y)) =
      (fun s y => ∑ b : Fin 4, lorentzSign4 b * K s y b b) := by
    funext s y
    exact lorentzTrace4_eq_sum _
  have htder (c : Fin 4) :
      boundaryPartial (fun s y => lorentzTrace4 (K s y)) c t x =
        ∑ b : Fin 4, lorentzSign4 b * boundaryPartial (fun s y => K s y b b) c t x := by
    rw [htrace, boundaryPartial_sum
      (f := fun b s y => lorentzSign4 b * K s y b b)
      (fun b => analyticAt_const.mul (analyticAt_matrix_entry hK b b))]
    apply Finset.sum_congr rfl
    intro b hb
    exact boundaryPartial_const_mul (f := fun s y => K s y b b)
      (analyticAt_matrix_entry hK b b) (lorentzSign4 b) c
  simp_rw [htder]
  fin_cases a <;> norm_num [eta4, lorentzSign4, Fin.sum_univ_four] <;> ring

end
end NSEGR.Assembly
