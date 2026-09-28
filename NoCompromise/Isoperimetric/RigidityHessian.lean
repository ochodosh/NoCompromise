import NoCompromise.Isoperimetric.ABPContact

/-!
# The Hessian on the ABP contact set: AM-GM and its equality case

Public versions of the Hessian-as-operator facts used in the ABP argument, together with
the equality case of the AM-GM inequality for the Hessian on the contact set
(blueprint `thm:isoperimetric-rigidity`, Step 4).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal InnerProductSpace

namespace LiquidDrop

/-- The derivative of `∇z` at `x`: the Hessian as an operator via the Riesz identification. -/
def abpHessianCLM (z : AmbientSpace → ℝ) (x : AmbientSpace) : AmbientSpace →L[ℝ] AmbientSpace :=
  (InnerProductSpace.toDual ℝ AmbientSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
    ∘L fderiv ℝ (fderiv ℝ z) x

lemma inner_abpHessianCLM (z : AmbientSpace → ℝ) (x v w : AmbientSpace) :
    ⟪abpHessianCLM z x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ z) x v w := by
  exact InnerProductSpace.toDual_symm_apply

theorem hasFDerivAt_gradient_abpHessianCLM {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) {x : AmbientSpace} (hx : x ∈ G) :
    HasFDerivAt (gradient z) (abpHessianCLM z x) x := by
  have hd := ((hz.contDiffAt (hGo.mem_nhds hx)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let R := (InnerProductSpace.toDual ℝ AmbientSpace).symm.toContinuousLinearEquiv
  exact R.toContinuousLinearMap.hasFDerivAt.comp x hd.hasFDerivAt

theorem continuousOn_abpHessianCLM {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) : ContinuousOn (abpHessianCLM z) G := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ z y) G :=
    hz.fderiv_of_isOpen hGo (by norm_num)
  have h2 : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ z) y) G :=
    h1.continuousOn_fderiv_of_isOpen hGo le_rfl
  exact continuousOn_const.clm_comp h2

/-- AM-GM for three nonnegative reals. -/
lemma amgm_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  have h (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
      27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
    have h1 := mul_nonneg hc (sq_nonneg (a - b))
    have h2 := mul_nonneg hc (mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hcb))
    have h3 := pow_nonneg (by linarith : 0 ≤ a + b - 2 * c) 3
    nlinarith only [h1, h2, h3]
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · have := h b c a ha hab hac
      nlinarith only [this]
    · have := h a b c hc hca (hca.trans hab)
      nlinarith only [this]
  · rcases le_total b c with hbc | hcb
    · have := h a c b hb hba hbc
      nlinarith only [this]
    · have := h a b c hc (hcb.trans hba) hcb
      nlinarith only [this]

theorem abs_det_abpHessianCLM_le {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) {x : AmbientSpace}
    (hx : x ∈ abpContactSet G z) :
    |(abpHessianCLM z x).det| ≤ (laplacianTrace z x / 3) ^ 3 := by
  let T := (abpHessianCLM z x).toLinearMap
  have hs : T.IsSymmetric := by
    intro v w
    change ⟪abpHessianCLM z x v, w⟫_ℝ = ⟪v, abpHessianCLM z x w⟫_ℝ
    rw [real_inner_comm (abpHessianCLM z x w) v, inner_abpHessianCLM, inner_abpHessianCLM]
    exact (hz.contDiffAt (hGo.mem_nhds hx.1)).isSymmSndFDerivAt (by simp) v w
  have hp : T.IsPositive := by
    refine ⟨hs, fun v => ?_⟩
    change 0 ≤ ⟪abpHessianCLM z x v, v⟫_ℝ
    rw [inner_abpHessianCLM]
    exact hessianForm_nonneg_of_mem_abpContactSet hGo hz hx v
  have hn : Module.finrank ℝ AmbientSpace = 3 := finrank_euclideanSpace_fin
  have ht : T.trace ℝ AmbientSpace = laplacianTrace z x := by
    rw [LinearMap.trace_eq_sum_inner T (EuclideanSpace.basisFun (Fin 3) ℝ)]
    unfold laplacianTrace
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.basisFun_apply, real_inner_comm]
    exact inner_abpHessianCLM z x _ _
  have he : ∑ i, hs.eigenvalues hn i = laplacianTrace z x := by
    simpa using (hs.trace_eq_sum_eigenvalues hn).symm.trans ht
  have hd : (abpHessianCLM z x).det = ∏ i, hs.eigenvalues hn i :=
    hs.det_eq_prod_eigenvalues hn
  rw [hd, abs_of_nonneg (Finset.prod_nonneg fun i _ => hp.nonneg_eigenvalues hn i)]
  rw [← he, Fin.prod_univ_three, Fin.sum_univ_three]
  exact amgm_three_le (hp.nonneg_eigenvalues hn 0) (hp.nonneg_eigenvalues hn 1)
    (hp.nonneg_eigenvalues hn 2)

/-- Equality in AM-GM when the third variable is the smallest. -/
private lemma amgm_three_eq_of_min {a b c : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b)
    (h : 27 * (a * b * c) = (a + b + c) ^ 3) : a = c ∧ b = c := by
  have h1 := mul_nonneg hc (sq_nonneg (a - b))
  have h2 := mul_nonneg hc (mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hcb))
  have h3 : (a + b - 2 * c) ^ 3 ≤ 0 := by nlinarith only [h, h1, h2]
  have h4 : a + b - 2 * c ≤ 0 := by
    by_contra hne
    have := pow_pos (not_le.mp hne) 3
    linarith
  constructor <;> linarith

/-- Equality in AM-GM for three nonnegative reals. -/
lemma amgm_three_eq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b * c = ((a + b + c) / 3) ^ 3) : a = b ∧ b = c := by
  have h' : 27 * (a * b * c) = (a + b + c) ^ 3 := by rw [h]; ring
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · obtain ⟨h1, h2⟩ := amgm_three_eq_of_min (a := b) (b := c) (c := a) ha hab hac
        (by linear_combination h')
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := amgm_three_eq_of_min (a := a) (b := b) (c := c) hc hca
        (hca.trans hab) h'
      constructor <;> linarith
  · rcases le_total b c with hbc | hcb
    · obtain ⟨h1, h2⟩ := amgm_three_eq_of_min (a := a) (b := c) (c := b) hb hba hbc
        (by linear_combination h')
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := amgm_three_eq_of_min (a := a) (b := b) (c := c) hc
        (hcb.trans hba) hcb h'
      constructor <;> linarith

/-- Blueprint thm:isoperimetric-rigidity, Step 4 (equality in AM-GM for a positive
semidefinite matrix): on the contact set, `|det D²z| = (Δz/3)^3` forces `D²z = (Δz/3) I`. -/
theorem abpHessianCLM_eq_smul_id_of_abs_det_eq {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) {x : AmbientSpace}
    (hx : x ∈ abpContactSet G z)
    (h : |(abpHessianCLM z x).det| = (laplacianTrace z x / 3) ^ 3) :
    abpHessianCLM z x = (laplacianTrace z x / 3) • ContinuousLinearMap.id ℝ AmbientSpace := by
  let T := (abpHessianCLM z x).toLinearMap
  have hs : T.IsSymmetric := by
    intro v w
    change ⟪abpHessianCLM z x v, w⟫_ℝ = ⟪v, abpHessianCLM z x w⟫_ℝ
    rw [real_inner_comm (abpHessianCLM z x w) v, inner_abpHessianCLM, inner_abpHessianCLM]
    exact (hz.contDiffAt (hGo.mem_nhds hx.1)).isSymmSndFDerivAt (by simp) v w
  have hp : T.IsPositive := by
    refine ⟨hs, fun v => ?_⟩
    change 0 ≤ ⟪abpHessianCLM z x v, v⟫_ℝ
    rw [inner_abpHessianCLM]
    exact hessianForm_nonneg_of_mem_abpContactSet hGo hz hx v
  have hn : Module.finrank ℝ AmbientSpace = 3 := finrank_euclideanSpace_fin
  have ht : T.trace ℝ AmbientSpace = laplacianTrace z x := by
    rw [LinearMap.trace_eq_sum_inner T (EuclideanSpace.basisFun (Fin 3) ℝ)]
    unfold laplacianTrace
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.basisFun_apply, real_inner_comm]
    exact inner_abpHessianCLM z x _ _
  have he : ∑ i, hs.eigenvalues hn i = laplacianTrace z x := by
    simpa using (hs.trace_eq_sum_eigenvalues hn).symm.trans ht
  have hd : (abpHessianCLM z x).det = ∏ i, hs.eigenvalues hn i :=
    hs.det_eq_prod_eigenvalues hn
  set μ := laplacianTrace z x / 3 with hμ
  have h0 := hp.nonneg_eigenvalues hn 0
  have h1 := hp.nonneg_eigenvalues hn 1
  have h2 := hp.nonneg_eigenvalues hn 2
  rw [hd, abs_of_nonneg (Finset.prod_nonneg fun i _ => hp.nonneg_eigenvalues hn i), hμ, ← he,
    Fin.prod_univ_three, Fin.sum_univ_three] at h
  rw [Fin.sum_univ_three] at he
  obtain ⟨e01, e12⟩ := amgm_three_eq h0 h1 h2 h
  have hev : ∀ i, hs.eigenvalues hn i = μ := by
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  have hT : T = μ • LinearMap.id := by
    refine (hs.eigenvectorBasis hn).toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, hs.apply_eigenvectorBasis hn i, hev i]
    simp
  ext1 v
  have := LinearMap.congr_fun hT v
  simpa [T] using this

end LiquidDrop
