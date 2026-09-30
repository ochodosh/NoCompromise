module

public import NoCompromise.Elliptic.BoundaryNeumannC2HolderPrimitive

@[expose] public section

/-!
# C²,α of the normal coefficient

For `A ∈ C²,α` on the closed unit ball, the normal coefficient
`b y = ⟪A (emb y) e₃, e₃⟫` is C²,α on the closed unit base ball with the same bound.
Composition with the isometric base embedding and a bounded linear map of norm at most one
does not increase Hölder norms.
-/

noncomputable section
open Set Metric InnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Precomposition by the base embedding after a bounded linear map: `T ↦ M ∘ T ∘ emb`. -/
def boundaryNeumannEmbComp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (M : F →L[ℝ] G) :
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] F) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] G) :=
  ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3)) G).flip
    graphBaseEmbedding).comp (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin 3)) F G M)

lemma boundaryNeumannEmbComp_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (M : F →L[ℝ] G)
    (T : EuclideanSpace ℝ (Fin 3) →L[ℝ] F) :
    boundaryNeumannEmbComp M T = (M.comp T).comp graphBaseEmbedding := rfl

lemma norm_graphBaseEmbedding_clm_le : ‖graphBaseEmbedding‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [norm_graphBaseEmbedding, one_mul]

lemma norm_boundaryNeumannEmbComp_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (M : F →L[ℝ] G) (hM : ‖M‖ ≤ 1) :
    ‖boundaryNeumannEmbComp M‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
  rw [boundaryNeumannEmbComp_apply, one_mul]
  calc
    _ ≤ ‖M.comp T‖ * ‖graphBaseEmbedding‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖M‖ * ‖T‖) * 1 := by
      gcongr
      · exact ContinuousLinearMap.opNorm_comp_le _ _
      · exact norm_graphBaseEmbedding_clm_le
    _ ≤ 1 * ‖T‖ * 1 := by gcongr
    _ = ‖T‖ := by ring

/-- C¹,α transfers between functions agreeing on an open neighbourhood of the set. -/
lemma boundaryNeumann_hasC1HolderOn_congr_of_eqOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} {f g : E → F} {S O : Set E} (hO : IsOpen O) (hSO : S ⊆ O)
    (he : EqOn f g O) (hf : HasC1HolderOn α f S) :
    HasC1HolderOn α g S ∧ nondivC1HolderNorm α g S ≤ nondivC1HolderNorm α f S := by
  obtain ⟨h0, n0⟩ := boundaryNeumann_holder_congr hf.function_holder (he.mono hSO)
  have hd : EqOn (fderiv ℝ f) (fderiv ℝ g) S := fun x hx =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hO.mem_nhds (hSO hx)) he)
  obtain ⟨h1, n1⟩ := boundaryNeumann_holder_congr hf.derivative_holder hd
  exact ⟨⟨hf.contDiff.congr fun x hx => (he (hSO hx)).symm, h0, h1⟩, add_le_add n0 n1⟩

lemma graphBaseEmbedding_mapsTo_closedBall :
    MapsTo graphBaseEmbedding (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (closedBall 0 1) := fun x hx => by
  simpa only [mem_closedBall, dist_zero_right, norm_graphBaseEmbedding] using hx

/-- Composition of a C¹,α map on the closed unit ball with the base embedding and a bounded
linear map of norm at most one, with the derivative formula. -/
theorem boundaryNeumann_hasC1HolderOn_clm_comp_embedding {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} (hα : 0 ≤ α) {g : EuclideanSpace ℝ (Fin 3) → F}
    {O : Set (EuclideanSpace ℝ (Fin 3))} (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hg : ContDiffOn ℝ 1 g O) (hgh : HasC1HolderOn α g (closedBall 0 1))
    (M : F →L[ℝ] G) (hM : ‖M‖ ≤ 1) :
    HasC1HolderOn α (fun y => M (g (graphBaseEmbedding y))) (closedBall 0 1) ∧
      nondivC1HolderNorm α (fun y => M (g (graphBaseEmbedding y))) (closedBall 0 1) ≤
        nondivC1HolderNorm α g (closedBall 0 1) ∧
      ∀ y ∈ graphBaseEmbedding ⁻¹' O,
        fderiv ℝ (fun y => M (g (graphBaseEmbedding y))) y =
          boundaryNeumannEmbComp M (fderiv ℝ g (graphBaseEmbedding y)) := by
  have hd : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖graphBaseEmbedding x - graphBaseEmbedding y‖ ≤ ‖x - y‖ := fun x _ y _ => by
    rw [← map_sub, norm_graphBaseEmbedding]
  have hderiv : ∀ y ∈ graphBaseEmbedding ⁻¹' O,
      fderiv ℝ (fun y => M (g (graphBaseEmbedding y))) y =
        boundaryNeumannEmbComp M (fderiv ℝ g (graphBaseEmbedding y)) := by
    intro y hy
    have hgd : DifferentiableAt ℝ g (graphBaseEmbedding y) :=
      (hg.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hy)
    have hc : HasFDerivAt (fun y => M (g (graphBaseEmbedding y)))
        ((M.comp (fderiv ℝ g (graphBaseEmbedding y))).comp graphBaseEmbedding) y :=
      M.hasFDerivAt.comp y (hgd.hasFDerivAt.comp y graphBaseEmbedding.hasFDerivAt)
    exact hc.fderiv
  obtain ⟨h0c, n0c⟩ := nondiv_holder_comp_contraction hα hgh.function_holder
    graphBaseEmbedding_mapsTo_closedBall hd
  obtain ⟨h0, n0⟩ := nondiv_holder_comp_clm h0c M
  obtain ⟨h1c, n1c⟩ := nondiv_holder_comp_contraction hα hgh.derivative_holder
    graphBaseEmbedding_mapsTo_closedBall hd
  obtain ⟨h1, n1⟩ := nondiv_holder_comp_clm h1c (boundaryNeumannEmbComp M)
  have hsubV : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ graphBaseEmbedding ⁻¹' O :=
    fun y hy => hsub (graphBaseEmbedding_mapsTo_closedBall hy)
  obtain ⟨h1', n1'⟩ := boundaryNeumann_holder_congr h1
    (g := fderiv ℝ (fun y => M (g (graphBaseEmbedding y))))
    (fun y hy => (hderiv y (hsubV hy)).symm)
  have hcd : ContDiffOn ℝ 1 (fun y => M (g (graphBaseEmbedding y))) (closedBall 0 1) :=
    M.contDiff.comp_contDiffOn
      ((hg.comp graphBaseEmbedding.contDiff.contDiffOn (fun _ hy => hy)).mono hsubV)
  refine ⟨⟨hcd, h0, h1'⟩, ?_, hderiv⟩
  have hn0 := hgh.function_holder.norm_nonneg
  have hn1 := hgh.derivative_holder.norm_nonneg
  have hE := norm_boundaryNeumannEmbComp_le M hM
  unfold nondivC1HolderNorm
  have ha : holderNorm α (fun y => M (g (graphBaseEmbedding y))) (closedBall 0 1) ≤
      holderNorm α g (closedBall 0 1) :=
    n0.trans ((mul_le_mul hM n0c h0c.norm_nonneg zero_le_one).trans_eq (one_mul _))
  have hb : holderNorm α (fderiv ℝ (fun y => M (g (graphBaseEmbedding y)))) (closedBall 0 1) ≤
      holderNorm α (fderiv ℝ g) (closedBall 0 1) :=
    n1'.trans (n1.trans ((mul_le_mul hE n1c h1c.norm_nonneg zero_le_one).trans_eq (one_mul _)))
  exact add_le_add ha hb

/-- The linear functional `T ↦ ⟪T e₃, e₃⟫`, of norm at most one. -/
def boundaryNeumannNormalFunctional :
    (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ :=
  (innerSL ℝ (EuclideanSpace.single (Fin.last 2) (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace.single (Fin.last 2) (1 : ℝ)))

lemma norm_boundaryNeumannNormalFunctional_le : ‖boundaryNeumannNormalFunctional‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
  simp only [boundaryNeumannNormalFunctional, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply, one_mul]
  calc
    _ ≤ ‖EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖ *
        ‖T (EuclideanSpace.single (Fin.last 2) (1 : ℝ))‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖T‖ * 1) := by
      rw [PiLp.norm_single, norm_one]
      gcongr
      simpa only [PiLp.norm_single, norm_one] using
        T.le_opNorm (EuclideanSpace.single (Fin.last 2) (1 : ℝ))
    _ = ‖T‖ := by ring

lemma boundaryNeumannNormalCoefficient_eq_functional
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannNormalCoefficient A =
      fun y => boundaryNeumannNormalFunctional (A (graphBaseEmbedding y)) := by
  funext y
  simp only [boundaryNeumannNormalCoefficient, boundaryNeumannNormalFunctional,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply]
  exact real_inner_comm _ _

/-- `thm:boundary-neumann`, C²,α of the normal coefficient: for `A ∈ C²,α` on the closed unit
ball with both C¹,α norms at most `K`, the normal coefficient `b y = ⟪A (emb y) e₃, e₃⟫` is C²
on the preimage of the neighbourhood, and `b`, `Db` are C¹,α on the closed unit base ball with
norms at most `K`. -/
theorem boundaryNeumannNormalCoefficient_c2_holder {α K : ℝ} (hα : 0 ≤ α)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {O : Set (EuclideanSpace ℝ (Fin 3))} (hO : IsOpen O) (hsub : closedBall 0 1 ⊆ O)
    (hA : ContDiffOn ℝ 2 A O) (hA1 : HasC1HolderOn α A (closedBall 0 1))
    (hA2 : HasC1HolderOn α (fderiv ℝ A) (closedBall 0 1))
    (hK1 : nondivC1HolderNorm α A (closedBall 0 1) ≤ K)
    (hK2 : nondivC1HolderNorm α (fderiv ℝ A) (closedBall 0 1) ≤ K) :
    ContDiffOn ℝ 2 (boundaryNeumannNormalCoefficient A) (graphBaseEmbedding ⁻¹' O) ∧
      HasC1HolderOn α (boundaryNeumannNormalCoefficient A) (closedBall 0 1) ∧
      nondivC1HolderNorm α (boundaryNeumannNormalCoefficient A) (closedBall 0 1) ≤ K ∧
      HasC1HolderOn α (fderiv ℝ (boundaryNeumannNormalCoefficient A)) (closedBall 0 1) ∧
      nondivC1HolderNorm α (fderiv ℝ (boundaryNeumannNormalCoefficient A))
        (closedBall 0 1) ≤ K := by
  have hc2 := boundaryNeumannNormalCoefficient_contDiffOn_n hA
  rw [boundaryNeumannNormalCoefficient_eq_functional] at hc2 ⊢
  have hA1' : ContDiffOn ℝ 1 A O := hA.of_le (by norm_num)
  obtain ⟨hb, nb, hdb⟩ := boundaryNeumann_hasC1HolderOn_clm_comp_embedding hα hO hsub hA1' hA1
    boundaryNeumannNormalFunctional norm_boundaryNeumannNormalFunctional_le
  have hdA : ContDiffOn ℝ 1 (fderiv ℝ A) O := hA.fderiv_of_isOpen hO (by norm_num)
  obtain ⟨hc, nc, -⟩ := boundaryNeumann_hasC1HolderOn_clm_comp_embedding hα hO hsub hdA hA2
    (boundaryNeumannEmbComp boundaryNeumannNormalFunctional)
    (norm_boundaryNeumannEmbComp_le _ norm_boundaryNeumannNormalFunctional_le)
  have hV : IsOpen (graphBaseEmbedding ⁻¹' O) := hO.preimage graphBaseEmbedding.continuous
  have hsubV : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ graphBaseEmbedding ⁻¹' O :=
    fun y hy => hsub (graphBaseEmbedding_mapsTo_closedBall hy)
  obtain ⟨hd, nd⟩ := boundaryNeumann_hasC1HolderOn_congr_of_eqOn hV hsubV
    (fun y hy => (hdb y hy).symm) hc
  exact ⟨hc2, hb, nb.trans hK1, hd, nd.trans (nc.trans hK2)⟩

/-- `T ↦ M ∘ T ∘ e` for bounded linear maps `e`, `M`. -/
def boundaryNeumannSandwich {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (e : D →L[ℝ] E) (M : F →L[ℝ] G) :
    (E →L[ℝ] F) →L[ℝ] (D →L[ℝ] G) :=
  ((ContinuousLinearMap.compL ℝ D E G).flip e).comp (ContinuousLinearMap.compL ℝ E F G M)

lemma norm_boundaryNeumannSandwich_le {D E F G : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] (e : D →L[ℝ] E)
    (M : F →L[ℝ] G) (he : ‖e‖ ≤ 1) (hM : ‖M‖ ≤ 1) :
    ‖boundaryNeumannSandwich e M‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
  change ‖(M.comp T).comp e‖ ≤ 1 * ‖T‖
  calc
    _ ≤ ‖M.comp T‖ * ‖e‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖M‖ * ‖T‖) * 1 := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖T‖ * 1 := by gcongr
    _ = 1 * ‖T‖ := by ring

/-- Composition of a C¹,α map with bounded linear maps of norm at most one on both sides. -/
theorem boundaryNeumann_hasC1HolderOn_clm_sandwich {D E F G : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : ℝ} (hα : 0 ≤ α) {g : E → F} {O W : Set E} (hO : IsOpen O) (hWO : W ⊆ O)
    (hg : ContDiffOn ℝ 1 g O) (hgh : HasC1HolderOn α g W)
    (e : D →L[ℝ] E) (he : ‖e‖ ≤ 1) {V : Set D} (hVW : MapsTo e V W)
    (M : F →L[ℝ] G) (hM : ‖M‖ ≤ 1) :
    HasC1HolderOn α (fun y => M (g (e y))) V ∧
      nondivC1HolderNorm α (fun y => M (g (e y))) V ≤ nondivC1HolderNorm α g W ∧
      ContDiffOn ℝ 1 (fun y => M (g (e y))) (e ⁻¹' O) := by
  have hd : ∀ x ∈ V, ∀ y ∈ V, ‖e x - e y‖ ≤ ‖x - y‖ := fun x _ y _ => by
    rw [← map_sub]
    exact (e.le_opNorm _).trans ((mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq
      (one_mul _))
  have hderiv : ∀ y ∈ e ⁻¹' O,
      fderiv ℝ (fun y => M (g (e y))) y = boundaryNeumannSandwich e M (fderiv ℝ g (e y)) := by
    intro y hy
    have hgd : DifferentiableAt ℝ g (e y) :=
      (hg.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hy)
    exact (M.hasFDerivAt.comp y (hgd.hasFDerivAt.comp y e.hasFDerivAt)).fderiv
  obtain ⟨h0c, n0c⟩ := nondiv_holder_comp_contraction hα hgh.function_holder hVW hd
  obtain ⟨h0, n0⟩ := nondiv_holder_comp_clm h0c M
  obtain ⟨h1c, n1c⟩ := nondiv_holder_comp_contraction hα hgh.derivative_holder hVW hd
  obtain ⟨h1, n1⟩ := nondiv_holder_comp_clm h1c (boundaryNeumannSandwich e M)
  have hsubV : V ⊆ e ⁻¹' O := fun y hy => hWO (hVW hy)
  obtain ⟨h1', n1'⟩ := boundaryNeumann_holder_congr h1
    (g := fderiv ℝ (fun y => M (g (e y))))
    (fun y hy => (hderiv y (hsubV hy)).symm)
  have hcd : ContDiffOn ℝ 1 (fun y => M (g (e y))) (e ⁻¹' O) :=
    M.contDiff.comp_contDiffOn (hg.comp e.contDiff.contDiffOn (fun _ hy => hy))
  refine ⟨⟨hcd.mono hsubV, h0, h1'⟩, ?_, hcd⟩
  have hE := norm_boundaryNeumannSandwich_le e M he hM
  unfold nondivC1HolderNorm
  have ha : holderNorm α (fun y => M (g (e y))) V ≤ holderNorm α g W :=
    n0.trans ((mul_le_mul hM n0c h0c.norm_nonneg zero_le_one).trans_eq (one_mul _))
  have hb : holderNorm α (fderiv ℝ (fun y => M (g (e y)))) V ≤
      holderNorm α (fderiv ℝ g) W :=
    n1'.trans (n1.trans ((mul_le_mul hE n1c h1c.norm_nonneg zero_le_one).trans_eq (one_mul _)))
  exact add_le_add ha hb

lemma boundaryNeumann_norm_graphProjectionN_le (x : EuclideanSpace ℝ (Fin 3)) :
    ‖graphProjectionN 2 x‖ ≤ ‖x‖ := by
  have h := norm_sq_graphProjectionN x
  nlinarith [norm_nonneg x, norm_nonneg (graphProjectionN 2 x), sq_nonneg (x (Fin.last 2))]

lemma boundaryNeumann_norm_graphProjectionN_clm_le : ‖graphProjectionN 2‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x =>
    (boundaryNeumann_norm_graphProjectionN_le x).trans_eq (one_mul _).symm

/-- `t ↦ t e₃`, of norm at most one. -/
def boundaryNeumannVerticalMap : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single (Fin.last 2) (1 : ℝ))

lemma norm_boundaryNeumannVerticalMap_le : ‖boundaryNeumannVerticalMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => ?_
  simp [boundaryNeumannVerticalMap, norm_smul]

lemma boundaryNeumannVerticalMap_apply (t : ℝ) :
    boundaryNeumannVerticalMap t = t • EuclideanSpace.single (Fin.last 2) (1 : ℝ) := rfl

/-- `thm:boundary-neumann`, second assertion, C¹,α of the inhomogeneous datum
`F = P + h e₃ − A ∇q` on `S = closure (boundaryHalfBall (1/4))`, with the explicit bound
`c K + K + 3 K Q`, where `c` is the primitive constant. The hypotheses on `A`, `f`, `h` are
implied by the C²,α / C¹,α / C²,α formats (with norms at most `K`); `Q` bounds the C¹,α norm
of `Dq` on `S`, where `q` is the lift. -/
theorem boundaryNeumannInhomDatum_hasC1HolderOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (K Q : ℝ)
      (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ) (h : EuclideanSpace ℝ (Fin 2) → ℝ)
      (O : Set (EuclideanSpace ℝ (Fin 3))) (U : Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen O → closedBall 0 1 ⊆ O →
      ContDiffOn ℝ 1 A O → HasC1HolderOn α A (closedBall 0 1) →
      nondivC1HolderNorm α A (closedBall 0 1) ≤ K →
      ContDiffOn ℝ 1 f O → HasC1HolderOn α f (closedBall 0 1) →
      nondivC1HolderNorm α f (closedBall 0 1) ≤ K →
      IsOpen U → closedBall 0 1 ⊆ U →
      ContDiffOn ℝ 1 h U → HasC1HolderOn α h (closedBall 0 1) →
      nondivC1HolderNorm α h (closedBall 0 1) ≤ K →
      ContDiffOn ℝ 2 (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)) (ball 0 1) →
      HasC1HolderOn α (fderiv ℝ (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)))
        (closure (boundaryHalfBall (1 / 4))) →
      nondivC1HolderNorm α
        (fderiv ℝ (boundaryNeumannLift h (boundaryNeumannNormalCoefficient A)))
        (closure (boundaryHalfBall (1 / 4))) ≤ Q →
      HasC1HolderOn α (boundaryNeumannInhomDatum A f h) (closure (boundaryHalfBall (1 / 4))) ∧
        nondivC1HolderNorm α (boundaryNeumannInhomDatum A f h)
          (closure (boundaryHalfBall (1 / 4))) ≤ c * K + K + 3 * K * Q := by
  obtain ⟨c, hc0, hP⟩ := boundaryNeumannPrimitive_hasC1HolderOn hα hα1
  refine ⟨c, hc0, ?_⟩
  intro K Q A f h O U hO hsub hA hAh hAK hf hfh hfK hU hsubU hh hhh hhK hq hqh hqQ
  set q := boundaryNeumannLift h (boundaryNeumannNormalCoefficient A) with hqdef
  have hSB : closure (boundaryHalfBall (1 / 4)) ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    boundaryNeumann_closure_halfBall_quarter_subset
  obtain ⟨hPc, hPh, hPn⟩ := hP f K O hO hsub hf hfh hfK
  have hmaps : MapsTo (graphProjectionN 2) (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (closedBall 0 1) := fun x hx => by
    rw [mem_closedBall, dist_zero_right]
    exact (boundaryNeumann_norm_graphProjectionN_le x).trans (mem_ball_zero_iff.mp hx).le
  obtain ⟨h2h, h2n, h2c⟩ := boundaryNeumann_hasC1HolderOn_clm_sandwich hα.le hU hsubU hh hhh
    (graphProjectionN 2) boundaryNeumann_norm_graphProjectionN_clm_le (hmaps.mono_left hSB)
    boundaryNeumannVerticalMap norm_boundaryNeumannVerticalMap_le
  simp only [boundaryNeumannVerticalMap_apply] at h2h h2n h2c
  have h2cB := h2c.mono fun x hx => hsubU (hmaps hx)
  have hq1 : ContDiffOn ℝ 1 (fderiv ℝ q) (ball 0 1) :=
    hq.fderiv_of_isOpen isOpen_ball (by norm_num)
  let L := (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖(toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm v‖ ≤ 1 * ‖v‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
  obtain ⟨hgh, hgn, hgc⟩ := boundaryNeumann_hasC1HolderOn_clm_sandwich hα.le isOpen_ball hSB
    hq1 hqh (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) ContinuousLinearMap.norm_id_le
    (mapsTo_id _) L hL
  have hgeq : (fun y => L (fderiv ℝ q ((ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 3))) y))) = gradient q := rfl
  rw [hgeq] at hgh hgn hgc
  have hgcB : ContDiffOn ℝ 1 (gradient q) (ball 0 1) := hgc.mono fun x hx => hx
  obtain ⟨hAS, hASn⟩ := hAh.mono (hSB.trans ball_subset_closedBall)
  have hAB : ContDiffOn ℝ 1 A (ball 0 1) := hA.mono (ball_subset_closedBall.trans hsub)
  obtain ⟨h3h, h3n⟩ := boundaryNeumann_hasC1HolderOn_bilinear isOpen_ball hSB hAB hgcB hAS hgh
    (ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
  simp only [ContinuousLinearMap.id_apply] at h3h h3n
  have h3c : ContDiffOn ℝ 1 (fun x => A x (gradient q x)) (ball 0 1) := hAB.clm_apply hgcB
  obtain ⟨h4h, h4n⟩ := boundaryNeumann_hasC1HolderOn_add isOpen_ball hSB hPc h2cB hPh h2h
  obtain ⟨h5h, h5n⟩ := boundaryNeumann_hasC1HolderOn_sub isOpen_ball hSB (hPc.add h2cB) h3c
    h4h h3h
  have hdeq : boundaryNeumannInhomDatum A f h = fun x =>
      (boundaryNeumannPrimitive f x +
        h (graphProjectionN 2 x) • EuclideanSpace.single (Fin.last 2) (1 : ℝ)) -
        A x (gradient q x) := rfl
  rw [hdeq]
  refine ⟨h5h, h5n.trans ?_⟩
  have hA0 := hAS.norm_nonneg
  have hg0 := hgh.norm_nonneg
  have hid : ‖ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hKa := hASn.trans hAK
  have hQb := hgn.trans hqQ
  have hK0 : 0 ≤ K := hA0.trans hKa
  have e1 : ‖ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))‖ *
        nondivC1HolderNorm α A (closure (boundaryHalfBall (1 / 4))) ≤ K :=
    (mul_le_mul hid hKa hA0 zero_le_one).trans_eq (one_mul K)
  have e2 := mul_le_mul e1 hQb hg0 hK0
  have e3 : 3 * ‖ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))‖ *
        nondivC1HolderNorm α A (closure (boundaryHalfBall (1 / 4))) *
        nondivC1HolderNorm α (gradient q) (closure (boundaryHalfBall (1 / 4))) ≤
      3 * K * Q := by
    nlinarith
  linarith [h2n.trans hhK]

end LiquidDrop
