module

public import NoCompromise.Elliptic.BoundaryNeumannInhom
public import NoCompromise.Sobolev.H1Algebra

@[expose] public section

/-!
# Quantitative estimates for the conormal lift

All estimates below concern the ordinary gradient, including at points of the
closed base disk: differentiability is supplied on an open neighbourhood.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_norm_gradient {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ‖gradient g x‖ = ‖fderiv ℝ g x‖ := by
  exact (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map _

lemma boundary_neumann_dist_le_two_rpow {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {d : ℝ} (hd : 0 ≤ d) (hd2 : d ≤ 2) : d ≤ 2 * d ^ a := by
  by_cases hd1 : d ≤ 1
  · have := Real.self_le_rpow_of_le_one hd hd1 ha1
    linarith [Real.rpow_nonneg hd a]
  · have := Real.one_le_rpow (le_of_not_ge hd1) ha
    linarith

lemma boundary_neumann_disk_dist {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 1) : dist x y ≤ 2 := by
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  have hy' : ‖y‖ ≤ 1 := by simpa using hy
  simpa only [dist_eq_norm] using (norm_sub_le x y).trans (by linarith)

lemma boundary_neumann_gradient_bound_lipschitz {n : ℕ} {K : ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ x ∈ closedBall 0 1, DifferentiableAt ℝ g x)
    (hb : ∀ x ∈ closedBall 0 1, ‖gradient g x‖ ≤ K)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closedBall 0 1)
    (hy : y ∈ closedBall 0 1) : ‖g x - g y‖ ≤ K * dist x y := by
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).norm_image_sub_le_of_norm_fderiv_le
    hg (fun z hz => by simpa only [boundary_neumann_norm_gradient] using hb z hz) hy hx

lemma boundary_neumann_gradient_bound_holder {n : ℕ} {a K : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hK : 0 ≤ K)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ∀ x ∈ closedBall 0 1, DifferentiableAt ℝ g x)
    (hb : ∀ x ∈ closedBall 0 1, ‖gradient g x‖ ≤ K)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closedBall 0 1)
    (hy : y ∈ closedBall 0 1) : ‖g x - g y‖ ≤ (2 * K) * dist x y ^ a := by
  exact (boundary_neumann_gradient_bound_lipschitz hg hb hx hy).trans
    ((mul_le_mul_of_nonneg_left
      (boundary_neumann_dist_le_two_rpow ha ha1 dist_nonneg
        (boundary_neumann_disk_dist hx hy)) hK).trans_eq (by ring))

lemma boundary_neumann_smul_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t B H Bv Hv r : ℝ} {v w : E}
    (hB : 0 ≤ B)
    (hs : ‖s‖ ≤ B) (hw : ‖w‖ ≤ Bv)
    (hst : ‖s - t‖ ≤ H * r) (hvw : ‖v - w‖ ≤ Hv * r) :
    ‖s • v - t • w‖ ≤ (B * Hv + H * Bv) * r := by
  have he : s • v - t • w = s • (v - w) + (s - t) • w := by
    simp only [smul_sub, sub_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖s‖ * ‖v - w‖ + ‖s - t‖ * ‖w‖ := by
      simpa only [norm_smul] using norm_add_le (s • (v - w)) ((s - t) • w)
    _ ≤ B * (Hv * r) + (H * r) * Bv := by
      exact add_le_add (mul_le_mul hs hvw (norm_nonneg _) hB)
        (mul_le_mul hst hw (norm_nonneg _) (le_trans (norm_nonneg _) hst))
    _ = _ := by ring

lemma boundary_neumann_inv_bound {lam s : ℝ} (hlam : 0 < lam) (hs : lam ≤ s) :
    ‖s⁻¹‖ ≤ lam⁻¹ := by
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (hlam.le.trans hs))]
  exact inv_anti₀ hlam hs

lemma boundary_neumann_inv_difference_bound {lam s t H r : ℝ}
    (hlam : 0 < lam) (hs : lam ≤ s) (ht : lam ≤ t)
    (hst : ‖s - t‖ ≤ H * r) :
    ‖s⁻¹ - t⁻¹‖ ≤ (lam⁻¹ ^ 2 * H) * r := by
  have he : s⁻¹ - t⁻¹ = s⁻¹ * (t - s) * t⁻¹ := by
    field_simp [(hlam.trans_le hs).ne', (hlam.trans_le ht).ne']
  rw [he, norm_mul, norm_mul, norm_sub_rev t s]
  calc
    _ ≤ (lam⁻¹ * (H * r)) * lam⁻¹ := by
      exact mul_le_mul
        (mul_le_mul (boundary_neumann_inv_bound hlam hs) hst (norm_nonneg _)
          (inv_nonneg.mpr hlam.le))
        (boundary_neumann_inv_bound hlam ht) (norm_nonneg _)
          (mul_nonneg (inv_nonneg.mpr hlam.le) ((norm_nonneg _).trans hst))
    _ = _ := by ring

lemma boundary_neumann_quotient_gradient {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} (hh : DifferentiableAt ℝ h x)
    (hb : DifferentiableAt ℝ b x) (hb0 : b x ≠ 0) :
    gradient (fun y => h y / b y) x =
      (b x ^ 2)⁻¹ • (b x • gradient h x - h x • gradient b x) := by
  have hi := (hasDerivAt_inv hb0).comp_hasFDerivAt x hb.hasFDerivAt
  have hp := hh.hasFDerivAt.mul hi
  ext i
  rw [gradient_apply_eq_fderiv_single]
  simp only [div_eq_mul_inv]
  have he := hp.fderiv
  simp only [Pi.mul_def, Function.comp_def] at he
  rw [he]
  simp only [add_apply, smul_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
    ← gradient_apply_eq_fderiv_single]
  field_simp [hb0]
  ring

/-- The base quotient is C¹ on the given neighbourhood and has a uniform value bound. -/
lemma boundaryNeumannQuotient_contDiffOn_bound {lam K : ℝ}
    (hlam : 0 < lam) (hK : 0 ≤ K)
    {h b : EuclideanSpace ℝ (Fin 2) → ℝ} {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hsub : closedBall 0 1 ⊆ U) (hh : ContDiffOn ℝ 1 h U) (hb : ContDiffOn ℝ 1 b U)
    (hpos : ∀ x ∈ U, lam ≤ b x) (hbh : ∀ x ∈ closedBall 0 1, ‖h x‖ ≤ K) :
    ContDiffOn ℝ 1 (fun y => h y / b y) U ∧
    (∀ x ∈ closedBall 0 1, ‖h x / b x‖ ≤ K * lam⁻¹) := by
  refine ⟨hh.div hb (fun x hx => (hlam.trans_le (hpos x hx)).ne'), ?_⟩
  intro x hx
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul (hbh x hx) (boundary_neumann_inv_bound hlam (hpos x (hsub hx)))
    (norm_nonneg _) hK

lemma boundaryNeumannLift_gradient {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hk : DifferentiableAt ℝ (fun y => h y / b y) (graphProjectionN 2 x)) :
    gradient (boundaryNeumannLift h b) x =
      x (Fin.last 2) • graphBaseEmbedding
        (gradient (fun y => h y / b y) (graphProjectionN 2 x)) +
      (h (graphProjectionN 2 x) / b (graphProjectionN 2 x)) •
        EuclideanSpace.single (Fin.last 2) 1 := by
  have hd := hk.hasFDerivAt.comp x (graphProjectionN 2).hasFDerivAt
  have hp := (EuclideanSpace.proj (Fin.last 2)).hasFDerivAt.mul hd
  ext i
  rw [gradient_apply_eq_fderiv_single]
  change fderiv ℝ (fun y => y (Fin.last 2) *
    (h (graphProjectionN 2 y) / b (graphProjectionN 2 y))) x
      (EuclideanSpace.single i 1) = _
  have he := hp.fderiv
  simp only [Pi.mul_def, Function.comp_def, EuclideanSpace.coe_proj] at he
  rw [he]
  fin_cases i <;>
    simp [graphProjectionN, graphBaseEmbedding, ← gradient_apply_eq_fderiv_single]

/-- A uniform bound for the gradient of the base quotient. -/
def boundaryNeumannQuotientGradientBound (lam K : ℝ) : ℝ :=
  (lam ^ 2)⁻¹ * (2 * K ^ 2)

/-- A uniform Hölder constant for the gradient of the base quotient. -/
def boundaryNeumannQuotientGradientHolder (lam K : ℝ) : ℝ :=
  (lam ^ 2)⁻¹ * (6 * K ^ 2) +
    ((lam ^ 2)⁻¹ ^ 2 * (4 * K ^ 2)) * (2 * K ^ 2)

lemma boundary_neumann_quotient_gradient_bound {lam K : ℝ}
    (hlam : 0 < lam) (hK : 0 ≤ K)
    {h b : EuclideanSpace ℝ (Fin 2) → ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hh : DifferentiableAt ℝ h x) (hb : DifferentiableAt ℝ b x)
    (hpos : lam ≤ b x) (hbh : ‖h x‖ ≤ K) (hbb : ‖b x‖ ≤ K)
    (hDh : ‖gradient h x‖ ≤ K) (hDb : ‖gradient b x‖ ≤ K) :
    ‖gradient (fun y => h y / b y) x‖ ≤ boundaryNeumannQuotientGradientBound lam K := by
  have hn : ‖b x • gradient h x - h x • gradient b x‖ ≤ 2 * K ^ 2 := by
    calc
      _ ≤ ‖b x‖ * ‖gradient h x‖ + ‖h x‖ * ‖gradient b x‖ := by
        simpa only [norm_smul] using norm_sub_le (b x • gradient h x) (h x • gradient b x)
      _ ≤ K * K + K * K :=
        add_le_add (mul_le_mul hbb hDh (norm_nonneg _) hK)
          (mul_le_mul hbh hDb (norm_nonneg _) hK)
      _ = _ := by ring
  rw [boundary_neumann_quotient_gradient hh hb (hlam.trans_le hpos).ne', norm_smul]
  exact mul_le_mul (boundary_neumann_inv_bound (sq_pos_of_pos hlam)
    (sq_le_sq₀ hlam.le (hlam.le.trans hpos) |>.mpr hpos)) hn (norm_nonneg _) (by positivity)

lemma boundary_neumann_quotient_gradient_holder {a lam K : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hlam : 0 < lam) (hK : 0 ≤ K)
    {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hdh : ∀ x ∈ closedBall 0 1, DifferentiableAt ℝ h x)
    (hdb : ∀ x ∈ closedBall 0 1, DifferentiableAt ℝ b x)
    (hpos : ∀ x ∈ closedBall 0 1, lam ≤ b x)
    (hbh : ∀ x ∈ closedBall 0 1, ‖h x‖ ≤ K)
    (hbb : ∀ x ∈ closedBall 0 1, ‖b x‖ ≤ K)
    (hDh : ∀ x ∈ closedBall 0 1, ‖gradient h x‖ ≤ K)
    (hDb : ∀ x ∈ closedBall 0 1, ‖gradient b x‖ ≤ K)
    (hhDh : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖gradient h x - gradient h y‖ ≤ K * dist x y ^ a)
    (hhDb : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖gradient b x - gradient b y‖ ≤ K * dist x y ^ a)
    {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 1) :
    ‖gradient (fun y => h y / b y) x - gradient (fun y => h y / b y) y‖ ≤
      boundaryNeumannQuotientGradientHolder lam K * dist x y ^ a := by
  have hh := boundary_neumann_gradient_bound_holder ha ha1 hK hdh hDh hx hy
  have hb := boundary_neumann_gradient_bound_holder ha ha1 hK hdb hDb hx hy
  have hnum : ‖(b x • gradient h x - h x • gradient b x) -
      (b y • gradient h y - h y • gradient b y)‖ ≤ (6 * K ^ 2) * dist x y ^ a := by
    have h1 := boundary_neumann_smul_difference_bound hK (hbb x hx) (hDh y hy)
      hb (hhDh x hx y hy)
    have h2 := boundary_neumann_smul_difference_bound hK (hbh x hx) (hDb y hy)
      hh (hhDb x hx y hy)
    have he : (b x • gradient h x - h x • gradient b x) -
        (b y • gradient h y - h y • gradient b y) =
        (b x • gradient h x - b y • gradient h y) -
        (h x • gradient b x - h y • gradient b y) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hden : ‖b x ^ 2 - b y ^ 2‖ ≤ (4 * K ^ 2) * dist x y ^ a := by
    have he := boundary_neumann_smul_difference_bound hK (hbb x hx) (hbb y hy) hb hb
    simp only [smul_eq_mul] at he
    simpa only [sq] using he.trans_eq
      (show (K * (2 * K) + 2 * K * K) * dist x y ^ a = (4 * K ^ 2) * dist x y ^ a by ring)
  have hnb : ‖b y • gradient h y - h y • gradient b y‖ ≤ 2 * K ^ 2 := by
    calc
      _ ≤ ‖b y‖ * ‖gradient h y‖ + ‖h y‖ * ‖gradient b y‖ := by
        simpa only [norm_smul] using norm_sub_le (b y • gradient h y) (h y • gradient b y)
      _ ≤ K * K + K * K :=
        add_le_add (mul_le_mul (hbb y hy) (hDh y hy) (norm_nonneg _) hK)
          (mul_le_mul (hbh y hy) (hDb y hy) (norm_nonneg _) hK)
      _ = _ := by ring
  have hsq {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ closedBall 0 1) :
      lam ^ 2 ≤ b z ^ 2 := sq_le_sq₀ hlam.le (hlam.le.trans (hpos z hz)) |>.mpr (hpos z hz)
  rw [boundary_neumann_quotient_gradient (hdh x hx) (hdb x hx)
      (hlam.trans_le (hpos x hx)).ne',
    boundary_neumann_quotient_gradient (hdh y hy) (hdb y hy)
      (hlam.trans_le (hpos y hy)).ne']
  exact boundary_neumann_smul_difference_bound (by positivity)
    (boundary_neumann_inv_bound (sq_pos_of_pos hlam) (hsq hx)) hnb
    (boundary_neumann_inv_difference_bound (sq_pos_of_pos hlam) (hsq hx) (hsq hy) hden) hnum

/-- C¹ on a neighbourhood of the compact closure supplies the genuine H¹ gradient. -/
lemma boundary_neumann_hasH1GradientOn_of_contDiffOn
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} {V : Set (EuclideanSpace ℝ (Fin 3))}
    (hV : IsOpen V) (hsub : closure (boundaryHalfBall 1) ⊆ V)
    (hg : ContDiffOn ℝ 1 g V) :
    HasH1GradientOn g (gradient g) (boundaryHalfBall 1) := by
  have hc := hg.continuousOn.mono hsub
  have hcg := (continuousOn_gradient_of_contDiffOn hV hg).mono hsub
  obtain ⟨B, hB⟩ := boundary_neumann_isCompact_closure.exists_bound_of_continuousOn hc
  obtain ⟨D, hD⟩ := boundary_neumann_isCompact_closure.exists_bound_of_continuousOn hcg
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top 1⟩
  refine ⟨hasWeakGradientOn_of_contDiffOn (isOpen_boundaryHalfBall 1)
    (hg.mono (subset_closure.trans hsub)), ?_, ?_⟩
  · apply MemLp.of_bound
      ((hc.mono subset_closure).aestronglyMeasurable (isOpen_boundaryHalfBall 1).measurableSet) B
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
    exact hB x (subset_closure hx)
  · apply MemLp.of_bound
      ((hcg.mono subset_closure).aestronglyMeasurable (isOpen_boundaryHalfBall 1).measurableSet) D
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
    exact hD x (subset_closure hx)

lemma boundary_neumann_projection_closedBall {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ closedBall 0 1) : graphProjectionN 2 x ∈ closedBall 0 1 := by
  simp only [mem_closedBall, dist_zero_right] at hx ⊢
  exact (boundary_neumann_norm_projection_le x).trans hx

lemma boundary_neumann_c1_projection_dist (x y : EuclideanSpace ℝ (Fin 3)) :
    dist (graphProjectionN 2 x) (graphProjectionN 2 y) ≤ dist x y := by
  simpa only [dist_eq_norm, map_sub] using boundary_neumann_norm_projection_le (x - y)

lemma boundaryNeumannLift_gradient_bound_of_quotient {Bk Dk : ℝ} (_hDk : 0 ≤ Dk)
    {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hk : ∀ y ∈ closedBall 0 1, DifferentiableAt ℝ (fun y => h y / b y) y)
    (hBk : ∀ y ∈ closedBall 0 1, ‖h y / b y‖ ≤ Bk)
    (hD : ∀ y ∈ closedBall 0 1, ‖gradient (fun y => h y / b y) y‖ ≤ Dk)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closedBall 0 1) :
    ‖gradient (boundaryNeumannLift h b) x‖ ≤ Dk + Bk := by
  have hp := boundary_neumann_projection_closedBall hx
  have hn : ‖x (Fin.last 2)‖ ≤ 1 :=
    (PiLp.norm_apply_le x _).trans (by simpa using hx)
  rw [boundaryNeumannLift_gradient (hk _ hp)]
  calc
    _ ≤ ‖x (Fin.last 2)‖ * ‖gradient (fun y => h y / b y) (graphProjectionN 2 x)‖ +
        ‖h (graphProjectionN 2 x) / b (graphProjectionN 2 x)‖ := by
      simpa only [norm_smul, norm_graphBaseEmbedding, PiLp.norm_single, norm_one, mul_one]
        using norm_add_le
          (x (Fin.last 2) • graphBaseEmbedding
            (gradient (fun y => h y / b y) (graphProjectionN 2 x)))
          ((h (graphProjectionN 2 x) / b (graphProjectionN 2 x)) •
            EuclideanSpace.single (Fin.last 2) (1 : ℝ))
    _ ≤ _ := by
      simpa only [one_mul] using add_le_add
        (mul_le_mul hn (hD _ hp) (norm_nonneg _) zero_le_one) (hBk _ hp)

lemma boundaryNeumannLift_gradient_holder_of_quotient {a Dk Hk : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hDk : 0 ≤ Dk) (hHk : 0 ≤ Hk)
    {h b : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hk : ∀ y ∈ closedBall 0 1, DifferentiableAt ℝ (fun y => h y / b y) y)
    (hD : ∀ y ∈ closedBall 0 1, ‖gradient (fun y => h y / b y) y‖ ≤ Dk)
    (hH : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖gradient (fun y => h y / b y) x - gradient (fun y => h y / b y) y‖ ≤
        Hk * dist x y ^ a)
    {x y : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 1) :
    ‖gradient (boundaryNeumannLift h b) x - gradient (boundaryNeumannLift h b) y‖ ≤
      (Hk + 4 * Dk) * dist x y ^ a := by
  have hpx := boundary_neumann_projection_closedBall hx
  have hpy := boundary_neumann_projection_closedBall hy
  have hp := Real.rpow_le_rpow dist_nonneg (boundary_neumann_c1_projection_dist x y) ha
  have hd : ‖x (Fin.last 2) - y (Fin.last 2)‖ ≤ 2 * dist x y ^ a := by
    exact (show ‖x (Fin.last 2) - y (Fin.last 2)‖ ≤ dist x y by
      simpa only [dist_eq_norm, PiLp.sub_apply] using PiLp.norm_apply_le (x - y) (Fin.last 2)).trans
        (boundary_neumann_dist_le_two_rpow ha ha1 dist_nonneg
          (boundary_neumann_disk_dist hx hy))
  have hgrad : ‖graphBaseEmbedding (gradient (fun y => h y / b y) (graphProjectionN 2 x)) -
      graphBaseEmbedding (gradient (fun y => h y / b y) (graphProjectionN 2 y))‖ ≤
        Hk * dist x y ^ a := by
    rw [← map_sub, norm_graphBaseEmbedding]
    exact (hH _ hpx _ hpy).trans (mul_le_mul_of_nonneg_left hp hHk)
  have h1 := boundary_neumann_smul_difference_bound zero_le_one
    ((PiLp.norm_apply_le x (Fin.last 2)).trans (by simpa using hx) : ‖x (Fin.last 2)‖ ≤ 1)
    (by simpa only [norm_graphBaseEmbedding] using hD _ hpy) hd hgrad
  have h2 : ‖((h (graphProjectionN 2 x) / b (graphProjectionN 2 x)) -
      (h (graphProjectionN 2 y) / b (graphProjectionN 2 y))) •
        EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖ ≤ (2 * Dk) * dist x y ^ a := by
    rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
    exact (boundary_neumann_gradient_bound_holder ha ha1 hDk hk hD hpx hpy).trans
      (mul_le_mul_of_nonneg_left hp (by positivity))
  rw [boundaryNeumannLift_gradient (hk _ hpx), boundaryNeumannLift_gradient (hk _ hpy)]
  have he : x (Fin.last 2) • graphBaseEmbedding
        (gradient (fun y => h y / b y) (graphProjectionN 2 x)) +
      (h (graphProjectionN 2 x) / b (graphProjectionN 2 x)) • EuclideanSpace.single (Fin.last 2) 1 -
      (y (Fin.last 2) • graphBaseEmbedding
        (gradient (fun y => h y / b y) (graphProjectionN 2 y)) +
      (h (graphProjectionN 2 y) / b (graphProjectionN 2 y)) •
        EuclideanSpace.single (Fin.last 2) (1 : ℝ)) =
      (x (Fin.last 2) • graphBaseEmbedding
        (gradient (fun y => h y / b y) (graphProjectionN 2 x)) -
      y (Fin.last 2) • graphBaseEmbedding
        (gradient (fun y => h y / b y) (graphProjectionN 2 y))) +
      ((h (graphProjectionN 2 x) / b (graphProjectionN 2 x)) -
      (h (graphProjectionN 2 y) / b (graphProjectionN 2 y))) •
        EuclideanSpace.single (Fin.last 2) 1 := by
    rw [sub_smul]
    abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- Uniform gradient bound for the uncut lift on the closed unit ball. -/
def boundaryNeumannLiftGradientBound (lam K : ℝ) : ℝ :=
  boundaryNeumannQuotientGradientBound lam K + K * lam⁻¹

/-- Uniform Hölder constant for the lift gradient on the closed unit ball. -/
def boundaryNeumannLiftGradientHolder (lam K : ℝ) : ℝ :=
  boundaryNeumannQuotientGradientHolder lam K + 4 * boundaryNeumannQuotientGradientBound lam K

/-- The quotient construction supplies the lift estimates and genuine Sobolev gradient.
The estimates hold on the full closed unit ball, hence on both sets used in the
inhomogeneous regularity argument. -/
theorem boundaryNeumannLift_c1_estimates {a lam K : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hlam : 0 < lam) (hK : 0 ≤ K)
    {h b : EuclideanSpace ℝ (Fin 2) → ℝ} {U : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (hsub : closedBall 0 1 ⊆ U)
    (hh : ContDiffOn ℝ 1 h U) (hb : ContDiffOn ℝ 1 b U)
    (hpos : ∀ x ∈ U, lam ≤ b x)
    (hbh : ∀ x ∈ closedBall 0 1, ‖h x‖ ≤ K)
    (hbb : ∀ x ∈ closedBall 0 1, ‖b x‖ ≤ K)
    (hDh : ∀ x ∈ closedBall 0 1, ‖gradient h x‖ ≤ K)
    (hDb : ∀ x ∈ closedBall 0 1, ‖gradient b x‖ ≤ K)
    (hhDh : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖gradient h x - gradient h y‖ ≤ K * dist x y ^ a)
    (hhDb : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖gradient b x - gradient b y‖ ≤ K * dist x y ^ a) :
    ContDiffOn ℝ 1 (boundaryNeumannLift h b) ((graphProjectionN 2) ⁻¹' U) ∧
    HasH1GradientOn (boundaryNeumannLift h b) (gradient (boundaryNeumannLift h b))
      (boundaryHalfBall 1) ∧
    (∀ x ∈ closedBall 0 1,
      ‖gradient (boundaryNeumannLift h b) x‖ ≤ boundaryNeumannLiftGradientBound lam K) ∧
    (∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖gradient (boundaryNeumannLift h b) x - gradient (boundaryNeumannLift h b) y‖ ≤
        boundaryNeumannLiftGradientHolder lam K * dist x y ^ a) ∧
    (∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖h x - h y‖ ≤ (2 * K) * dist x y ^ a) := by
  have hb0 : ∀ x ∈ U, b x ≠ 0 := fun x hx => (hlam.trans_le (hpos x hx)).ne'
  have hdh : ∀ x ∈ closedBall 0 1, DifferentiableAt ℝ h x :=
    fun x hx => (hh.differentiableOn one_ne_zero x (hsub hx)).differentiableAt
      (hU.mem_nhds (hsub hx))
  have hdb : ∀ x ∈ closedBall 0 1, DifferentiableAt ℝ b x :=
    fun x hx => (hb.differentiableOn one_ne_zero x (hsub hx)).differentiableAt
      (hU.mem_nhds (hsub hx))
  obtain ⟨hck, hB⟩ := boundaryNeumannQuotient_contDiffOn_bound hlam hK hsub hh hb hpos hbh
  have hk : ∀ x ∈ closedBall 0 1, DifferentiableAt ℝ (fun y => h y / b y) x :=
    fun x hx => (hck.differentiableOn one_ne_zero x (hsub hx)).differentiableAt
      (hU.mem_nhds (hsub hx))
  have hD : ∀ x ∈ closedBall 0 1, ‖gradient (fun y => h y / b y) x‖ ≤
      boundaryNeumannQuotientGradientBound lam K :=
    fun x hx => boundary_neumann_quotient_gradient_bound hlam hK (hdh x hx) (hdb x hx)
      (hpos x (hsub hx)) (hbh x hx) (hbb x hx) (hDh x hx) (hDb x hx)
  have hH : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
      ‖gradient (fun y => h y / b y) x - gradient (fun y => h y / b y) y‖ ≤
        boundaryNeumannQuotientGradientHolder lam K * dist x y ^ a :=
    fun x hx y hy => boundary_neumann_quotient_gradient_holder ha ha1 hlam hK hdh hdb
      (fun x hx => hpos x (hsub hx)) hbh hbb hDh hDb hhDh hhDb hx hy
  have hq := boundaryNeumannLift_contDiffOn hh hb hb0
  refine ⟨hq, boundary_neumann_hasH1GradientOn_of_contDiffOn
    (hU.preimage (graphProjectionN 2).continuous) ?_ hq, ?_, ?_, ?_⟩
  · intro x hx
    exact hsub (boundary_neumann_projection_closedBall (by
      simpa only [mem_closedBall, dist_zero_right] using boundary_neumann_closed_norm_le hx))
  · exact fun x hx => boundaryNeumannLift_gradient_bound_of_quotient
      (by unfold boundaryNeumannQuotientGradientBound; positivity) hk hB hD hx
  · exact fun x hx y hy => boundaryNeumannLift_gradient_holder_of_quotient ha ha1
      (by unfold boundaryNeumannQuotientGradientBound; positivity)
      (by unfold boundaryNeumannQuotientGradientHolder; positivity) hk hD hH hx hy
  · exact fun x hx y hy => boundary_neumann_gradient_bound_holder ha ha1 hK hdh hDh hx hy

end LiquidDrop
