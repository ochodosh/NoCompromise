import NoCompromise.Elliptic.NeumannChartC3Geometry
import NoCompromise.Elliptic.NeumannChartC1Data

/-!
# Hölder data bounds from C³ chart heights
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient NNReal

namespace LiquidDrop

/-- The surface density uses one derivative of the height. -/
theorem contDiff_neumannChartC1BoundaryDatum_of_contDiff (c : C1BoundaryChart)
    {r : ℕ∞} (hψ : ContDiff ℝ (r + 1) c.height) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    {h₀ : AmbientSpace → ℝ} (hh : ContDiff ℝ r h₀) :
    ContDiff ℝ r (neumannChartC1BoundaryDatum c a ρ h₀) := by
  have hg : ContDiff ℝ r (gradient c.height) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp
      (hψ.fderiv_right le_rfl)
  have hs : ContDiff ℝ r
      (fun t => Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) :=
    (contDiff_const.add
      ((hg.comp (contDiff_const.add (contDiff_id.const_smul ρ))).norm_sq ℝ)).sqrt
        (fun t => ne_of_gt (by positivity))
  exact (((hh.comp (contDiff_neumannLocalizeMap_of_contDiff c hψ a ρ)).comp
    graphBaseEmbedding.contDiff).mul contDiff_const |>.mul hs).neg

/-- The volume density uses one derivative of the coordinate map. -/
theorem contDiffOn_neumannChartC1Forcing_of_contDiff
    {Θ : AmbientSpace → AmbientSpace} {r : ℕ∞} (hΘ : ContDiff ℝ (r + 1) Θ)
    {f₀ : AmbientSpace → ℝ} (hf : ContDiff ℝ r f₀)
    {U : Set AmbientSpace} (hreg : ∀ y ∈ U, (fderiv ℝ Θ y).IsInvertible) :
    ContDiffOn ℝ r (neumannChartC1Forcing Θ f₀) U := by
  intro y hy
  exact ((hf.comp (hΘ.of_le (le_add_of_nonneg_right zero_le_one))).contDiffAt.mul
    (contDiffAt_neumannLocalizeJacobian_of_contDiff hΘ (hreg y hy))).contDiffWithinAt

/-- C¹ data on the larger ball have bounds and α-Hölder bounds on the unit ball. -/
theorem neumannChartC3_c1_bounds {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {g : EuclideanSpace ℝ (Fin n) → E}
    (hg : ContDiffOn ℝ 1 g (ball 0 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ closedBall 0 1, ‖g x‖ ≤ K) ∧
      ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
        ‖g x - g y‖ ≤ K * dist x y ^ α := by
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ball 0 2 :=
    closedBall_subset_ball (by norm_num)
  have hD := (hg.fderiv_of_isOpen isOpen_ball (by simp :
    (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  have hc := isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨B, hB, hb⟩ :=
    (hc.image_of_continuousOn (hg.continuousOn.mono hsub)).isBounded.exists_pos_norm_le
  obtain ⟨L, hL, hl⟩ :=
    (hc.image_of_continuousOn (hD.mono hsub)).isBounded.exists_pos_norm_le
  refine ⟨B + 2 * L, by positivity, fun x hx =>
    (hb _ (mem_image_of_mem _ hx)).trans (by linarith), ?_⟩
  intro x hx y hy
  have hlip : ‖g x - g y‖ ≤ L * dist x y :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => (hg.contDiffAt (isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp))
        (fun z hz => hl _ (mem_image_of_mem _ hz)) hy hx
  calc
    _ ≤ L * dist x y := hlip
    _ ≤ L * (2 * dist x y ^ α) := mul_le_mul_of_nonneg_left
      (boundary_neumann_dist_le_two_rpow hα hα1 dist_nonneg
        (boundary_neumann_disk_dist hx hy)) hL.le
    _ ≤ (B + 2 * L) * dist x y ^ α := by
      nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α]

/-- C³ height supplies all hypotheses of the flat C¹ conormal theorem.
The normal coefficient is constant on the face, so its gradient has every
Hölder exponent. The remaining bounds follow from C¹ regularity on a larger ball. -/
theorem neumannChartC3_exists_data (c : C1BoundaryChart)
    (hψ : ContDiff ℝ 3 c.height) (a : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hreg : ∀ y ∈ ball 0 2, (fderiv ℝ (neumannLocalizeMap c a ρ) y).IsInvertible)
    {f₀ h₀ : AmbientSpace → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f₀)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h₀) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ lam cap HA K : ℝ, 0 < lam ∧ 0 ≤ cap ∧ 0 ≤ HA ∧ 0 ≤ K ∧
      NeumannChartC1Data (neumannLocalizeCoefficient (neumannLocalizeMap c a ρ))
        (neumannChartC1Forcing (neumannLocalizeMap c a ρ) f₀)
        (neumannChartC1BoundaryDatum c a ρ h₀) α lam cap HA K := by
  let Θ := neumannLocalizeMap c a ρ
  let A := neumannLocalizeCoefficient Θ
  let f := neumannChartC1Forcing Θ f₀
  let h := neumannChartC1BoundaryDatum c a ρ h₀
  have hΘ : ContDiff ℝ 2 Θ := contDiff_neumannLocalizeMap_of_contDiff c hψ a ρ
  have hA : ContDiffOn ℝ 1 A (ball 0 2) :=
    contDiffOn_neumannLocalizeCoefficient_of_contDiff (r := 1) hΘ hreg
  have hfs : ContDiffOn ℝ 1 f (ball 0 2) :=
    contDiffOn_neumannChartC1Forcing_of_contDiff (r := 1) hΘ (hf.of_le (by simp)) hreg
  have hhs : ContDiff ℝ 2 h :=
    contDiff_neumannChartC1BoundaryDatum_of_contDiff c (r := 2) hψ a ρ (hh.of_le (by simp))
  have hbase {r : ℝ} {t : EuclideanSpace ℝ (Fin 2)} (ht : t ∈ ball 0 r) :
      graphBaseEmbedding t ∈ ball 0 r := by
    simpa only [mem_ball, dist_zero_right, norm_graphBaseEmbedding] using ht
  have hbs : ContDiffOn ℝ 2 (boundaryNeumannNormalCoefficient A) (ball 0 2) := by
    change ContDiffOn ℝ 2 (boundaryNeumannNormalCoefficient
      (neumannLocalizeCoefficient (neumannLocalizeMap c a ρ))) (ball 0 2)
    rw [neumannChartC3_normal_coefficient c (hψ.of_le (by norm_num)) a hρ]
    exact contDiffOn_const
  have hgrad (g : EuclideanSpace ℝ (Fin 2) → ℝ)
      (hg : ContDiffOn ℝ 2 g (ball 0 2)) :
      ContDiffOn ℝ 1 (gradient g) (ball 0 2) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen isOpen_ball (by norm_num))
  obtain ⟨lam, hlam, cap, hcap, hell⟩ :=
    neumannLocalizeCoefficient_compact_bounds_c1 (hΘ.of_le (by norm_num))
    (isCompact_closedBall (0 : AmbientSpace) (3 / 2 : ℝ))
    (fun y hy => hreg y (closedBall_subset_ball (by norm_num) hy))
  obtain ⟨HA, hHA, -, hHAh⟩ := neumannChartC3_c1_bounds hα.le hα1.le hA
  obtain ⟨Kf, hKf, hbf, hhf⟩ := neumannChartC3_c1_bounds hα.le hα1.le hfs
  obtain ⟨Kh, hKh, hbh, -⟩ := neumannChartC3_c1_bounds hα.le hα1.le
    (hhs.of_le (by norm_num)).contDiffOn
  obtain ⟨Kb, hKb, hbb, -⟩ := neumannChartC3_c1_bounds hα.le hα1.le (hbs.of_le (by norm_num))
  obtain ⟨KDh, hKDh, hbDh, hhDh⟩ := neumannChartC3_c1_bounds hα.le hα1.le
    (hgrad h hhs.contDiffOn)
  obtain ⟨KDb, hKDb, hbDb, hhDb⟩ := neumannChartC3_c1_bounds hα.le hα1.le
    (hgrad _ hbs)
  let K := Kf + Kh + Kb + KDh + KDb
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKf' : Kf ≤ K := by dsimp [K]; linarith
  have hKh' : Kh ≤ K := by dsimp [K]; linarith
  have hKb' : Kb ≤ K := by dsimp [K]; linarith
  have hKDh' : KDh ≤ K := by dsimp [K]; linarith
  have hKDb' : KDb ≤ K := by dsimp [K]; linarith
  have hclosed : closure (boundaryHalfBall 1) ⊆ closedBall (0 : AmbientSpace) 1 :=
    fun x hx => by simpa only [mem_closedBall, dist_zero_right] using
      boundary_neumann_closed_norm_le hx
  have hlarge : closedBall (0 : AmbientSpace) 1 ⊆ closedBall 0 (3 / 2 : ℝ) :=
    closedBall_subset_closedBall (by norm_num)
  have htwo : closedBall (0 : AmbientSpace) 1 ⊆ ball 0 2 :=
    closedBall_subset_ball (by norm_num)
  refine ⟨lam, cap, HA, K, hlam, hcap.le, hHA, hK, ?_⟩
  refine ⟨hA.continuousOn.mono (hclosed.trans htwo),
    fun x hx => (hell x (hlarge (hclosed hx))).1,
    fun x hx => (hell x (hlarge (hclosed hx))).2,
    fun x hx y hy => hHAh x (hclosed hx) y (hclosed hy),
    fun x _ hx i hi =>
      neumannLocalizeCoefficient_cross_face_c2 c (hψ.of_le (by norm_num)) a hρ hx hi,
    ?_, fun x hx => (hbh x hx).trans hKh', fun x hx => (hbb x hx).trans hKb',
    fun x hx => (hbDh x hx).trans hKDh', fun x hx => (hbDb x hx).trans hKDb',
    ?_, ?_, hfs.continuousOn.mono (hclosed.trans htwo),
    fun x hx => (hbf x (hclosed hx)).trans hKf', ?_⟩
  · refine ⟨ball 0 (3 / 2 : ℝ), isOpen_ball, closedBall_subset_ball (by norm_num),
      (hhs.of_le (by simp)).contDiffOn,
      (hbs.of_le (by simp)).mono (ball_subset_ball (by norm_num)), ?_⟩
    intro t ht
    exact boundaryNeumannNormalCoefficient_ge (hell _ (ball_subset_closedBall (hbase ht))).2
  · intro x hx y hy
    exact (hhDh x hx y hy).trans
      (mul_le_mul_of_nonneg_right hKDh' (Real.rpow_nonneg dist_nonneg _))
  · intro x hx y hy
    exact (hhDb x hx y hy).trans
      (mul_le_mul_of_nonneg_right hKDb' (Real.rpow_nonneg dist_nonneg _))
  · intro x hx y hy
    exact (hhf x (hclosed hx) y (hclosed hy)).trans
      (mul_le_mul_of_nonneg_right hKf' (Real.rpow_nonneg dist_nonneg _))

end LiquidDrop
