module

public import NoCompromise.Elliptic.NeumannChartC1Smooth
public import NoCompromise.Elliptic.BoundaryNeumannInhomC1Conormal

@[expose] public section

/-!
# Bounds for smooth Neumann data in normal coordinates

The data predicate below records exactly the coefficient and datum hypotheses
of `boundary_neumann_c1_holder_conormal`. The constants are obtained on compact
subsets of the regular chart; the lower bound for the normal coefficient holds
on the open base ball of radius `3 / 2`.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient

namespace LiquidDrop

/-- The inward-coordinate datum is minus the outward flux times surface area. -/
def neumannChartC1BoundaryDatum (c : C1BoundaryChart) (a : EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (h₀ : AmbientSpace → ℝ) (t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  -(h₀ (neumannLocalizeMap c a ρ (graphBaseEmbedding t)) * ρ ^ 2 *
    Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2))

/-- The forcing density includes the absolute volume Jacobian. -/
def neumannChartC1Forcing (Θ : AmbientSpace → AmbientSpace)
    (f₀ : AmbientSpace → ℝ) (y : AmbientSpace) : ℝ :=
  f₀ (Θ y) * |(fderiv ℝ Θ y).det|

theorem smooth_neumannChartC1BoundaryDatum (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    {h₀ : AmbientSpace → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h₀) :
    ContDiff ℝ (⊤ : ℕ∞) (neumannChartC1BoundaryDatum c a ρ h₀) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (gradient c.height) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp
      (hψ.fderiv_right (by simp))
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun t => Real.sqrt (1 + ‖gradient c.height (a + ρ • t)‖ ^ 2)) :=
    (contDiff_const.add
      ((hg.comp (contDiff_const.add (contDiff_id.const_smul ρ))).norm_sq ℝ)).sqrt
        (fun t => ne_of_gt (by positivity))
  exact (((hh.comp (smooth_neumannLocalizeMap c hψ a ρ)).comp
    graphBaseEmbedding.contDiff).mul contDiff_const |>.mul hs).neg

theorem smoothOn_neumannChartC1Forcing
    {Θ : AmbientSpace → AmbientSpace} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ)
    {f₀ : AmbientSpace → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f₀)
    {U : Set AmbientSpace} (hreg : ∀ y ∈ U, (fderiv ℝ Θ y).IsInvertible) :
    ContDiffOn ℝ (⊤ : ℕ∞) (neumannChartC1Forcing Θ f₀) U := by
  intro y hy
  exact ((hf.comp hΘ).contDiffAt.mul
    (contDiffAt_neumannLocalizeJacobian hΘ (hreg y hy))).contDiffWithinAt

/-- Smooth vector-valued data have a common bound and any sub-Lipschitz
Hölder bound on the unit disk, by compactness and the mean value inequality. -/
theorem neumannChartC1_smooth_bounds {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {g : EuclideanSpace ℝ (Fin n) → E}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball 0 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x ∈ closedBall 0 1, ‖g x‖ ≤ K) ∧
      ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
        ‖g x - g y‖ ≤ K * dist x y ^ α := by
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ball 0 2 :=
    closedBall_subset_ball (by norm_num)
  have hD := (hg.fderiv_of_isOpen isOpen_ball (by simp :
    (0 : WithTop ℕ∞) + 1 ≤ ↑(⊤ : ℕ∞))).continuousOn
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

/-- Exactly the data assumptions of the flat C¹ conormal theorem. -/
structure NeumannChartC1Data
    (A : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace)
    (f : AmbientSpace → ℝ) (h : EuclideanSpace ℝ (Fin 2) → ℝ)
    (α lam cap HA K : ℝ) : Prop where
  continuous_coefficient : ContinuousOn A (closure (boundaryHalfBall 1))
  bound_coefficient : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap
  elliptic : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
    lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ
  holder_coefficient : ∀ x ∈ closure (boundaryHalfBall 1),
    ∀ y ∈ closure (boundaryHalfBall 1), ‖A x - A y‖ ≤ HA * dist x y ^ α
  cross_face : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
    ∀ i : Fin 3, i ≠ Fin.last 2 →
      A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
      A x (EuclideanSpace.single (Fin.last 2) 1) i = 0
  normal_neighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
    closedBall 0 1 ⊆ U ∧ ContDiffOn ℝ 1 h U ∧
    ContDiffOn ℝ 1 (boundaryNeumannNormalCoefficient A) U ∧
    ∀ x ∈ U, lam ≤ boundaryNeumannNormalCoefficient A x
  bound_datum : ∀ x ∈ closedBall 0 1, ‖h x‖ ≤ K
  bound_normal : ∀ x ∈ closedBall 0 1, ‖boundaryNeumannNormalCoefficient A x‖ ≤ K
  bound_gradient_datum : ∀ x ∈ closedBall 0 1, ‖gradient h x‖ ≤ K
  bound_gradient_normal : ∀ x ∈ closedBall 0 1,
    ‖gradient (boundaryNeumannNormalCoefficient A) x‖ ≤ K
  holder_gradient_datum : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
    ‖gradient h x - gradient h y‖ ≤ K * dist x y ^ α
  holder_gradient_normal : ∀ x ∈ closedBall 0 1, ∀ y ∈ closedBall 0 1,
    ‖gradient (boundaryNeumannNormalCoefficient A) x -
      gradient (boundaryNeumannNormalCoefficient A) y‖ ≤ K * dist x y ^ α
  continuous_forcing : ContinuousOn f (closure (boundaryHalfBall 1))
  bound_forcing : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ K
  holder_forcing : ∀ x ∈ closure (boundaryHalfBall 1),
    ∀ y ∈ closure (boundaryHalfBall 1), ‖f x - f y‖ ≤ K * dist x y ^ α

theorem neumannChartC1_exists_data (c : C1BoundaryChart)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) c.height) (a : EuclideanSpace ℝ (Fin 2))
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
  have hΘ := smooth_neumannLocalizeMap c hψ a ρ
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A (ball 0 2) :=
    contDiffOn_neumannLocalizeCoefficient hΘ hreg
  have hfs : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 2) :=
    smoothOn_neumannChartC1Forcing hΘ hf hreg
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h := smooth_neumannChartC1BoundaryDatum c hψ a ρ hh
  have hbase {r : ℝ} {t : EuclideanSpace ℝ (Fin 2)} (ht : t ∈ ball 0 r) :
      graphBaseEmbedding t ∈ ball 0 r := by
    simpa only [mem_ball, dist_zero_right, norm_graphBaseEmbedding] using ht
  have hbs : ContDiffOn ℝ (⊤ : ℕ∞) (boundaryNeumannNormalCoefficient A) (ball 0 2) := by
    have he := hA.comp graphBaseEmbedding.contDiff.contDiffOn (fun _ ht => hbase ht)
    exact (he.clm_apply contDiffOn_const).inner ℝ contDiffOn_const
  have hgrad (g : EuclideanSpace ℝ (Fin 2) → ℝ)
      (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball 0 2)) :
      ContDiffOn ℝ (⊤ : ℕ∞) (gradient g) (ball 0 2) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.contDiff.comp_contDiffOn
      (hg.fderiv_of_isOpen isOpen_ball (by simp))
  obtain ⟨lam, hlam, cap, hcap, hell⟩ := neumannLocalizeCoefficient_compact_bounds hΘ
    (isCompact_closedBall (0 : AmbientSpace) (3 / 2 : ℝ))
    (fun y hy => hreg y (closedBall_subset_ball (by norm_num) hy))
  obtain ⟨HA, hHA, -, hHAh⟩ := neumannChartC1_smooth_bounds hα.le hα1.le hA
  obtain ⟨Kf, hKf, hbf, hhf⟩ := neumannChartC1_smooth_bounds hα.le hα1.le hfs
  obtain ⟨Kh, hKh, hbh, -⟩ := neumannChartC1_smooth_bounds hα.le hα1.le hhs.contDiffOn
  obtain ⟨Kb, hKb, hbb, -⟩ := neumannChartC1_smooth_bounds hα.le hα1.le hbs
  obtain ⟨KDh, hKDh, hbDh, hhDh⟩ := neumannChartC1_smooth_bounds hα.le hα1.le
    (hgrad h hhs.contDiffOn)
  obtain ⟨KDb, hKDb, hbDb, hhDb⟩ := neumannChartC1_smooth_bounds hα.le hα1.le
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
    fun x _ hx i hi => neumannLocalizeCoefficient_cross_face c hψ a hρ hx hi,
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
