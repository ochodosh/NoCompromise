module

public import NoCompromise.Elliptic.SobolevChainLocal

@[expose] public section

/-! A continuous weak gradient produces a genuine C¹ representative. Local
mollifications converge through their derivatives; an actual Lebesgue point
fixes their additive constant. No initial continuity of the function is assumed. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_tendstoLocallyUniformlyOn_bump_convolution {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : AEStronglyMeasurable g volume)
    (hc : ContinuousOn g U)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))}
    (hφ : Tendsto (fun j => (φ j).rOut) l (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun j => (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) g l U := by
  apply tendstoLocallyUniformlyOn_iff_filter.mpr
  intro x hx
  rw [hU.nhdsWithin_eq hx]
  have hc' : ContinuousAt g x := hc.continuousAt (hU.mem_nhds hx)
  have hconv : Tendsto (fun p : ι × EuclideanSpace ℝ (Fin n) =>
      ((φ p.1).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) p.2)
      (l ×ˢ 𝓝 x) (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right (hφ.comp tendsto_fst)
      (Eventually.of_forall fun _ => hg)
      (hc'.tendsto.comp tendsto_snd) tendsto_snd
  exact ((hc'.tendsto.comp tendsto_snd).prodMk_nhds hconv).mono_right (nhds_le_uniformity _)

/-- A whole-space weak gradient continuous near a closed ball gives a C¹
representative on the ball, with the actual gradient identified pointwise. -/
theorem campanato_c1_representative_of_global_weak_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasWeakGradientOn u G univ)
    {c : EuclideanSpace ℝ (Fin n)} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hG : ContinuousOn G (ball c R)) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ 1 v (ball c r) ∧ u =ᵐ[volume.restrict (ball c r)] v ∧
        ∀ x ∈ ball c r, gradient v x = G x := by
  classical
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let w (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u
  have hiu := locallyIntegrableOn_univ.mp hu.locallyIntegrable_function
  have hiG := locallyIntegrableOn_univ.mp hu.locallyIntegrable_gradient
  have hw (j) : ContDiff ℝ (⊤ : ℕ∞) (w j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left _ (φ j).contDiff_normed hiu
  have hder (j) : fderiv ℝ (w j) = fun y => toDual ℝ _
      (((φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) y) := by
    funext y
    rw [← toDual_gradient, hu.gradient_convolution (φ j).contDiff_normed
      (φ j).hasCompactSupport_normed]
  have hconv := campanato_tendstoLocallyUniformlyOn_bump_convolution
    isOpen_ball hiG.aestronglyMeasurable hG hφ
  have hunif := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall c r)).mp (hconv.mono (closedBall_subset_ball hrR))
  have hderlim : TendstoUniformlyOn (fun j => fderiv ℝ (w j))
      (fun x => toDual ℝ _ (G x)) atTop (ball c r) := by
    simpa only [Function.comp_def, hder] using
      (toDual ℝ (EuclideanSpace ℝ (Fin n))).isometry.uniformContinuous
        |>.comp_tendstoUniformlyOn (hunif.mono ball_subset_closedBall)
  have hpoint : ∀ᵐ x ∂volume, Tendsto (fun j => w j x) atTop (𝓝 (u x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ
      (Eventually.of_forall fun j => by dsimp [φ]; linarith :
        ∀ᶠ j in atTop, (φ j).rOut ≤ 2 * (φ j).rIn) hiu
  obtain ⟨x₀, hx₀, hlim₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume c hr).ne' (ae_restrict_of_ae hpoint)
  have hex (x) (hx : x ∈ ball c r) : ∃ v : ℝ, Tendsto (fun j => w j x) atTop (𝓝 v) := by
    apply cauchy_map_iff_exists_tendsto.mp
    exact cauchy_map_of_uniformCauchySeqOn_fderiv isOpen_ball
      (convex_ball c r).isPreconnected hderlim.uniformCauchySeqOn
      (fun j y _ => ((hw j).differentiable (by simp) y).hasFDerivAt)
      hx₀ hx hlim₀.cauchy_map
  let v (x : EuclideanSpace ℝ (Fin n)) := if hx : x ∈ ball c r then (hex x hx).choose else 0
  have hlim (x) (hx : x ∈ ball c r) : Tendsto (fun j => w j x) atTop (𝓝 (v x)) := by
    simpa only [v, dite_eq_left hx] using (hex x hx).choose_spec
  have hd (x) (hx : x ∈ ball c r) : HasFDerivAt v (toDual ℝ _ (G x)) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_ball
      hderlim.tendstoLocallyUniformlyOn
      (fun j y _ => ((hw j).differentiable (by simp) y).hasFDerivAt) hlim hx
  refine ⟨v, ?_, ?_, ?_⟩
  · change ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) v (ball c r)
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn isOpen_ball.uniqueDiffOn).mpr
    refine ⟨by simp, fun x => toDual ℝ _ (G x), ?_, ?_⟩
    · exact contDiffOn_zero.mpr ((toDual ℝ _).continuous.comp_continuousOn
        (hG.mono (ball_subset_ball hrR.le)))
    · exact fun x hx => (hd x hx).hasFDerivWithinAt
  · filter_upwards [ae_restrict_of_ae hpoint, ae_restrict_mem measurableSet_ball] with x hx hxr
    exact tendsto_nhds_unique hx (hlim x hxr)
  · intro x hx
    apply (toDual ℝ _).injective
    rw [toDual_gradient, (hd x hx).fderiv]


/-- Local form of the C¹ representative bridge, requiring only the genuine
weak gradient and its continuity on the original ball. -/
theorem campanato_c1_representative_of_continuous_weak_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {c : EuclideanSpace ℝ (Fin n)} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : HasWeakGradientOn u G (ball c R)) (hG : ContinuousOn G (ball c R)) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ 1 v (ball c r) ∧ u =ᵐ[volume.restrict (ball c r)] v ∧
        ∀ x ∈ ball c r, gradient v x = G x := by
  let s := (r + R) / 2
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨η, hη, hcη, hsη, hone, _⟩ := exists_smooth_cutoff_one_near_compact
    (isCompact_closedBall c s) isOpen_ball (closedBall_subset_ball hsR)
  have hηnear (x) (hx : x ∈ closedBall c s) : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    hone.filter_mono (nhds_le_nhdsSet hx)
  have hηone (x) (hx : x ∈ closedBall c s) : η x = 1 := (hηnear x hx).self_of_nhds
  have hηgrad (x) (hx : x ∈ closedBall c s) : gradient η x = 0 := by
    unfold gradient
    rw [(hηnear x hx).fderiv_eq]
    simp
  have hcut := hu.mul_compact_cutoff (hη.of_le (by simp)) hcη hsη
  have heq : EqOn (fun x => η x • G x + u x • gradient η x) G (ball c s) := by
    intro x hx
    dsimp only
    rw [hηone x (ball_subset_closedBall hx), hηgrad x (ball_subset_closedBall hx)]
    simp
  have hcont : ContinuousOn (fun x => η x • G x + u x • gradient η x) (ball c s) :=
    (hG.mono (ball_subset_ball hsR.le)).congr heq
  obtain ⟨v, hv, he, hgrad⟩ := campanato_c1_representative_of_global_weak_gradient
    hcut hr hrs hcont
  refine ⟨v, hv, ?_, ?_⟩
  · filter_upwards [he, ae_restrict_mem measurableSet_ball] with x hx hxr
    simpa only [hηone x (ball_subset_closedBall (ball_subset_ball hrs.le hxr)), one_mul] using hx
  · intro x hx
    exact (hgrad x hx).trans (heq (ball_subset_ball hrs.le hx))

end LiquidDrop
