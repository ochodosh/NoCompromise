import NoCompromise.Regularity.PerimeterConvergenceGluing
import NoCompromise.Regularity.PerimeterConvergenceL1

/-! # Inner-ball comparison for local L¹ limits at varying admissible scales -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Annular L¹ convergence supplies actual glued competitors with vanishing
boundary cost; their scale-dependent comparisons pass to the limiting set. -/
theorem exists_perimeter_inner_comparison_bound
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    {F G : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hmG : NullMeasurableSet G volume) (hG : HasLocallyFinitePerimeter G)
    {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀)) (x : AmbientSpace)
    {a b R : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbR : b < R)
    (hscale : ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hGF : G =ᵐ[volume.restrict (ball x b \ closedBall x a)] F)
    (hlim : Tendsto (fun j => ∫ z in closedBall x b,
      |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) :
    ∃ B : ℕ → ℝ≥0∞,
      Tendsto B atTop (𝓝 (perimeterIn G (ball x b) +
        ENNReal.ofReal ω₀ * volume ((F ∆ G) ∩ ball x b))) ∧
      ∀ᶠ j in atTop, perimeterIn (E j) (ball x a) ≤ B j := by
  have hmE (j) := (hE j).nullMeasurable
  have hpE (j) := (hE j).locallyFinite
  have hiE (j) : IntegrableOn ((E j).indicator (fun _ => (1 : ℝ))) (closedBall x b) :=
    (locallyIntegrable_indicator_one (hmE j)).integrableOn_isCompact (isCompact_closedBall x b)
  have hiF : IntegrableOn (F.indicator (fun _ => (1 : ℝ))) (closedBall x b) :=
    (locallyIntegrable_indicator_one hmF).integrableOn_isCompact (isCompact_closedBall x b)
  have hsub : ball x b \ closedBall x a ⊆ closedBall x b :=
    sdiff_subset.trans ball_subset_closedBall
  have htann := tendsto_l1_on_subset hsub hiE hiF hlim
  have htnorm := tendsto_eLpNorm_indicator_sub_one_of_l1 hmE hmF
    (fun j => (hiE j).mono_set hsub) (hiF.mono_set hsub) htann
  obtain ⟨r, hr, hcost, _, _⟩ :=
    exists_annular_gluing_radii hpE hmE hG hmG hmF x ha hab hGF htnorm
  have hterr := tendsto_volume_symmDiff_inter_of_l1 hmE hmF
    (fun j => (hiE j).mono_set ball_subset_closedBall) (hiF.mono_set ball_subset_closedBall)
    (tendsto_l1_on_subset ball_subset_closedBall hiE hiF hlim)
  let V := volume ((F ∆ G) ∩ ball x b)
  have hV : V ≠ ∞ := (lt_of_le_of_lt (measure_mono inter_subset_right)
    (measure_ball_lt_top (μ := volume) (x := x) (r := b))).ne
  let B := fun j => perimeterIn G (ball x b) +
    hausdorffMeasure2 3 ((densityOne G ∆ densityOne (E j)) ∩ sphere x (r j)) +
      ENNReal.ofReal (ω j) * (volume ((E j ∆ F) ∩ ball x b) + V)
  have hB : ∀ᶠ j in atTop, perimeterIn (E j) (ball x a) ≤ B j := by
    filter_upwards [hscale] with j hjs
    have hj := (hE j).perimeterIn_goodRadius_gluing_le
      (hr j).2.1 (hr j).2.2 ((hr j).1.2.trans hbR) hjs
    have hleft : perimeterIn (E j) (ball x a) ≤ perimeterIn (E j) (ball x (r j)) :=
      variation_mono measurableSet_ball (ball_subset_ball (hr j).1.1.le)
    have hright : perimeterIn G (ball x (r j)) ≤ perimeterIn G (ball x b) :=
      variation_mono measurableSet_ball (ball_subset_ball (hr j).1.2.le)
    have hvol : volume ((E j ∆ G) ∩ ball x (r j)) ≤ volume ((E j ∆ F) ∩ ball x b) + V :=
      (measure_mono (inter_subset_inter_right _ (ball_subset_ball (hr j).1.2.le))).trans
        (volume_symmDiff_inter_triangle (hmE j) hmF hmG)
    exact (hleft.trans hj).trans
      (add_le_add (add_le_add hright le_rfl) (mul_le_mul le_rfl hvol bot_le bot_le))
  have hω' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω
  have herrV : Tendsto (fun j => volume ((E j ∆ F) ∩ ball x b) + V) atTop (𝓝 V) := by
    simpa only [zero_add] using hterr.add_const V
  have hpen := ENNReal.Tendsto.mul hω' (Or.inr hV) herrV
    (Or.inr ENNReal.ofReal_ne_top)
  have hBt : Tendsto B atTop
      (𝓝 (perimeterIn G (ball x b) + ENNReal.ofReal ω₀ * V)) := by
    simpa only [B, Function.comp_def, add_zero] using
      ((tendsto_const_nhds.add hcost).add hpen)
  exact ⟨B, hBt, hB⟩

/-- The interior competitor inequality passes to the L¹ limit. -/
theorem perimeter_limit_inner_ball_comparison
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    {F G : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hmG : NullMeasurableSet G volume) (hG : HasLocallyFinitePerimeter G)
    {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀)) (x : AmbientSpace)
    {a b R : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbR : b < R)
    (hscale : ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hGF : G =ᵐ[volume.restrict (ball x b \ closedBall x a)] F)
    (hlim : Tendsto (fun j => ∫ z in closedBall x b,
      |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) :
    perimeterIn F (ball x a) ≤ perimeterIn G (ball x b) +
      ENNReal.ofReal ω₀ * volume ((F ∆ G) ∩ ball x b) := by
  obtain ⟨B, hBt, hB⟩ := exists_perimeter_inner_comparison_bound
    hE hmF hmG hG hω x ha hab hbR hscale hGF hlim
  have hiE (j) : IntegrableOn ((E j).indicator (fun _ => (1 : ℝ))) (closedBall x b) :=
    (locallyIntegrable_indicator_one (hE j).nullMeasurable).integrableOn_isCompact
      (isCompact_closedBall x b)
  have hiF : IntegrableOn (F.indicator (fun _ => (1 : ℝ))) (closedBall x b) :=
    (locallyIntegrable_indicator_one hmF).integrableOn_isCompact (isCompact_closedBall x b)
  have hlsc := perimeterIn_le_liminf_of_locally_l1 isOpen_ball
    (fun j => (hE j).nullMeasurable) hmF
    (fun K _ hKA => tendsto_l1_on_subset
      (hKA.trans ((ball_subset_ball hab.le).trans ball_subset_closedBall)) hiE hiF hlim)
  exact hlsc.trans ((liminf_le_liminf hB).trans_eq hBt.liminf_eq)

/-- The same genuine competitors control the upper limit of the original perimeters. -/
theorem limsup_perimeter_inner_ball_le
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    {F G : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hmG : NullMeasurableSet G volume) (hG : HasLocallyFinitePerimeter G)
    {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀)) (x : AmbientSpace)
    {a b R : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbR : b < R)
    (hscale : ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hGF : G =ᵐ[volume.restrict (ball x b \ closedBall x a)] F)
    (hlim : Tendsto (fun j => ∫ z in closedBall x b,
      |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) :
    limsup (fun j => perimeterIn (E j) (ball x a)) atTop ≤
      perimeterIn G (ball x b) + ENNReal.ofReal ω₀ * volume ((F ∆ G) ∩ ball x b) := by
  obtain ⟨B, hBt, hB⟩ := exists_perimeter_inner_comparison_bound
    hE hmF hmG hG hω x ha hab hbR hscale hGF hlim
  exact (limsup_le_limsup hB).trans_eq hBt.limsup_eq

end LiquidDrop
