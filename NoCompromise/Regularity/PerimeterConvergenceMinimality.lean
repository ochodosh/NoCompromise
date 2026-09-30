module

public import NoCompromise.Regularity.PerimeterConvergenceInner

@[expose] public section

/-!
# Local quasiminimality of the actual L¹ limit

The competitor is assumed locally BV only on the original open domain. Its
finite-perimeter realization is a proved localization used inside the argument,
not an additional hypothesis on the competitor or the limiting set.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma perimeterIn_ball_le_of_inner_bounds {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    {R a₀ : ℝ} (hR : 0 < R) (ha₀ : a₀ < R) {C : ℝ≥0∞}
    (hb : ∀ a : ℝ, a₀ < a → a < R → perimeterIn F (ball x a) ≤ C) :
    perimeterIn F (ball x R) ≤ C := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  obtain ⟨u, ⟨hu, huR⟩, hXu⟩ := exists_pos_lt_subset_ball hR (isClosed_tsupport X) hX.2.2.1
  let a := (max a₀ u + R) / 2
  have hma : max a₀ u < a := by dsimp [a]; linarith [max_lt ha₀ huR]
  have haR : a < R := by dsimp [a]; linarith [max_lt ha₀ huR]
  have hua : u < a := (le_max_right _ _).trans_lt hma
  have ha₀a : a₀ < a := (le_max_left _ _).trans_lt hma
  have hXa : tsupport X ⊆ ball x a := hXu.trans (ball_subset_ball hua.le)
  have htest : IsVariationTestField (ball x a) X := ⟨hX.1, hX.2.1, hXa, hX.2.2.2⟩
  have he : (∫ z in ball x R, F.indicator (fun _ => (1 : ℝ)) z * divergenceN X z) =
      ∫ z in ball x a, F.indicator (fun _ => (1 : ℝ)) z * divergenceN X z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball
      (ball_subset_ball haR.le)
    intro z hz
    rw [divergenceN_eq_zero_of_notMem_tsupport (fun hh => hz.2 (hXa hh)), mul_zero]
  rw [he]
  have hf : ENNReal.ofReal (∫ z in ball x a,
      F.indicator (fun _ => (1 : ℝ)) z * divergenceN X z) ≤ perimeterIn F (ball x a) :=
    le_iSup_of_le X (le_iSup_of_le htest le_rfl)
  exact hf.trans (hb a ha₀a haR)

/-- The full local competitor inequality, with the original local BV hypothesis. -/
theorem perimeter_limit_local_comparison
    {U F G : Set AmbientSpace} (hU : IsOpen U)
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    (hmF : NullMeasurableSet F volume)
    (hG : IsLocallyBVOn (G.indicator (fun _ => (1 : ℝ))) U)
    {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀))
    (hlim : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0))
    (x : AmbientSpace) {R : ℝ} (hR : 0 < R) (hRU : closedBall x R ⊆ U)
    (hscale : ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hs : closure (F ∆ G) ⊆ ball x R) :
    perimeterIn F (ball x R) ≤ perimeterIn G (ball x R) +
      ENNReal.ofReal ω₀ * volume (F ∆ G) := by
  obtain ⟨G', hmG', _, hpG', heG⟩ :=
    hG.exists_finitePerimeter_eq_near_compact hU (isCompact_closedBall x R) hRU
  have hGeq := heG.self_of_nhdsSet
  obtain ⟨a₀, ⟨ha₀, ha₀R⟩, hsa⟩ := exists_pos_lt_subset_ball hR isClosed_closure hs
  apply perimeterIn_ball_le_of_inner_bounds F x hR ha₀R
  intro a ha₀a haR
  let b := (a + R) / 2
  have hab : a < b := by dsimp [b]; linarith
  have hbR : b < R := by dsimp [b]; linarith
  have hbU : closedBall x b ⊆ U := (closedBall_subset_closedBall hbR.le).trans hRU
  have hbb : ball x b ⊆ closedBall x R :=
    (ball_subset_ball hbR.le).trans ball_subset_closedBall
  have hG'F : G' =ᵐ[volume.restrict (ball x b \ closedBall x a)] F := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_closedBall)] with z hz
    change (z ∈ G') = (z ∈ F)
    have hzG : (z ∈ G) = (z ∈ G') := hGeq (hbb hz.1)
    rw [← hzG]
    have hn : z ∉ F ∆ G := by
      intro hd
      have hz₀ := hsa (subset_closure hd)
      have hza : z ∈ closedBall x a :=
        ball_subset_closedBall (ball_subset_ball ha₀a.le hz₀)
      exact hz.2 hza
    apply propext
    simp only [mem_symmDiff] at hn
    tauto
  have hi := perimeter_limit_inner_ball_comparison hE hmF hmG' hpG' hω x
    (ha₀.le.trans ha₀a.le) hab hbR hscale hG'F
    (hlim (closedBall x b) (isCompact_closedBall x b) hbU)
  have hpEq : perimeterIn G' (ball x b) = perimeterIn G (ball x b) := by
    apply perimeterIn_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (hGeq (hbb hz)).symm
  have hVEq : (F ∆ G') ∩ ball x b = (F ∆ G) ∩ ball x b := by
    ext z
    by_cases hz : z ∈ ball x b
    · have he := hGeq (hbb hz)
      change (z ∈ G) = (z ∈ G') at he
      simp only [mem_inter_iff, hz, and_true, mem_symmDiff, he]
    · simp only [mem_inter_iff, hz, and_false]
  rw [hpEq, hVEq] at hi
  exact hi.trans (add_le_add
    (variation_mono measurableSet_ball (ball_subset_ball hbR.le))
    (mul_le_mul le_rfl (measure_mono inter_subset_left) bot_le bot_le))

/-- Quasiminimality relative to an arbitrary open domain. The support condition
on the difference implies compactness because it lies in a bounded ball. -/
structure IsLocallyOmegaMinimalOn (F : Set AmbientSpace) (ω : ℝ) (U : Set AmbientSpace) : Prop where
  nonneg : 0 ≤ ω
  nullMeasurable : NullMeasurableSet F volume
  locallyBV : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U
  comparison : ∀ (x : AmbientSpace) (R : ℝ), 0 < R → closedBall x R ⊆ U →
    ∀ G : Set AmbientSpace, NullMeasurableSet G volume →
      IsLocallyBVOn (G.indicator (fun _ => (1 : ℝ))) U →
      closure (F ∆ G) ⊆ ball x R →
      perimeterIn F (ball x R) ≤ perimeterIn G (ball x R) +
        ENNReal.ofReal ω * volume (F ∆ G)

/-- Part (i) of blueprint `lem:perimeter-measure-convergence`: the genuine local
limit is quasiminimal under the stated varying-scale admissibility condition. -/
theorem locally_omegaMinimal_of_locally_l1
    {U F : Set AmbientSpace} (hU : IsOpen U)
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    (hmF : NullMeasurableSet F volume) {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀))
    (hbound : ∀ A : Set AmbientSpace, IsOpen A → IsCompact (closure A) →
      closure A ⊆ U → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (E j) A ≤ C)
    (hscale : ∀ (x : AmbientSpace) (R : ℝ), 0 < R → closedBall x R ⊆ U →
      ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) : IsLocallyOmegaMinimalOn F ω₀ U := by
  refine ⟨ge_of_tendsto hω (Eventually.of_forall fun j => (hE j).nonneg), hmF,
    locallyBV_indicator_of_locally_l1_perimeter_bound (fun j => (hE j).nullMeasurable)
      hmF hbound hlim, ?_⟩
  intro x R hR hRU G _ hG hs
  exact perimeter_limit_local_comparison hU hE hmF hG hω hlim x hR hRU
    (hscale x R hR hRU) hs

end LiquidDrop
