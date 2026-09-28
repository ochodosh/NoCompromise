import NoCompromise.BV.Defs
import NoCompromise.Sobolev.MaximalMeasurability
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Density representatives

The definitions in `BV.Defs` use the real volume fraction in open balls and the full
positive-radius limit. At every fixed radius this fraction is continuous in the
center for Lebesgue-measurable sets. The limit conditions therefore define Borel
sets. Lebesgue differentiation proves that density-one and density-zero points
agree almost everywhere with the set and its complement in positive dimension.
The essential boundary has zero ambient volume. All three representatives are
unchanged, pointwise as sets, by almost-everywhere changes of the original set.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma lowerSemicontinuous_toReal_of_finite {α : Type*} [TopologicalSpace α]
    {f : α → ℝ≥0∞} (hf : LowerSemicontinuous f) (hfin : ∀ x, f x ≠ ∞) :
    LowerSemicontinuous (fun x => (f x).toReal) := by
  intro x a ha
  by_cases hneg : a < 0
  · exact Eventually.of_forall fun y => hneg.trans_le ENNReal.toReal_nonneg
  · have ha' : ENNReal.ofReal a < f x :=
      (ENNReal.ofReal_lt_iff_lt_toReal (not_lt.mp hneg) (hfin x)).mpr ha
    filter_upwards [hf x _ ha'] with y hy
    exact (ENNReal.ofReal_lt_iff_lt_toReal (not_lt.mp hneg) (hfin y)).mp hy

/-- The ball-volume fraction is lower semicontinuous in its center. -/
lemma lowerSemicontinuous_densityRatio {n : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) :
    LowerSemicontinuous (fun x => densityRatio E x r) := by
  by_cases hr : 0 < r
  · have hf := lowerSemicontinuous_ballRatio (volume.restrict E) hr
    have hfin (x : EuclideanSpace ℝ (Fin n)) :
        volume.restrict E (ball x r) / volume (ball x r) ≠ ∞ := by
      apply ENNReal.div_ne_top
      · exact ne_top_of_le_ne_top measure_ball_lt_top.ne (Measure.restrict_le_self _)
      · exact (measure_ball_pos volume x hr).ne'
    have h := lowerSemicontinuous_toReal_of_finite hf hfin
    simpa only [densityRatio, ENNReal.toReal_div, Measure.restrict_apply measurableSet_ball,
      inter_comm] using h
  · simpa only [densityRatio, ball_eq_empty.mpr (not_lt.mp hr), inter_empty, measure_empty,
      ENNReal.toReal_zero, div_zero] using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ :
        EuclideanSpace ℝ (Fin n) => (0 : ℝ)))

/-- The complementary fractions add to one for every positive radius. -/
lemma densityRatio_compl {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    densityRatio Eᶜ x r = 1 - densityRatio E x r := by
  have hsum := measure_inter_add_sdiff₀ (ball x r) hE
  have h1 : volume (ball x r ∩ E) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_left)
  have h2 : volume (ball x r \ E) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hsum' := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add h1 h2] at hsum'
  have hb : (volume (ball x r)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne).ne'
  simp only [densityRatio]
  rw [div_eq_iff hb]
  rw [Set.sdiff_eq, inter_comm] at hsum'
  rw [Set.inter_comm (ball x r)] at hsum'
  field_simp
  linarith

/-- For fixed radius, the volume fraction of a measurable set is continuous. -/
lemma continuous_densityRatio {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) (r : ℝ) : Continuous (fun x => densityRatio E x r) := by
  by_cases hr : 0 < r
  · apply continuous_iff_lower_upperSemicontinuous.mpr
    refine ⟨lowerSemicontinuous_densityRatio E r, ?_⟩
    have h : UpperSemicontinuous (fun x => 1 + -(densityRatio Eᶜ x r)) :=
      upperSemicontinuous_const.add (lowerSemicontinuous_densityRatio Eᶜ r).neg
    have heq : (fun x => densityRatio E x r) =
        (fun x => 1 + -(densityRatio Eᶜ x r)) := by
      funext x
      rw [densityRatio_compl hE x hr]
      ring
    rw [heq]
    exact h
  · simpa only [densityRatio, ball_eq_empty.mpr (not_lt.mp hr), inter_empty, measure_empty,
      ENNReal.toReal_zero, div_zero] using (continuous_const : Continuous (fun _ :
        EuclideanSpace ℝ (Fin n) => (0 : ℝ)))

/-- A continuous family has a Borel limit condition along a countably generated filter. -/
lemma measurableSet_tendsto_of_continuous {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] {l : Filter β} [l.IsCountablyGenerated]
    {f : β → α → ℝ} (hf : ∀ r, Continuous (f r)) (a : ℝ) :
    MeasurableSet {x | Tendsto (fun r => f r x) l (𝓝 a)} := by
  obtain ⟨u, hu⟩ := l.exists_antitone_basis
  have heq : {x | Tendsto (fun r => f r x) l (𝓝 a)} =
      ⋂ k : ℕ, ⋃ m : ℕ, ⋂ r ∈ u m, (f r) ⁻¹' closedBall a (1 / (↑k + 1)) := by
    ext x
    simp only [mem_ofPred_eq, hu.toHasBasis.tendsto_iff nhds_basis_closedBall_inv_nat_succ,
      mem_iInter, mem_iUnion, mem_preimage, true_implies, true_and]
  rw [heq]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun m =>
    (isClosed_biInter fun r (_ : r ∈ u m) => isClosed_closedBall.preimage (hf r)).measurableSet

/-- The full positive-radius density-one condition defines a Borel set. -/
lemma measurableSet_densityOne {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) : MeasurableSet (densityOne E) :=
  measurableSet_tendsto_of_continuous (continuous_densityRatio hE) 1

/-- The full positive-radius density-zero condition defines a Borel set. -/
lemma measurableSet_densityZero {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) : MeasurableSet (densityZero E) :=
  measurableSet_tendsto_of_continuous (continuous_densityRatio hE) 0

/-- The essential boundary of a Lebesgue-measurable set is Borel. -/
lemma measurableSet_essentialBoundary {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) : MeasurableSet (essentialBoundary E) :=
  ((measurableSet_densityZero hE).union (measurableSet_densityOne hE)).compl

lemma densityRatio_nonneg {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : 0 ≤ densityRatio E x r :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma densityOne_compl {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE : NullMeasurableSet E volume) : densityOne Eᶜ = densityZero E := by
  ext x
  constructor
  · intro hx
    change Tendsto (densityRatio E x) (𝓝[>] 0) (𝓝 0)
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hx
    have heq : (fun r => (1 : ℝ) - densityRatio Eᶜ x r) =ᶠ[𝓝[>] 0] densityRatio E x := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [densityRatio_compl hE x hr]
      ring
    simpa only [sub_self] using h.congr' heq
  · intro hx
    change Tendsto (densityRatio Eᶜ x) (𝓝[>] 0) (𝓝 1)
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hx
    have heq : (fun r => (1 : ℝ) - densityRatio E x r) =ᶠ[𝓝[>] 0] densityRatio Eᶜ x := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (densityRatio_compl hE x hr).symm
    simpa only [sub_zero] using h.congr' heq

lemma disjoint_densityZero_densityOne {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    Disjoint (densityZero E) (densityOne E) := by
  apply disjoint_left.mpr
  intro x h0 h1
  exact zero_ne_one (tendsto_nhds_unique h0 h1)

/-- Lebesgue differentiation gives density one at almost every point of the set. -/
lemma ae_mem_densityOne {n : ℕ} (hn : 0 < n) (E : Set (EuclideanSpace ℝ (Fin n))) :
    ∀ᵐ x ∂volume.restrict E, x ∈ densityOne E := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hball (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
      ball x r =ᵐ[volume] closedBall x r := by
    exact ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (le_of_eq (Measure.addHaar_closedBall_eq_addHaar_ball volume x r))
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume E 1] with x hx
  have hmem : ∀ᶠ r : ℝ in 𝓝[>] 0, x ∈ closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul] using mem_closedBall_self (le_of_lt hr)
  have ht := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id hmem
  have ht' := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).comp ht
  change Tendsto (densityRatio E x) (𝓝[>] 0) (𝓝 1)
  have heq : densityRatio E x = (fun r =>
      (volume (E ∩ closedBall x r) / volume (closedBall x r)).toReal) := by
    funext r
    have hinter := ae_eq_set_inter (ae_eq_refl E) (hball x r)
    simp only [ENNReal.toReal_div, densityRatio,
      measure_congr hinter, measure_congr (hball x r)]
  rw [heq]
  simpa only [ENNReal.toReal_one, Function.comp_def] using ht'

/-- The density-one representative agrees almost everywhere with the original set. -/
lemma densityOne_ae_eq {n : ℕ} (hn : 0 < n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume) :
    densityOne E =ᵐ[volume] E := by
  have hi := ae_imp_of_ae_restrict (ae_mem_densityOne hn E)
  have ho := ae_imp_of_ae_restrict (ae_mem_densityOne hn Eᶜ)
  rw [densityOne_compl hE] at ho
  filter_upwards [hi, ho] with x hx hy
  by_cases h : x ∈ E
  · exact propext ⟨fun _ => h, fun _ => hx h⟩
  · exact propext ⟨fun h1 => False.elim
      ((disjoint_left.mp (disjoint_densityZero_densityOne E)) (hy h) h1), fun he => (h he).elim⟩

/-- The density-zero representative agrees almost everywhere with the complement. -/
lemma densityZero_ae_eq {n : ℕ} (hn : 0 < n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume) :
    densityZero E =ᵐ[volume] Eᶜ := by
  rw [← densityOne_compl hE]
  exact densityOne_ae_eq hn hE.compl

/-- The essential boundary has zero ambient Lebesgue volume. -/
lemma volume_essentialBoundary {n : ℕ} (hn : 0 < n)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume) :
    volume (essentialBoundary E) = 0 := by
  have heq : essentialBoundary E =ᵐ[volume] (∅ : Set (EuclideanSpace ℝ (Fin n))) := by
    have h := ((densityZero_ae_eq hn hE).union (densityOne_ae_eq hn hE)).compl
    exact h.trans (Eventually.of_forall fun x => by
      change (¬ (x ∉ E ∨ x ∈ E)) = False
      simp)
  rw [measure_congr heq, measure_empty]

/-- Almost-everywhere changes preserve every ball-volume fraction. -/
lemma densityRatio_congr_ae {n : ℕ} {E F : Set (EuclideanSpace ℝ (Fin n))}
    (hEF : E =ᵐ[volume] F) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    densityRatio E x r = densityRatio F x r := by
  have hi : E ∩ ball x r =ᵐ[volume] F ∩ ball x r := ae_eq_set_inter hEF (ae_eq_refl _)
  simp only [densityRatio, measure_congr hi]

/-- Almost-everywhere equal sets have exactly the same density-one representative. -/
lemma densityOne_congr_ae {n : ℕ} {E F : Set (EuclideanSpace ℝ (Fin n))}
    (hEF : E =ᵐ[volume] F) : densityOne E = densityOne F := by
  have heq : densityRatio E = densityRatio F :=
    funext fun x => funext fun r => densityRatio_congr_ae hEF x r
  simp only [densityOne, heq]

/-- Almost-everywhere equal sets have exactly the same density-zero representative. -/
lemma densityZero_congr_ae {n : ℕ} {E F : Set (EuclideanSpace ℝ (Fin n))}
    (hEF : E =ᵐ[volume] F) : densityZero E = densityZero F := by
  have heq : densityRatio E = densityRatio F :=
    funext fun x => funext fun r => densityRatio_congr_ae hEF x r
  simp only [densityZero, heq]

/-- Almost-everywhere equal sets have exactly the same essential boundary. -/
lemma essentialBoundary_congr_ae {n : ℕ} {E F : Set (EuclideanSpace ℝ (Fin n))}
    (hEF : E =ᵐ[volume] F) : essentialBoundary E = essentialBoundary F := by
  simp only [essentialBoundary, densityZero_congr_ae hEF, densityOne_congr_ae hEF]

end LiquidDrop
