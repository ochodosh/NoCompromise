import NoCompromise.BV.RadialCuts
import Mathlib.MeasureTheory.Integral.Average

/-!
# Good truncation of a finite-volume finite-perimeter set

The first-moment argument selects one genuine good radius in each successive
unit interval. Spherical slicing bounds its new boundary area by the original
volume tail. Measure continuity and the exact cut identity then give perimeter
convergence, without appealing to a truncation theorem as an input.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma HasFinitePerimeter.hasLocallyFinitePerimeter {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : HasFinitePerimeter E) :
    HasLocallyFinitePerimeter E := by
  intro A _ _
  exact (variation_mono MeasurableSet.univ (subset_univ A)).trans_lt hE

/-- The tail of a finite-measure set vanishes along integer balls. -/
lemma tendsto_measure_sdiff_ball_nat_zero {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hmE : NullMeasurableSet E μ)
    (hE : μ E < ∞) (c : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k : ℕ => μ (E \ ball c k)) atTop (𝓝 0) := by
  have hanti : Antitone (fun k : ℕ => E \ ball c k) := by
    intro i j hij x hx
    exact ⟨hx.1, fun hxi => hx.2 (ball_subset_ball (by exact_mod_cast hij) hxi)⟩
  have hi : (⋂ k : ℕ, E \ ball c k) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_gt (dist x c)
    exact (mem_iInter.mp hx k).2 hk
  have ht := tendsto_measure_iInter_atTop
    (fun k : ℕ => hmE.diff measurableSet_ball.nullMeasurableSet) hanti
    ⟨0, ((measure_mono sdiff_subset).trans_lt hE).ne⟩
  simpa only [Function.comp_def, hi, measure_empty] using ht

lemma tendsto_measure_ball_nat (μ : Measure AmbientSpace) (c : AmbientSpace) :
    Tendsto (fun k : ℕ => μ (ball c k)) atTop (𝓝 (μ univ)) := by
  have hm : Monotone (fun k : ℕ => ball c k) :=
    fun i j hij => ball_subset_ball (by exact_mod_cast hij)
  simpa only [Function.comp_def, iUnion_ball_nat] using tendsto_measure_iUnion_atTop hm

/-- A good radius can be chosen in each unit interval, with its section area
bounded by the original volume outside the smaller integer ball. -/
theorem exists_goodRadius_in_unit_interval {E : Set AmbientSpace}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (c : AmbientSpace) (k : ℕ) :
    ∃ r : ℝ, (k : ℝ) < r ∧ r < k + 1 ∧ IsGoodRadius E hE hmE c r ∧
      hausdorffMeasure2 3 (densityOne E ∩ sphere c r) ≤ volume (E \ ball c k) := by
  let μ : Measure ℝ := volume.restrict (Ioo (k : ℝ) (k + 1))
  let : IsProbabilityMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    norm_num⟩
  have hg : ∀ᵐ r ∂μ, r ∈ Ioo (k : ℝ) (k + 1) ∧ IsGoodRadius E hE hmE c r := by
    have hs : Ioo (k : ℝ) (k + 1) ⊆ Ioi (0 : ℝ) :=
      fun r hr => (Nat.cast_nonneg k).trans_lt hr.1
    exact (ae_restrict_mem measurableSet_Ioo).and
      (ae_restrict_of_ae_restrict_of_subset hs (ae_isGoodRadius E hE hmE c))
  obtain ⟨r, hr, hb⟩ := exists_notMem_null_le_lintegral
    ((measurable_sphere_sections (measurableSet_densityOne hmE) c).aemeasurable (μ := μ))
    (ae_iff.mp hg)
  have hr' : r ∈ Ioo (k : ℝ) (k + 1) ∧ IsGoodRadius E hE hmE c r := by
    simpa only [mem_ofPred_eq, not_not] using hr
  refine ⟨r, hr'.1.1, hr'.1.2, hr'.2, hb.trans ?_⟩
  change (∫⁻ t in Ioo (k : ℝ) (k + 1),
    hausdorffMeasure2 3 (densityOne E ∩ sphere c t)) ≤ _
  rw [spherical_slicing hmE c (Nat.cast_nonneg k)]
  exact measure_mono (fun x hx => ⟨hx.1, hx.2.2⟩)

/-- Blueprint `lem:good-truncation`, with arbitrary fixed center. The radii are
strictly increasing, all are genuine good radii, and all three limits are
limits of the original extended-real geometric quantities. -/
theorem exists_good_truncation {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (hvE : volume E < ∞) (hpE : HasFinitePerimeter E)
    (c : AmbientSpace) :
    ∃ R : ℕ → ℝ,
      (∀ k : ℕ, (k : ℝ) < R k ∧ R k < k + 1) ∧ StrictMono R ∧ Tendsto R atTop atTop ∧
      (∀ k, IsGoodRadius E hpE.hasLocallyFinitePerimeter hmE c (R k)) ∧
      Tendsto (fun k => hausdorffMeasure2 3 (densityOne E ∩ sphere c (R k))) atTop (𝓝 0) ∧
      Tendsto (fun k => volume (E \ ball c (R k))) atTop (𝓝 0) ∧
      Tendsto (fun k => perimeter (E ∩ ball c (R k))) atTop (𝓝 (perimeter E)) := by
  choose R hRl hRu hg hs using
    exists_goodRadius_in_unit_interval hpE.hasLocallyFinitePerimeter hmE c
  have hmono : StrictMono R := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact (hRu k).trans (by simpa only [Nat.cast_add, Nat.cast_one] using hRl (k + 1))
  have htop : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun k => (hRl k).le) tendsto_natCast_atTop_atTop
  have htail := tendsto_measure_sdiff_ball_nat_zero hmE hvE c
  have hsection : Tendsto (fun k => hausdorffMeasure2 3 (densityOne E ∩ sphere c (R k)))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => bot_le) hs
  have hvol : Tendsto (fun k => volume (E \ ball c (R k))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => bot_le)
    intro k
    apply measure_mono
    intro x hx
    exact ⟨hx.1, fun hxb => hx.2 (ball_subset_ball (hRl k).le hxb)⟩
  have hp := canonicalPerimeterPolar E hpE.hasLocallyFinitePerimeter hmE
  have hperim : Tendsto (fun k => perimeterIn E (ball c (R k))) atTop
      (𝓝 (perimeter E)) := by
    have hmass := tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_measure_ball_nat (canonicalPerimeterMeasure E hpE.hasLocallyFinitePerimeter hmE) c)
      tendsto_const_nhds
      (fun k => measure_mono (ball_subset_ball (hRl k).le))
      (fun _ => measure_mono (subset_univ _))
    have htotal : canonicalPerimeterMeasure E hpE.hasLocallyFinitePerimeter hmE univ =
        perimeter E := (hp.open_eq univ isOpen_univ).trans (perimeterN_eq_perimeter E hmE)
    simpa only [hp.open_eq _ isOpen_ball, htotal] using hmass
  refine ⟨R, fun k => ⟨hRl k, hRu k⟩, hmono, htop, hg, hsection, hvol, ?_⟩
  have ht := hperim.add hsection
  simpa only [add_zero, ← (hg _).perimeter_cut_identities.1] using ht

end LiquidDrop
