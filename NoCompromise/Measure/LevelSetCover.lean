module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-!
# Hausdorff-null level sets from finite covers

At each scale a finite spatial cover and measurable target sets give a measurable
upper envelope for level-set Hausdorff content. Its integral is the finite sum of
diameter powers times target measures. Fatou's lemma and the Hausdorff covering
construction give almost-everywhere null fibers when these costs tend to zero.

This avoids assuming measurability of Hausdorff content as a function of the level.
No regularity of the scalar map or measurability of the covered set is needed here;
those geometric hypotheses belong to applications that construct the covers.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace LiquidDrop

variable {X : Type*} [EMetricSpace X]

/-- A measurable finite-cover upper envelope for the size of a level set. -/
def levelCoverMass {ι : Type*} [Fintype ι] (d : ℝ) (C : ι → Set X)
    (I : ι → Set ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑ i, (I i).indicator (fun _ => ediam (C i) ^ d) t

/-- Measurability uses only the target sets. -/
lemma measurable_levelCoverMass {ι : Type*} [Fintype ι] (d : ℝ) (C : ι → Set X)
    (I : ι → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    Measurable (levelCoverMass d C I) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (hI i)

/-- The integrated envelope is exactly the sum of covering costs. -/
lemma lintegral_levelCoverMass {ι : Type*} [Fintype ι] (d : ℝ) (C : ι → Set X)
    (I : ι → Set ℝ) (hI : ∀ i, MeasurableSet (I i)) :
    ∫⁻ t, levelCoverMass d C I t = ∑ i, ediam (C i) ^ d * volume (I i) := by
  simp only [levelCoverMass]
  rw [lintegral_finsetSum]
  · congr 1
    funext i
    exact lintegral_indicator_const (hI i) _
  · intro i _
    exact measurable_const.indicator (hI i)

variable [MeasurableSpace X] [BorelSpace X]

/-- Shrinking finite covers bound fiber Hausdorff measure by the limiting envelopes. -/
lemma hausdorffMeasure_fiber_le_liminf_levelCoverMass
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)] (d : ℝ) (hd : 0 < d)
    (u : X → ℝ) (S : Set X) (C : ∀ k, ι k → Set X) (I : ∀ k, ι k → Set ℝ)
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ k i, ediam (C k i) ≤ r k)
    (hcover : ∀ k, S ⊆ ⋃ i, C k i)
    (himage : ∀ k i, u '' (S ∩ C k i) ⊆ I k i) (t : ℝ) :
    Measure.hausdorffMeasure d (S ∩ u ⁻¹' {t}) ≤
      liminf (fun k => levelCoverMass d (C k) (I k) t) atTop := by
  classical
  let B : ∀ k, ι k → Set X := fun k i => if t ∈ I k i then C k i else ∅
  have hBdiam : ∀ k i, ediam (B k i) ≤ r k := by
    intro k i
    dsimp [B]
    split_ifs <;> simp_all only [ediam_empty, zero_le]
  have hBcover : ∀ k, S ∩ u ⁻¹' {t} ⊆ ⋃ i, B k i := by
    intro k x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover k hx.1)
    have ht : t ∈ I k i := himage k i ⟨x, ⟨hx.1, hi⟩, hx.2⟩
    exact mem_iUnion.mpr ⟨i, by simpa [B, ht] using hi⟩
  have h := Measure.hausdorffMeasure_le_liminf_sum d (S ∩ u ⁻¹' {t}) r hr B
    (Eventually.of_forall hBdiam) (Eventually.of_forall hBcover)
  convert h using 1
  congr 1
  funext k
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : t ∈ I k i
  · simp [B, ht]
  · simp [B, ht, ENNReal.zero_rpow_of_pos hd]

/-- Vanishing integrated covering costs force almost every fiber to be Hausdorff-null. -/
lemma ae_hausdorffMeasure_fiber_eq_zero_of_covers
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)] (d : ℝ) (hd : 0 < d)
    (u : X → ℝ) (S : Set X) (C : ∀ k, ι k → Set X) (I : ∀ k, ι k → Set ℝ)
    (hI : ∀ k i, MeasurableSet (I k i))
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ k i, ediam (C k i) ≤ r k)
    (hcover : ∀ k, S ⊆ ⋃ i, C k i)
    (himage : ∀ k i, u '' (S ∩ C k i) ⊆ I k i)
    (hmass : Tendsto (fun k => ∑ i, ediam (C k i) ^ d * volume (I k i)) atTop (𝓝 0)) :
    ∀ᵐ t ∂volume, Measure.hausdorffMeasure d (S ∩ u ⁻¹' {t}) = 0 := by
  have hmeas := fun k => measurable_levelCoverMass d (C k) (I k) (hI k)
  have hint : ∫⁻ t, liminf (fun k => levelCoverMass d (C k) (I k) t) atTop = 0 := by
    apply le_antisymm _ bot_le
    calc
      _ ≤ liminf (fun k => ∫⁻ t, levelCoverMass d (C k) (I k) t) atTop :=
        lintegral_liminf_le hmeas
      _ = 0 := by
        simp_rw [lintegral_levelCoverMass d _ _ (hI _)]
        exact hmass.liminf_eq
  filter_upwards [(lintegral_eq_zero_iff (Measurable.liminf hmeas)).mp hint] with t ht
  apply le_antisymm _ bot_le
  exact (hausdorffMeasure_fiber_le_liminf_levelCoverMass d hd u S C I r hr
    hdiam hcover himage t).trans (le_of_eq ht)

/-- The same criterion in the normalized Euclidean Hausdorff convention. -/
lemma ae_euclideanHausdorffMeasure_fiber_eq_zero_of_covers
    {ι : ℕ → Type*} [∀ k, Fintype (ι k)] (d : ℕ) (hd : 0 < d)
    (u : X → ℝ) (S : Set X) (C : ∀ k, ι k → Set X) (I : ∀ k, ι k → Set ℝ)
    (hI : ∀ k i, MeasurableSet (I k i))
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ k i, ediam (C k i) ≤ r k)
    (hcover : ∀ k, S ⊆ ⋃ i, C k i)
    (himage : ∀ k i, u '' (S ∩ C k i) ⊆ I k i)
    (hmass : Tendsto (fun k => ∑ i, ediam (C k i) ^ (d : ℝ) * volume (I k i))
      atTop (𝓝 0)) :
    ∀ᵐ t ∂volume, Measure.euclideanHausdorffMeasure d (S ∩ u ⁻¹' {t}) = 0 := by
  filter_upwards [ae_hausdorffMeasure_fiber_eq_zero_of_covers d (by exact_mod_cast hd)
    u S C I hI r hr hdiam hcover himage hmass] with t ht
  simp [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ht]

end LiquidDrop
