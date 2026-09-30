module

public import NoCompromise.Elliptic.CampanatoHolderSegment
public import NoCompromise.Elliptic.SobolevChainLocal

@[expose] public section

/-! The segment average has the claimed ordinary directional derivative even
when the datum is only continuous. The argument is the one-dimensional FTC,
localized to the exact segment domain. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanatoSegmentAverage_hasDerivAt_global {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {h : ℝ} (hh : h ≠ 0) (e x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => campanatoSegmentAverage g (h • e) (x + s • e))
      ((g (x + h • e) - g x) / h) 0 := by
  let f (t : ℝ) := g (x + t • e)
  have hf : Continuous f := hg.comp (continuous_const.add (continuous_id.smul continuous_const))
  let F (t : ℝ) := ∫ s in (0 : ℝ)..t, f s
  have hd (t : ℝ) : HasDerivAt F (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      (hf.stronglyMeasurableAtFilter volume (𝓝 t)) hf.continuousAt
  have heq (s : ℝ) : campanatoSegmentAverage g (h • e) (x + s • e) =
      h⁻¹ * (F (s + h) - F s) := by
    rw [campanatoSegmentAverage_eq_oriented g hh]
    congr 1
    calc
      _ = ∫ t in (0 : ℝ)..h, f (t + s) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [f]
        congr 1
        simp only [add_smul]
        abel
      _ = ∫ t in s..h + s, f t := by
        rw [intervalIntegral.integral_comp_add_right]
        simp
      _ = F (s + h) - F s := by
        dsimp only [F]
        rw [intervalIntegral.integral_interval_sub_left
          (hf.intervalIntegrable 0 (s + h)) (hf.intervalIntegrable 0 s)]
        rw [add_comm s h]
  have hs : HasDerivAt (fun s : ℝ => F (s + h)) (f h) 0 := by
    simpa only [zero_add, mul_one, id_eq, Function.comp_def] using
      (hd (0 + h)).comp 0 ((hasDerivAt_id 0).add_const h)
  rw [show (fun s : ℝ => campanatoSegmentAverage g (h • e) (x + s • e)) =
    (fun s : ℝ => h⁻¹ * (F (s + h) - F s)) from funext heq]
  convert! (hs.sub (hd 0)).const_mul h⁻¹ using 1
  simp only [f, zero_smul, add_zero]
  ring

/-- The classical directional derivative identity on exactly U_h, for positive
or negative nonzero h. No derivative of g is used. -/
theorem campanatoSegmentAverage_hasDerivAt {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContinuousOn g U)
    {h : ℝ} (hh : h ≠ 0) (e : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ campanatoSegmentDomain U (h • e)) :
    HasDerivAt (fun s : ℝ => campanatoSegmentAverage g (h • e) (x + s • e))
      ((g (x + h • e) - g x) / h) 0 := by
  let K := (fun t : ℝ => x + t • (h • e)) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image
    (continuous_const.add (continuous_id.smul continuous_const))
  have hKU : K ⊆ U := by rintro y ⟨t, ht, rfl⟩; exact hx t ht
  obtain ⟨η, hη, hcη, hsη, hone, _⟩ := exists_smooth_cutoff_one_near_compact hK hU hKU
  let g' (y : EuclideanSpace ℝ (Fin n)) := η y * g y
  have hg' : Continuous g' := (sobolevChain_contDiff_cutoff hU
    (contDiffOn_zero.mpr hg) (hη.of_le (by simp)) hsη).continuous
  obtain ⟨V, hV, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hone
  have hgeq (y) (hy : y ∈ V) : g' y = g y := by
    have hηy : η y = 1 := hVone hy
    simp only [g', hηy, one_mul]
  have hxV : x ∈ campanatoSegmentDomain V (h • e) := fun t ht => hKV (mem_image_of_mem _ ht)
  have heqavg (y) (hy : y ∈ campanatoSegmentDomain V (h • e)) :
      campanatoSegmentAverage g' (h • e) y = campanatoSegmentAverage g (h • e) y := by
    apply setIntegral_congr_fun measurableSet_Icc
    exact fun t ht => hgeq _ (hy t ht)
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, x + s • e ∈ campanatoSegmentDomain V (h • e) := by
    have htC : Continuous (fun s : ℝ => x + s • e) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have ht : Tendsto (fun s : ℝ => x + s • e) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul, add_zero] using htC.tendsto (0 : ℝ)
    exact ht ((isOpen_campanatoSegmentDomain hV (h • e)).mem_nhds hxV)
  have hzero : g' x = g x := by simpa using hgeq _ (hxV 0 (by simp))
  have hone : g' (x + h • e) = g (x + h • e) := by simpa using hgeq _ (hxV 1 (by simp))
  have hd := campanatoSegmentAverage_hasDerivAt_global hg' hh e x
  rw [hzero, hone] at hd
  exact hd.congr_of_eventuallyEq (hnear.mono (fun s hs => (heqavg _ hs).symm))

/-- The vector datum is continuous on its exact segment domain when α > 0. -/
lemma campanatoSegmentField_continuousOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : ℝ} (ha : 0 < a) (hg : ContinuousOn g U) (hf : HasFiniteHolderNormOn a g U)
    (h : ℝ) (e : EuclideanSpace ℝ (Fin n)) (he : ‖e‖ = 1) :
    ContinuousOn (campanatoSegmentField g h e) (campanatoSegmentDomain U (h • e)) := by
  have hb := (campanatoSegmentField_holder hg hf h e he).1
  apply campanato_continuousOn_of_holder_bound hb.seminorm_nonneg ha
  intro x hx y hy
  simpa only [dist_eq_norm] using campanato_holder_norm_sub_le hb hx hy

end LiquidDrop
