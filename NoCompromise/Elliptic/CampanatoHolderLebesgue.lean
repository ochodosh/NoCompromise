import NoCompromise.Elliptic.CampanatoHolderAverages

/-! Dyadic limits of genuine volume-ball averages agree almost everywhere
with the original locally integrable function. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma campanato_dyadic_radii_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j * R) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Filter.Eventually.of_forall (fun j => ?_)⟩
  · simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const R
  · exact mul_pos (pow_pos (by norm_num) j) hR

/-- An everywhere-defined dyadic average limit is an actual representative of
an L² field on every interior set with a uniform ball neighborhood. -/
theorem campanato_ae_eq_of_dyadic_average_limit {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f g : EuclideanSpace ℝ (Fin n) → F} {U : Set (EuclideanSpace ℝ (Fin n))}
    {R : ℝ} (hU : MeasurableSet U) (hR : 0 < R)
    (hf : MemLp f 2 (volume.restrict (ball 0 1)))
    (hballs : ∀ x ∈ U, ball x R ⊆ ball 0 1)
    (hlim : ∀ x ∈ U,
      Tendsto (fun j : ℕ => ⨍ y in ball x ((1 / 2 : ℝ) ^ j * R), f y) atTop (𝓝 (g x))) :
    f =ᵐ[volume.restrict U] g := by
  let μ := volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  let : IsFiniteMeasure μ :=
    ⟨by simpa [μ] using (isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin n)))
      (r := 1)).measure_lt_top⟩
  have hsub : U ⊆ ball 0 1 := fun x hx => hballs x hx (mem_ball_self hR)
  have hi : Integrable f μ := hf.integrable (by norm_num)
  have hae := ae_tendsto_average_ball μ hi.locallyIntegrable
  have hUae : ∀ᵐ x ∂volume.restrict U, x ∈ U := ae_restrict_mem hU
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae, hUae] with x hx hxU
  have ht := hx.comp (campanato_dyadic_radii_tendsto hR)
  have heq : (fun j : ℕ => ⨍ y in ball x ((1 / 2 : ℝ) ^ j * R), f y ∂μ) =
      fun j : ℕ => ⨍ y in ball x ((1 / 2 : ℝ) ^ j * R), f y := by
    funext j
    have hs : ball x ((1 / 2 : ℝ) ^ j * R) ⊆ ball 0 1 := by
      apply (ball_subset_ball ?_).trans (hballs x hxU)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) hR.le
    change average ((volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).restrict _) f = _
    rw [Measure.restrict_restrict_of_subset hs]
  change Tendsto (fun j : ℕ =>
    ⨍ y in ball x ((1 / 2 : ℝ) ^ j * R), f y ∂μ) atTop (𝓝 (f x)) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht (hlim x hxU)

end LiquidDrop
