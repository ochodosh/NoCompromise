import NoCompromise.Sobolev.H1TraceKernelChartGeometry
import NoCompromise.Sobolev.H1TraceKernelApprox

/-!
# Inward translations inside a boundary chart
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma exists_inward_translations_of_compact {n : ℕ} (i : Fin n)
    {K W : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) (hKi : ∀ x ∈ K, 0 ≤ x i) :
    ∃ a : ℕ → EuclideanSpace ℝ (Fin n), Tendsto a atTop (𝓝 0) ∧
      ∀ j x, x - a j ∈ K → x ∈ W ∧ 0 < x i := by
  obtain ⟨ε, hε, hεW⟩ := hK.exists_cthickening_subset_open hW hKW
  let δ (j : ℕ) : ℝ := ε * (1 / ((j : ℝ) + 1))
  let a (j : ℕ) := δ j • EuclideanSpace.single i (1 : ℝ)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδε (j : ℕ) : δ j ≤ ε := by
    have h : 1 / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h hε.le
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [mul_zero, zero_smul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε).smul
        (tendsto_const_nhds (x := EuclideanSpace.single i (1 : ℝ)))
  refine ⟨a, ha, fun j x hx => ⟨?_, ?_⟩⟩
  · apply hεW
    apply mem_cthickening_of_dist_le x (x - a j) ε K hx
    have hd : dist x (x - a j) = δ j := by
      simp only [dist_eq_norm, sub_sub_cancel, a, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hδ j), PiLp.norm_single, norm_one, mul_one]
    rw [hd]
    exact hδε j
  · have h := hKi (x - a j) hx
    simp only [PiLp.sub_apply, a, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, mul_one] at h
    linarith [hδ j]

lemma LipschitzGraphChart.mem_domain_iff_normal_pos {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (c : LipschitzGraphChart n) (hc : c.IsChartFor D)
    {x : EuclideanSpace ℝ (Fin n)} (hxr : x ∈ c.region) :
    x ∈ D ↔ 0 < c.homeomorph.symm x c.normal := by
  constructor
  · intro hxD
    have hxup : x ∈ c.upperRegion := hc.symm ▸ ⟨hxD, hxr⟩
    obtain ⟨w, hw, rfl⟩ := hxup
    simpa only [c.homeomorph.symm_apply_apply] using (show 0 < w c.normal from hw.2)
  · intro hxpos
    have hxpre : c.homeomorph.symm x ∈ coordinateCube n c.radius := by
      obtain ⟨w, hw, rfl⟩ := hxr
      simpa only [c.homeomorph.symm_apply_apply] using hw
    have hxup : x ∈ c.upperRegion :=
      ⟨c.homeomorph.symm x, ⟨hxpre, hxpos⟩, c.homeomorph.apply_symm_apply x⟩
    exact (hc ▸ hxup).1

lemma LipschitzGraphChart.mem_domain_iff_last_pos {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (c : LipschitzGraphChart (k + 1)) (hc : c.IsChartFor D)
    {x : EuclideanSpace ℝ (Fin (k + 1))} (hxr : x ∈ c.region) :
    x ∈ D ↔ 0 < c.boundaryPlaneChart.symm x (Fin.last k) := by
  rw [c.mem_domain_iff_normal_pos hc hxr]
  change _ ↔ 0 < (coareaSwap c.normal).symm (c.homeomorph.symm x) (Fin.last k)
  simp only [coareaSwap_symm_apply, Equiv.swap_apply_right]

end LiquidDrop
