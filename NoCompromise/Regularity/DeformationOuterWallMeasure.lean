import NoCompromise.Regularity.DeformationAnnulus

/-! # Null vertical walls from uniformly dominated horizontal bands -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A bound on every open horizontal band transfers nullity of an interior
vertical wall. Only the source measure needs to be finite on compact sets. -/
theorem measure_cylindrical_wall_zero_of_band_bound
    (μ ρ : Measure AmbientSpace) [IsFiniteMeasureOnCompacts ρ]
    {r s : ℝ} (hs : s < r) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ a b : ℝ, b ≤ r →
      μ (cylindricalTransition r a b) ≤ C * ρ (cylindricalTransition r a b))
    (hzero : ρ {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} = 0) :
    μ {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} = 0 := by
  let δ : ℕ → ℝ := fun j => (r - s) / (j + 1)
  have hδ (j : ℕ) : 0 < δ j := div_pos (sub_pos.mpr hs) (by positivity)
  have hδle (j : ℕ) : δ j ≤ r - s := by
    dsimp [δ]
    exact div_le_self (sub_nonneg.mpr hs.le) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have htδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r - s)
  have haδ : Antitone δ := by
    intro i j hij
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hs.le) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1)
  let A : ℕ → Set AmbientSpace := fun j =>
    cylindricalTransition r (s - δ j) (s + δ j)
  have hA (j : ℕ) : MeasurableSet (A j) :=
    (isOpen_cylindricalTransition r (s - δ j) (s + δ j)).measurableSet
  have haA : Antitone A := by
    intro i j hij x hx
    exact ⟨⟨lt_of_le_of_lt (sub_le_sub_left (haδ hij) s) hx.1.1,
      lt_of_lt_of_le hx.1.2 (by linarith [haδ hij])⟩, hx.2⟩
  have hwall (j : ℕ) : {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r}
      ⊆ A j := by
    intro x hx
    exact ⟨⟨by rw [hx.1]; linarith [hδ j], by rw [hx.1]; linarith [hδ j]⟩,
      ⟨hx.1 ▸ hs, hx.2⟩⟩
  have hi : (⋂ j : ℕ, A j) =
      {x : AmbientSpace | ‖graphProjectionN 2 x‖ = s ∧ |x 2| < r} := by
    ext x
    constructor
    · intro hx
      have hxt (j : ℕ) := mem_iInter.mp hx j
      have hlow : s ≤ ‖graphProjectionN 2 x‖ := by
        have ht : Tendsto (fun j => s - δ j) atTop (𝓝 s) := by
          simpa only [sub_zero] using tendsto_const_nhds.sub htδ
        exact le_of_tendsto ht (Eventually.of_forall fun j => (hxt j).1.1.le)
      have hup : ‖graphProjectionN 2 x‖ ≤ s := by
        have ht : Tendsto (fun j => s + δ j) atTop (𝓝 s) := by
          simpa only [add_zero] using tendsto_const_nhds.add htδ
        exact ge_of_tendsto ht (Eventually.of_forall fun j => (hxt j).1.2.le)
      exact ⟨le_antisymm hup hlow, (hxt 0).2.2⟩
    · intro hx
      exact mem_iInter.mpr fun j => hwall j hx
  have hfinite : ρ (A 0) < ∞ :=
    ((isBounded_standardCylinder r).subset inter_subset_right).measure_lt_top
  have ht : Tendsto (fun j => ρ (A j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hi, hzero] using
      tendsto_measure_iInter_atTop (fun j => (hA j).nullMeasurableSet) haA ⟨0, hfinite.ne⟩
  have hmul : Tendsto (fun j => C * ρ (A j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr hC)
  apply le_antisymm ?_ bot_le
  apply ge_of_tendsto hmul
  apply Eventually.of_forall
  intro j
  exact (measure_mono (hwall j)).trans
    (hbound (s - δ j) (s + δ j) (by linarith [hδle j]))

end LiquidDrop
