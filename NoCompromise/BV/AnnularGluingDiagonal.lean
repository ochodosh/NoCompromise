module

public import NoCompromise.BV.AnnularGluing

@[expose] public section

/-!
# Diagonal gluing in expanding annuli

For each fixed annulus the actual L¹ error vanishes. A strictly increasing
subsequence makes the normalized error small in the successively chosen
annuli, after which first-moment selection gives genuine good cutting radii.
-/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A rowwise null array has a null diagonal along a strictly increasing subsequence. -/
lemma exists_strictMono_diagonal_tendsto_zero {v : ℕ → ℕ → ℝ≥0∞}
    (ht : ∀ k, Tendsto (v k) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (fun k => v k (σ k)) atTop (𝓝 0) := by
  have he (k : ℕ) : 0 < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by positivity
  have hh (k : ℕ) : ∃ N, ∀ n ≥ N, v k n < ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
    eventually_atTop.mp ((tendsto_order.mp (ht k)).2 _ (he k))
  choose N hN using hh
  let σ : ℕ → ℕ := Nat.rec (N 0) (fun k p => max (N (k + 1)) (p + 1))
  have hσN : ∀ k, N k ≤ σ k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_left _ _
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact (Nat.lt_succ_self (σ k)).trans_le (le_max_right _ _)
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ⟨σ, hσ, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun k => (hN k (σ k) (hσN k)).le)⟩

/-- The expanding-annuli diagonal clause of blueprint `prop:annular-gluing`.
The hypotheses are actual local L¹ convergence on each specified annulus. -/
theorem exists_diagonal_annular_gluing_radii
    {E : ℕ → Set AmbientSpace} {F G : Set AmbientSpace}
    (hE : ∀ j, HasLocallyFinitePerimeter (E j))
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hF : HasLocallyFinitePerimeter F) (hmF : NullMeasurableSet F volume)
    (hmG : NullMeasurableSet G volume)
    (c : AmbientSpace) {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hab : ∀ k, a k < b k)
    (hat : Tendsto a atTop atTop)
    (hFG : ∀ k, F =ᵐ[volume.restrict (ball c (b k) \ closedBall c (a k))] G)
    (ht : ∀ k, Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - G.indicator (fun _ => (1 : ℝ)))
      1 (volume.restrict (ball c (b k) \ closedBall c (a k)))) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, ∃ r : ℕ → ℝ, StrictMono σ ∧ Tendsto r atTop atTop ∧
      (∀ k, r k ∈ Ioo (a k) (b k) ∧ IsGoodRadius (E (σ k)) (hE (σ k)) (hmE (σ k)) c (r k) ∧
        IsGoodRadius F hF hmF c (r k)) ∧
      Tendsto (fun k => hausdorffMeasure2 3
        ((densityOne F ∆ densityOne (E (σ k))) ∩ sphere c (r k))) atTop (𝓝 0) ∧
      (∀ k W, IsOpen W → closedBall c (b k) ⊆ W →
        perimeterIn ((F ∩ ball c (r k)) ∪ (E (σ k) \ ball c (r k))) W ≤
          perimeterIn F (ball c (r k)) + perimeterIn (E (σ k)) (W \ closedBall c (r k)) +
            hausdorffMeasure2 3 ((densityOne F ∆ densityOne (E (σ k))) ∩ sphere c (r k))) ∧
      ∀ k, perimeter ((F ∩ ball c (r k)) ∪ (E (σ k) \ ball c (r k))) ≤
        perimeterIn F (ball c (r k)) + perimeterIn (E (σ k)) (closedBall c (r k))ᶜ +
          hausdorffMeasure2 3 ((densityOne F ∆ densityOne (E (σ k))) ∩ sphere c (r k)) := by
  let v : ℕ → ℕ → ℝ≥0∞ := fun k j =>
    volume ((F ∆ E j) ∩ (ball c (b k) \ closedBall c (a k))) /
      ENNReal.ofReal (b k - a k)
  have hv (k) : Tendsto (v k) atTop (𝓝 0) := by
    have hvol : Tendsto (fun j => volume ((F ∆ E j) ∩
        (ball c (b k) \ closedBall c (a k)))) atTop (𝓝 0) := by
      simpa only [volume_symmDiff_inter_eq_indicator_error (hmE _) hmF hmG (hFG k)] using ht k
    have hden : ENNReal.ofReal (b k - a k) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hab k))).ne'
    simpa only [v, ENNReal.zero_div] using ENNReal.Tendsto.div_const hvol (Or.inr hden)
  obtain ⟨σ, hσ, hdiag⟩ := exists_strictMono_diagonal_tendsto_zero hv
  have hgood (k) : ∀ᵐ r ∂volume.restrict (Ioo (a k) (b k)),
      IsGoodRadius (E (σ k)) (hE (σ k)) (hmE (σ k)) c r ∧
        IsGoodRadius F hF hmF c r := by
    have hs : Ioo (a k) (b k) ⊆ Ioi (0 : ℝ) := fun r hr => (ha k).trans_lt hr.1
    exact (ae_restrict_of_ae_restrict_of_subset hs
      (ae_isGoodRadius (E (σ k)) (hE (σ k)) (hmE (σ k)) c)).and
      (ae_restrict_of_ae_restrict_of_subset hs (ae_isGoodRadius F hF hmF c))
  choose r hr hg hb using fun k => exists_radius_spherical_mismatch_le
    (hmE (σ k)) hmF c (ha k) (hab k) (hgood k)
  refine ⟨σ, r, hσ, tendsto_atTop_mono (fun k => (hr k).1.le) hat,
    fun k => ⟨hr k, hg k⟩, ?_, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiag
      (fun _ => bot_le) hb
  · intro k W hW hbW
    exact (hg k).1.gluing_perimeterIn_le (hg k).2 hW
      ((closedBall_subset_closedBall (hr k).2.le).trans hbW)
  · exact fun k => (hg k).1.gluing_perimeter_le (hg k).2

end LiquidDrop
