import NoCompromise.Value.Defs
import NoCompromise.Value.BoundedApprox

/-!
# Subadditivity of the value function

Bounded competitors can be separated by translation with vanishing Coulomb interaction.
Exact-volume bounded approximation then gives subadditivity for arbitrary competitors.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Bounded competitors: the key step of blueprint `lem:subadditivity`. -/
theorem valueFunction_add_le_energy_of_bounded {V₁ V₂ : ℝ} (h₁ : 0 < V₁) (h₂ : 0 < V₂)
    {A B : Set AmbientSpace} (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    (hAb : Bornology.IsBounded A) (hBb : Bornology.IsBounded B)
    (hvA : volume A = ENNReal.ofReal V₁) (hvB : volume B = ENNReal.ofReal V₂) :
    valueFunction (V₁ + V₂) ≤ energy A + energy B := by
  obtain ⟨R, hR, hAB⟩ := (hAb.union hBb).subset_ball_lt 0 (0 : AmbientSpace)
  have hAR : A ⊆ ball 0 R := fun _ hx => hAB (Or.inl hx)
  have hBR : B ⊆ ball 0 R := fun _ hx => hAB (Or.inr hx)
  let e : AmbientSpace := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  let F : ℝ → Set AmbientSpace := fun t => (fun y => y + t • e) '' B
  have hF (t : ℝ) : F t = (fun y => t • e + y) '' B := by
    simp only [F, add_comm]
  have hmF (t : ℝ) : NullMeasurableSet (F t) volume := by
    rw [hF]
    exact nullMeasurableSet_image_of_differentiable (by fun_prop)
      (fun _ _ hh => add_left_cancel hh) hB
  have hvF (t : ℝ) : volume (F t) = volume B := by
    rw [hF, volume_image_translate]
  have hIF (t : ℝ) : coulombInteraction A (F t) ≠ ∞ := by
    apply (coulombInteraction_lt_top A (F t) _ _).ne
    · rw [hvA]
      exact ENNReal.ofReal_lt_top
    · rw [hvF, hvB]
      exact ENNReal.ofReal_lt_top
  have hI : Tendsto (fun t => coulombInteraction A (F t)) atTop (𝓝 0) := by
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_coulombInteraction_translate hAR hBR he)
    change Tendsto (fun t => ENNReal.ofReal (coulombInteraction A (F t)).toReal)
      atTop (𝓝 (ENNReal.ofReal 0)) at ht
    simpa only [ENNReal.ofReal_toReal (hIF _),
      ENNReal.ofReal_zero] using ht
  have hbound : ∀ᶠ t : ℝ in atTop,
      valueFunction (V₁ + V₂) ≤ energy A + energy B + coulombInteraction A (F t) := by
    filter_upwards [eventually_gt_atTop (2 * R)] with t ht
    have hd : 0 < t - 2 * R := sub_pos.mpr ht
    have hdist : ∀ x ∈ A, ∀ y ∈ F t, t - 2 * R ≤ dist x y := by
      intro x hx y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hxR : ‖x‖ < R := by simpa using hAR hx
      have hzR : ‖z‖ < R := by simpa using hBR hz
      have ht0 : 0 ≤ t := by linarith
      have hnorm : ‖t • e‖ = t := by
        rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg ht0]
      have hid : t • e = (x - z) - (x - (z + t • e)) := by abel
      have htri := norm_sub_le (x - z) (x - (z + t • e))
      rw [← hid, hnorm] at htri
      rw [dist_eq_norm]
      have htri' := norm_sub_le x z
      linarith
    have hsep : AreSeparated A (F t) := by
      refine ⟨ENNReal.ofReal (t - 2 * R), (ENNReal.ofReal_pos.mpr hd).ne', ?_⟩
      intro x hx y hy
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdist x hx y hy)
    have hdisj : Disjoint A (F t) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have := hdist x hx x hy
      simp only [dist_self] at this
      linarith
    have hv : volume (A ∪ F t) = ENNReal.ofReal (V₁ + V₂) := by
      rw [measure_union₀ (hmF t) hdisj.aedisjoint, hvF, hvA, hvB,
        ENNReal.ofReal_add h₁.le h₂.le]
    have hp : perimeter (A ∪ F t) = perimeter A + perimeter (F t) := by
      rw [← perimeterN_eq_perimeter _ (hA.union (hmF t)),
        perimeterN_union_of_areSeparated hA (hmF t) hsep,
        perimeterN_eq_perimeter _ hA, perimeterN_eq_perimeter _ (hmF t)]
    have henergy : energy (A ∪ F t) =
        energy A + energy B + coulombInteraction A (F t) := by
      calc
        energy (A ∪ F t) = energy A + energy (F t) +
            coulombInteraction A (F t) := by
          rw [energy, hp, coulombEnergy_union A (F t) (hmF t) hdisj]
          simp only [energy]
          ac_rfl
        _ = _ := by rw [hF, energy_translate hB]
    exact (valueFunction_le (hA.union (hmF t)) hv).trans_eq henergy
  have ht := (tendsto_const_nhds (x := energy A + energy B)).add hI
  rw [add_zero] at ht
  exact ge_of_tendsto ht hbound

private theorem valueFunction_add_le_energy {V₁ V₂ : ℝ} (h₁ : 0 < V₁) (h₂ : 0 < V₂)
    {A B : Set AmbientSpace} (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume)
    (hvA : volume A = ENNReal.ofReal V₁) (hvB : volume B = ENNReal.ofReal V₂) :
    valueFunction (V₁ + V₂) ≤ energy A + energy B := by
  by_cases hEA : energy A = ∞
  · simp [hEA]
  by_cases hEB : energy B = ∞
  · simp [hEB]
  have hpA : HasFinitePerimeter A := by
    rw [HasFinitePerimeter, perimeterN_eq_perimeter _ hA]
    exact lt_of_le_of_lt (le_add_right le_rfl) (lt_top_iff_ne_top.mpr hEA)
  have hpB : HasFinitePerimeter B := by
    rw [HasFinitePerimeter, perimeterN_eq_perimeter _ hB]
    exact lt_of_le_of_lt (le_add_right le_rfl) (lt_top_iff_ne_top.mpr hEB)
  obtain ⟨F, hmF, hbF, _, hvF, hpF, hcF⟩ := exists_bounded_approximation A hA
    (by rw [hvA]; exact ENNReal.ofReal_pos.mpr h₁)
    (by rw [hvA]; exact ENNReal.ofReal_lt_top) hpA
  obtain ⟨G, hmG, hbG, _, hvG, hpG, hcG⟩ := exists_bounded_approximation B hB
    (by rw [hvB]; exact ENNReal.ofReal_pos.mpr h₂)
    (by rw [hvB]; exact ENNReal.ofReal_lt_top) hpB
  have heF : Tendsto (fun n => energy (F n)) atTop (𝓝 (energy A)) := by
    simpa only [energy, perimeterN_eq_perimeter _ (hmF _),
      perimeterN_eq_perimeter _ hA] using hpF.add hcF
  have heG : Tendsto (fun n => energy (G n)) atTop (𝓝 (energy B)) := by
    simpa only [energy, perimeterN_eq_perimeter _ (hmG _),
      perimeterN_eq_perimeter _ hB] using hpG.add hcG
  exact ge_of_tendsto' (heF.add heG) fun n =>
    valueFunction_add_le_energy_of_bounded h₁ h₂ (hmF n) (hmG n) (hbF n) (hbG n)
      ((hvF n).trans hvA) ((hvG n).trans hvB)

/-- Blueprint `lem:subadditivity`. -/
theorem valueFunction_add_le {V₁ V₂ : ℝ} (h₁ : 0 < V₁) (h₂ : 0 < V₂) :
    valueFunction (V₁ + V₂) ≤ valueFunction V₁ + valueFunction V₂ := by
  unfold valueFunction
  simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
  exact le_iInf fun A => le_iInf fun hA => le_iInf fun hvA =>
    le_iInf fun B => le_iInf fun hB => le_iInf fun hvB =>
      valueFunction_add_le_energy h₁ h₂ hA hB hvA hvB

/-- Blueprint `lem:subadditivity`, real form (`m` is finite by `valueFunction_lt_top`). -/
theorem valueFunction_add_le_toReal {V₁ V₂ : ℝ} (h₁ : 0 < V₁) (h₂ : 0 < V₂) :
    (valueFunction (V₁ + V₂)).toReal ≤ (valueFunction V₁).toReal +
      (valueFunction V₂).toReal := by
  have hfin₁ := (valueFunction_lt_top h₁).ne
  have hfin₂ := (valueFunction_lt_top h₂).ne
  simpa only [ENNReal.toReal_add hfin₁ hfin₂] using
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin₁, hfin₂⟩) (valueFunction_add_le h₁ h₂)

end LiquidDrop
