import NoCompromise.BV.Compactness
import NoCompromise.Regularity.DeformationClearance

/-! # Almost-everywhere refinement for compactly confined indicator perturbations -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Local L¹ convergence of indicators that agree with one fixed set outside
a compact region admits a genuine almost-everywhere convergent subsequence. -/
theorem exists_subseq_ae_of_locally_l1_fixed_exterior {n : ℕ}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))} {F B K : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : ∀ j, NullMeasurableSet (E j) volume)
    (hmF : NullMeasurableSet F volume) (hmB : NullMeasurableSet B volume)
    (hK : IsCompact K)
    (hext : ∀ j x, x ∉ K → (E j).indicator (fun _ => (1 : ℝ)) x =
      B.indicator (fun _ => (1 : ℝ)) x)
    (hlim : ∀ A : Set (EuclideanSpace ℝ (Fin n)), IsCompact A →
      Tendsto (fun j => ∫ x in A,
        |(E j).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ x ∂volume,
      Tendsto (fun j => (E (k j)).indicator (fun _ => (1 : ℝ)) x) atTop
        (𝓝 (F.indicator (fun _ => (1 : ℝ)) x)) := by
  let f (j : ℕ) := (E j).indicator (fun _ => (1 : ℝ))
  let g := F.indicator (fun _ => (1 : ℝ))
  let b := B.indicator (fun _ => (1 : ℝ))
  have hext' (j : ℕ) (x) (hx : x ∉ K) : f j x = b x := hext j x hx
  have hi (j : ℕ) : LocallyIntegrable (f j) := locallyIntegrable_indicator_one (hmE j)
  have hg : LocallyIntegrable g := locallyIntegrable_indicator_one hmF
  have hb : LocallyIntegrable b := locallyIntegrable_indicator_one hmB
  have hzero : ∀ᵐ x ∂volume.restrict Kᶜ, g x - b x = 0 := by
    have hh := ae_mem_closed_of_locally_l1_convergence hK.isClosed.isOpen_compl
      (fun j => ((hi j).sub hb).locallyIntegrableOn Kᶜ)
      ((hg.sub hb).locallyIntegrableOn Kᶜ)
      (S := ({0} : Set ℝ))
      (fun A hA _ => by
        have he (u v w : ℝ) : (u - w) - (v - w) = u - v := by ring
        simpa only [Pi.sub_apply, he] using hlim A hA)
      isClosed_singleton (fun j => ?_)
    · simpa only [mem_singleton_iff, Pi.sub_apply] using hh
    · filter_upwards [ae_restrict_mem hK.measurableSet.compl] with x hx
      change f j x - b x ∈ ({0} : Set ℝ)
      rw [hext' j x hx, sub_self]
      exact mem_singleton 0
  have hout : ∀ᵐ x ∂volume, x ∉ K → g x = b x := by
    filter_upwards [(ae_restrict_iff' hK.measurableSet.compl).mp hzero] with x hx
    exact fun hn => sub_eq_zero.mp (hx hn)
  have hezero (j : ℕ) : ∀ᵐ x ∂volume, x ∉ K → f j x - g x = 0 := by
    filter_upwards [hout] with x hx
    intro hn
    rw [hext' j x hn, hx hn, sub_self]
  have hier (j : ℕ) : Integrable (fun x => f j x - g x) volume := by
    have hiK := ((hi j).sub hg).integrableOn_isCompact hK
    apply ((integrable_indicator_iff hK.measurableSet).mpr hiK).congr
    filter_upwards [hezero j] with x hx
    by_cases hn : x ∈ K
    · exact indicator_of_mem hn _
    · rw [indicator_of_notMem hn]
      exact (hx hn).symm
  have ht : Tendsto (fun j => ∫ x, |f j x - g x|) atTop (𝓝 0) := by
    convert hlim K hK using 1
    funext j
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hezero j] with x hx
    intro hn
    rw [hx hn, abs_zero]
  have he : Tendsto (fun j => eLpNorm (f j - g) 1 volume) atTop (𝓝 0) := by
    have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    simp only [ENNReal.ofReal_zero] at ht'
    convert ht' using 1
    funext j
    rw [eLpNorm_one_eq_lintegral_enorm (f := f j - g) (hier j).aestronglyMeasurable]
    simp only [Pi.sub_apply]
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hier j)]
    simp only [Real.norm_eq_abs, Function.comp_def]
  have hm := tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero he
  exact hm.exists_seq_tendsto_ae

/-- All actual strip competitors agree pointwise with the original set outside
one fixed compact ball, independently of epsilon. -/
lemma compressionCompetitor_indicator_eq_outside_fixed_ball
    (E : Set AmbientSpace) {r σ τ : ℝ} (hr : 0 < r) (hst : σ < τ) (hτr : τ ≤ r)
    (ε c : ℝ) {x : AmbientSpace} (hx : x ∉ closedBall 0 (2 * r + 1)) :
    (compressionCompetitor E r σ τ ε c).indicator (fun _ => (1 : ℝ)) x =
      E.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hp : τ ≤ ‖graphProjectionN 2 x‖
  · exact compressionCompetitor_indicator_outside_base E r σ τ ε c hst hp
  · by_cases hh : -r ≤ x 2 ∧ x 2 < r
    · exfalso
      apply hx
      have hp' : ‖graphProjectionN 2 x‖ < r := (lt_of_not_ge hp).trans_le hτr
      have hv : |x 2| ≤ r := abs_le.mpr ⟨hh.1, hh.2.le⟩
      have he := norm_sq_graphProjectionN x
      simp only [show Fin.last 2 = (2 : Fin 3) from rfl] at he
      have hp2 := (sq_le_sq₀ (norm_nonneg _) hr.le).mpr hp'.le
      have hv2 : (x 2) ^ 2 ≤ r ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr.le).mpr hv
      change ‖x - 0‖ ≤ 2 * r + 1
      rw [sub_zero]
      nlinarith [norm_nonneg x]
    · exact compressionCompetitor_indicator_outside_height E r σ τ ε c hh

end LiquidDrop
