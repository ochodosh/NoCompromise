import NoCompromise.Regularity.DensityCutComparison
import NoCompromise.DeGiorgi.DensityODE
import NoCompromise.Sobolev.BV

/-!
# Two-sided phase density for perimeter quasiminimizers

The proved nonsharp isoperimetric inequality is sufficient. A small cubic
barrier, depending on the quasiminimality constant, absorbs the volume error;
the existing one-dimensional barrier theorem then gives a uniform lower bound
for each phase at every essential-boundary point.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma essentialBoundary_compl {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : NullMeasurableSet E volume) : essentialBoundary Eᶜ = essentialBoundary E := by
  have hz : densityZero Eᶜ = densityOne E := by
    simpa only [compl_compl] using (densityOne_compl hmE.compl).symm
  rw [essentialBoundary, essentialBoundary, hz, densityOne_compl hmE, union_comm]

lemma radialVolume_pos_at_essentialBoundary {E : Set AmbientSpace} {x : AmbientSpace}
    (hx : x ∈ essentialBoundary E) {r : ℝ} (hr : 0 < r) : 0 < radialVolume E x r := by
  have hfin : volume (E ∩ ball x r) < ∞ :=
    (measure_mono inter_subset_right).trans_lt isBounded_ball.measure_lt_top
  have hp : 0 < volume (E ∩ ball x r) := by
    by_contra hn
    have hz : volume (E ∩ ball x r) = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hd : x ∈ densityZero E := by
      change Tendsto (densityRatio E x) (𝓝[>] (0 : ℝ)) (𝓝 0)
      apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hr)] with t ht
      have ht0 : volume (E ∩ ball x t) = 0 :=
        measure_mono_null (inter_subset_inter_right E (ball_subset_ball ht.le)) hz
      simp only [densityRatio, ht0, ENNReal.toReal_zero, zero_div]
    exact hx (Or.inl hd)
  exact ENNReal.toReal_pos hp.ne' hfin.ne

/-- The threshold below which the quasiminimality volume error is absorbable at unit scale. -/
def quasiminimalDensityBarrier (ω : ℝ) : ℝ := (1 / (2 * (ω + 1))) ^ 3

/-- An explicit two-sided density constant, strictly less than half the unit-ball volume. -/
def quasiminimalDensityConstant (ω : ℝ) : ℝ :=
  min (densityCubicConstant (quasiminimalDensityBarrier ω) (1 / 4)) ((4 * Real.pi / 3) / 4)

lemma quasiminimalDensityBarrier_pos {ω : ℝ} (hω : 0 ≤ ω) :
    0 < quasiminimalDensityBarrier ω := by unfold quasiminimalDensityBarrier; positivity

lemma quasiminimalDensityConstant_pos {ω : ℝ} (hω : 0 ≤ ω) :
    0 < quasiminimalDensityConstant ω := by
  exact lt_min (densityCubicConstant_pos (quasiminimalDensityBarrier_pos hω) (by norm_num))
    (by positivity)

lemma quasiminimalDensityConstant_lt {ω : ℝ} :
    quasiminimalDensityConstant ω < (4 * Real.pi / 3) / 2 := by
  apply (min_le_right _ _).trans_lt
  have := Real.pi_pos
  linarith

lemma volume_error_le_half_rpow_of_cubic_bound {ω m r : ℝ} (hω : 0 ≤ ω)
    (hm : 0 ≤ m) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hb : m ≤ quasiminimalDensityBarrier ω * r ^ 3) :
    ω * m ≤ (1 / 2 : ℝ) * m ^ (2 / 3 : ℝ) := by
  let a : ℝ := 1 / (2 * (ω + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have haeq : a * (2 * (ω + 1)) = 1 := by
    dsimp [a]
    exact one_div_mul_cancel (by positivity : 2 * (ω + 1) ≠ 0)
  have hcoef : ω * a ≤ 1 / 2 := by nlinarith
  have hroot : m ^ (1 / 3 : ℝ) ≤ a * r := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hm _) (mul_nonneg ha.le hr)
      (by decide : (3 : ℕ) ≠ 0)).mp
    rw [cubic_root_cube hm, mul_pow]
    exact hb
  have hroota : m ^ (1 / 3 : ℝ) ≤ a :=
    hroot.trans (mul_le_of_le_one_right ha.le hr1)
  by_cases hm0 : m = 0
  · simp [hm0]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hid : m ^ (1 / 3 : ℝ) * m ^ (2 / 3 : ℝ) = m := by
    rw [← Real.rpow_add hmpos]
    norm_num
  calc
    ω * m = (ω * m ^ (1 / 3 : ℝ)) * m ^ (2 / 3 : ℝ) := by rw [mul_assoc, hid]
    _ ≤ (1 / 2 : ℝ) * m ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hroota hω).trans hcoef) (Real.rpow_nonneg hm _)

/-- The actual isoperimetric differential inequality for the radial volume. -/
theorem IsOmegaMinimal.ae_radial_density_inequality {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) (x : AmbientSpace) :
    ∀ᵐ r : ℝ, 0 < r → r ≤ 1 →
      radialVolume E x r ^ (2 / 3 : ℝ) ≤
        2 * deriv (radialVolume E x) r + ω * radialVolume E x r := by
  have hgood := (ae_restrict_iff' measurableSet_Ioi).mp
    (ae_isGoodRadius E hE.locallyFinite hE.nullMeasurable x)
  filter_upwards [hgood, hE.ae_cut_comparison x, ae_deriv_radialVolume hE.nullMeasurable x]
    with r hg hcut hd hr hr1
  have hg' := hg hr
  have hmcut := hE.nullMeasurable.inter (measurableSet_ball (x := x) (ε := r)).nullMeasurableSet
  have hvcut : volume (E ∩ ball x r) < ∞ :=
    (measure_mono inter_subset_right).trans_lt isBounded_ball.measure_lt_top
  have hpN := hg'.hasFinitePerimeter_cut_in
  have hp : perimeter (E ∩ ball x r) < ∞ := by rwa [← perimeterN_eq_perimeter _ hmcut]
  have hi := ENNReal.toReal_mono hp.ne (volume_rpow_two_thirds_le_perimeter hmcut hvcut hp)
  have hpB := hE.locallyFinite (ball x r) isOpen_ball isBounded_ball.isCompact_closure
  have hS := hausdorffMeasure2_spherical_section_lt_top E x r
  rw [← ENNReal.toReal_rpow, hg'.perimeter_cut_identities.1,
    ENNReal.toReal_add hpB.ne hS.ne] at hi
  have hSd : (hausdorffMeasure2 3 (densityOne E ∩ sphere x r)).toReal =
      deriv (radialVolume E x) r := (hd hr).symm
  rw [hSd] at hi
  have hc := hcut hr hr1
  change radialVolume E x r ^ (2 / 3 : ℝ) ≤ _ at hi
  linarith

/-- A uniform cubic lower bound for either phase, at all unit-scale radii. -/
theorem IsOmegaMinimal.radialVolume_lower_bound {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x : AmbientSpace} (hx : x ∈ essentialBoundary E)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    quasiminimalDensityConstant ω * r ^ 3 ≤ radialVolume E x r := by
  have hd : ∀ᵐ t : ℝ, t ∈ Ioo 0 1 →
      radialVolume E x t ≤ quasiminimalDensityBarrier ω * t ^ 3 →
      (1 / 4 : ℝ) * radialVolume E x t ^ (2 / 3 : ℝ) ≤ deriv (radialVolume E x) t := by
    filter_upwards [hE.ae_radial_density_inequality x] with t ht ht01 hb
    have he := volume_error_le_half_rpow_of_cubic_bound hE.nonneg
      (radialVolume_nonneg E x t) ht01.1.le ht01.2.le hb
    have hi := ht ht01.1 ht01.2.le
    nlinarith only [he, hi]
  have hbound := cubic_lower_barrier_of_lipschitz
    (quasiminimalDensityBarrier_pos hE.nonneg) (by norm_num : (0 : ℝ) < 1 / 4)
    (lipschitzOnWith_radialVolume hE.nullMeasurable x 1) (radialVolume_zero E x)
    (fun t ht _ => radialVolume_pos_at_essentialBoundary hx ht) hd r ⟨hr, hr1⟩
  apply le_trans _ hbound
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hr _)

/-- Both phases have positive uniform cubic density at every essential-boundary point. -/
theorem IsOmegaMinimal.two_sided_density_explicit {E : Set AmbientSpace} {ω : ℝ}
    (hE : IsOmegaMinimal E ω) {x : AmbientSpace} (hx : x ∈ essentialBoundary E)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    quasiminimalDensityConstant ω * r ^ 3 ≤ radialVolume E x r ∧
      radialVolume E x r ≤ ((4 * Real.pi / 3) - quasiminimalDensityConstant ω) * r ^ 3 := by
  have hxc : x ∈ essentialBoundary Eᶜ := by rwa [essentialBoundary_compl hE.nullMeasurable]
  have hleft := hE.radialVolume_lower_bound hx hr hr1
  have hright := hE.compl.radialVolume_lower_bound hxc hr hr1
  have hsum := radialVolume_add_compl hE.nullMeasurable x hr
  exact ⟨hleft, by nlinarith only [hright, hsum]⟩

/-- Blueprint `lem:two-sided-density`, with constants chosen uniformly from `ω` alone. -/
theorem quasiminimal_two_sided_density (ω : ℝ) (hω : 0 ≤ ω) :
    ∃ r_d c_d : ℝ, 0 < r_d ∧ r_d ≤ 1 ∧ 0 < c_d ∧ c_d < (4 * Real.pi / 3) / 2 ∧
      ∀ (E : Set AmbientSpace), IsOmegaMinimal E ω → ∀ x ∈ essentialBoundary E,
        ∀ r : ℝ, 0 < r → r < r_d →
          c_d * r ^ 3 ≤ radialVolume E x r ∧
          radialVolume E x r ≤ ((4 * Real.pi / 3) - c_d) * r ^ 3 := by
  refine ⟨1, quasiminimalDensityConstant ω, by norm_num, le_rfl,
    quasiminimalDensityConstant_pos hω, quasiminimalDensityConstant_lt, ?_⟩
  intro E hE x hx r hr hr1
  exact hE.two_sided_density_explicit hx hr.le hr1.le

end LiquidDrop
