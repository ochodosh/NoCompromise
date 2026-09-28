import NoCompromise.BV.ExactCuts
import NoCompromise.Energy.Coulomb

/-!
# Perimeter splitting at a good radius

Blueprint `lem:perimeter-splitting`: the exact identity `perimeter_cut_add` and the
asymptotic inequality `perimeter_splitting`.
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LiquidDrop

/-- The canonical perimeter measure splits across a sphere carrying no mass. -/
theorem perimeterIn_ball_add_perimeterIn_compl_closedBall
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {R : ℝ}
    (hR : IsGoodRadius E hE hmE 0 R) :
    perimeterIn E (ball 0 R) + perimeterIn E (closedBall 0 R)ᶜ = perimeter E := by
  classical
  set μ := canonicalPerimeterMeasure E hE hmE with hμ
  have hp := canonicalPerimeterPolar E hE hmE
  have hball : μ (ball (0 : AmbientSpace) R) = perimeterIn E (ball 0 R) :=
    canonicalPerimeterMeasure_open E hE hmE isOpen_ball
  have hout : μ (closedBall (0 : AmbientSpace) R)ᶜ = perimeterIn E (closedBall 0 R)ᶜ :=
    canonicalPerimeterMeasure_open E hE hmE isClosed_closedBall.isOpen_compl
  have huniv : μ (univ : Set AmbientSpace) = perimeter E :=
    (canonicalPerimeterMeasure_open E hE hmE isOpen_univ).trans
      (perimeterN_eq_perimeter E hmE)
  have hdisj : Disjoint (ball (0 : AmbientSpace) R) (closedBall (0 : AmbientSpace) R)ᶜ :=
    disjoint_compl_right_iff_subset.mpr ball_subset_closedBall
  have hadd : μ (ball (0 : AmbientSpace) R) + μ (closedBall (0 : AmbientSpace) R)ᶜ =
      μ (ball (0 : AmbientSpace) R ∪ (closedBall (0 : AmbientSpace) R)ᶜ) :=
    (measure_union hdisj isClosed_closedBall.measurableSet.compl).symm
  refine le_antisymm ?_ ?_
  · rw [← hball, ← hout, hadd, ← huniv]
    exact measure_mono (subset_univ _)
  · rw [← hball, ← hout, hadd, ← huniv]
    have hcover : (univ : Set AmbientSpace) ⊆
        (ball (0 : AmbientSpace) R ∪ (closedBall (0 : AmbientSpace) R)ᶜ) ∪
          sphere (0 : AmbientSpace) R := by
      intro x _
      rcases lt_trichotomy (dist x (0 : AmbientSpace)) R with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr (by simpa [mem_closedBall] using not_le.mpr h))
    calc μ (univ : Set AmbientSpace)
        ≤ μ ((ball (0 : AmbientSpace) R ∪ (closedBall (0 : AmbientSpace) R)ᶜ) ∪
            sphere (0 : AmbientSpace) R) := measure_mono hcover
      _ ≤ μ (ball (0 : AmbientSpace) R ∪ (closedBall (0 : AmbientSpace) R)ᶜ) +
            μ (sphere (0 : AmbientSpace) R) := measure_union_le _ _
      _ = μ (ball (0 : AmbientSpace) R ∪ (closedBall (0 : AmbientSpace) R)ᶜ) := by
            rw [hR.2.1, add_zero]

/-- Blueprint `eq:perimeter-splitting-exact`. -/
theorem perimeter_cut_add (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {R : ℝ}
    (hR : IsGoodRadius E hE hmE 0 R) :
    perimeter (E ∩ ball 0 R) + perimeter (E \ ball 0 R) =
      perimeter E + 2 * hausdorffMeasure2 3 (densityOne E ∩ sphere 0 R) := by
  obtain ⟨hin, hoff⟩ := hR.perimeter_cut_identities
  rw [hin, hoff, ← perimeterIn_ball_add_perimeterIn_compl_closedBall E hE hmE hR]
  ring

/-- The local L¹ distance of two indicators on a set is the volume of the symmetric
difference inside it. -/
theorem setIntegral_abs_indicator_sub (A B K : Set AmbientSpace)
    (hA : NullMeasurableSet A volume) (hB : NullMeasurableSet B volume) :
    (∫ x in K, |A.indicator (fun _ => (1 : ℝ)) x - B.indicator (fun _ => (1 : ℝ)) x|) =
      volume.real (symmDiff A B ∩ K) := by
  have hAB : NullMeasurableSet (symmDiff A B) (volume.restrict K) :=
    (hA.symmDiff hB).mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  calc
    _ = ∫ x in K, (symmDiff A B).indicator (fun _ => (1 : ℝ)) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB, mem_symmDiff]
    _ = _ := by
      rw [integral_indicator₀ hAB, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_restrict_apply₀ hAB]

/-- Global L¹ convergence, measured by the symmetric difference, implies local L¹ convergence. -/
theorem tendsto_setIntegral_abs_indicator_sub_of_symmDiff
    {A : ℕ → Set AmbientSpace} {B : Set AmbientSpace}
    (hA : ∀ n, NullMeasurableSet (A n) volume) (hB : NullMeasurableSet B volume)
    (hconv : Tendsto (fun n => volume (symmDiff (A n) B)) atTop (𝓝 0)) (K : Set AmbientSpace) :
    Tendsto (fun n => ∫ x in K,
      |(A n).indicator (fun _ => (1 : ℝ)) x - B.indicator (fun _ => (1 : ℝ)) x|) atTop (𝓝 0) := by
  simp_rw [setIntegral_abs_indicator_sub _ _ K (hA _) hB]
  have hreal : Tendsto (fun n => volume.real (symmDiff (A n) B)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    simpa [measureReal_def, Function.comp_def] using this
  have hfin : ∀ᶠ n in atTop, volume (symmDiff (A n) B) ≠ ∞ :=
    (hconv.eventually (gt_mem_nhds zero_lt_one)).mono fun n hn => (hn.trans ENNReal.one_lt_top).ne
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hreal
  filter_upwards [hfin] with n hn
  exact measureReal_mono inter_subset_left hn

/-- Blueprint `lem:perimeter-splitting`, asymptotic form:
`Per(E_n) ≥ Per(E) + Per(G_n) + o(1)` along good radii with `a_n → 0` and `F_n → E` in `L¹`. -/
theorem perimeter_splitting {C : ℝ}
    (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (hE : ∀ n, HasLocallyFinitePerimeter (E n)) (hmE : ∀ n, NullMeasurableSet (E n) volume)
    (hmF : NullMeasurableSet F volume)
    (hper : ∀ n, perimeter (E n) ≤ ENNReal.ofReal C)
    (R : ℕ → ℝ) (hR : ∀ n, IsGoodRadius (E n) (hE n) (hmE n) 0 (R n))
    (ha : Tendsto (fun n => hausdorffMeasure2 3 (densityOne (E n) ∩ sphere 0 (R n)))
      atTop (𝓝 0))
    (hconv : Tendsto (fun n => volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop (𝓝 0)) :
    perimeter F < ∞ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n,
      (perimeter F).toReal + (perimeter (E n \ ball 0 (R n))).toReal + ε n ≤
        (perimeter (E n)).toReal := by
  set a : ℕ → ℝ≥0∞ := fun n => hausdorffMeasure2 3 (densityOne (E n) ∩ sphere 0 (R n)) with ha_def
  have hmFn : ∀ n, NullMeasurableSet (E n ∩ ball 0 (R n)) volume :=
    fun n => (hmE n).inter measurableSet_ball.nullMeasurableSet
  have hexact : ∀ n, perimeter (E n ∩ ball 0 (R n)) + perimeter (E n \ ball 0 (R n)) =
      perimeter (E n) + 2 * a n := fun n => perimeter_cut_add (E n) (hE n) (hmE n) (hR n)
  -- lower semicontinuity of perimeter under global L¹ convergence
  have hlsc : perimeter F ≤ liminf (fun n => perimeter (E n ∩ ball 0 (R n))) atTop := by
    have h := perimeterIn_le_liminf_of_locally_l1 (U := Set.univ) isOpen_univ hmFn hmF
      (fun K _ _ => tendsto_setIntegral_abs_indicator_sub_of_symmDiff hmFn hmF hconv K)
    have h1 : perimeterIn F univ = perimeter F := perimeterN_eq_perimeter F hmF
    have h2 : ∀ n, perimeterIn (E n ∩ ball 0 (R n)) univ = perimeter (E n ∩ ball 0 (R n)) :=
      fun n => perimeterN_eq_perimeter _ (hmFn n)
    simpa only [h1, h2] using h
  have hC : ENNReal.ofReal C < ∞ := ENNReal.ofReal_lt_top
  have ha_small : ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ n in atTop, a n < δ :=
    fun δ hδ => ha.eventually (gt_mem_nhds hδ)
  -- the pieces have finite perimeter whenever `a n` is finite
  have hFn_le : ∀ n, perimeter (E n ∩ ball 0 (R n)) ≤ ENNReal.ofReal C + 2 * a n := fun n =>
    le_self_add.trans ((hexact n).le.trans (add_le_add (hper n) le_rfl))
  have hGn_le : ∀ n, perimeter (E n \ ball 0 (R n)) ≤ ENNReal.ofReal C + 2 * a n := fun n =>
    le_add_self.trans ((hexact n).le.trans (add_le_add (hper n) le_rfl))
  have hPF : perimeter F < ∞ := by
    refine lt_of_le_of_lt (hlsc.trans (liminf_le_of_frequently_le' ?_)) (b := ENNReal.ofReal C + 2)
      (ENNReal.add_lt_top.mpr ⟨hC, ENNReal.ofNat_lt_top⟩)
    refine (ha_small 1 zero_lt_one).frequently.mono fun n hn => (hFn_le n).trans ?_
    gcongr
    calc 2 * a n ≤ 2 * 1 := by gcongr
      _ = 2 := mul_one 2
  refine ⟨hPF, ?_⟩
  set X : ℕ → ℝ := fun n => (perimeter (E n)).toReal - (perimeter F).toReal -
    (perimeter (E n \ ball 0 (R n))).toReal with hX
  refine ⟨fun n => min 0 (X n), ?_, fun n => ?_⟩
  swap
  · have := min_le_right (0 : ℝ) (X n)
    simp only [hX] at this ⊢
    linarith
  -- `min 0 (X n) → 0`, i.e. `X n ≥ -δ` eventually
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hPFr : ENNReal.ofReal ((perimeter F).toReal - δ / 2) < liminf
      (fun n => perimeter (E n ∩ ball 0 (R n))) atTop ∨ (perimeter F).toReal - δ / 2 < 0 := by
    by_cases hneg : (perimeter F).toReal - δ / 2 < 0
    · exact Or.inr hneg
    · left
      refine lt_of_lt_of_le ?_ hlsc
      have hge := not_lt.mp hneg
      have hpos : 0 < (perimeter F).toReal := by linarith
      calc ENNReal.ofReal ((perimeter F).toReal - δ / 2)
          < ENNReal.ofReal (perimeter F).toReal :=
            (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)
        _ = perimeter F := ENNReal.ofReal_toReal hPF.ne
  have hev_lsc : ∀ᶠ n in atTop,
      (perimeter F).toReal - δ / 2 ≤ (perimeter (E n ∩ ball 0 (R n))).toReal := by
    rcases hPFr with h | h
    · filter_upwards [eventually_lt_of_lt_liminf h, ha_small 1 zero_lt_one] with n hn han
      have hfin : perimeter (E n ∩ ball 0 (R n)) ≠ ∞ :=
        ((hFn_le n).trans_lt (ENNReal.add_lt_top.mpr ⟨hC, ENNReal.mul_lt_top (by simp)
          (han.trans ENNReal.one_lt_top)⟩)).ne
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hn.le
    · exact Eventually.of_forall fun n => h.le.trans ENNReal.toReal_nonneg
  have hev_a : ∀ᶠ n in atTop, a n < ENNReal.ofReal (δ / 4) :=
    ha_small _ (ENNReal.ofReal_pos.mpr (by linarith))
  obtain ⟨N, hN⟩ := (hev_lsc.and hev_a).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have hafin : a n ≠ ∞ := (h2.trans ENNReal.ofReal_lt_top).ne
  have har : (a n).toReal < δ / 4 := by
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hafin]
    · exact h2
  have hEfin : perimeter (E n) ≠ ∞ := ((hper n).trans_lt hC).ne
  have hFnfin : perimeter (E n ∩ ball 0 (R n)) ≠ ∞ :=
    ((hFn_le n).trans_lt (ENNReal.add_lt_top.mpr ⟨hC, ENNReal.mul_lt_top (by simp)
      hafin.lt_top⟩)).ne
  have hGnfin : perimeter (E n \ ball 0 (R n)) ≠ ∞ :=
    ((hGn_le n).trans_lt (ENNReal.add_lt_top.mpr ⟨hC, ENNReal.mul_lt_top (by simp)
      hafin.lt_top⟩)).ne
  have hreal := congrArg ENNReal.toReal (hexact n)
  rw [ENNReal.toReal_add hFnfin hGnfin, ENNReal.toReal_add hEfin
    (ENNReal.mul_ne_top (by simp) hafin), ENNReal.toReal_mul] at hreal
  simp only [ENNReal.toReal_ofNat] at hreal
  have hXn : -δ < X n := by
    simp only [hX]
    linarith [ENNReal.toReal_nonneg (a := a n)]
  rw [Real.dist_eq, sub_zero, abs_of_nonpos (min_le_left _ _)]
  rcases le_total 0 (X n) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

end LiquidDrop
