import NoCompromise.Compactness.Decomposition
import NoCompromise.Compactness.Nonvanishing
import NoCompromise.Value.Defs
import NoCompromise.Value.Continuity
import NoCompromise.Binding.Strict
import NoCompromise.Threshold.Defs

/-!
# Existence below the threshold (blueprint chapter 19)

Blueprint `prop:existence-subcritical`: for `0 < V < V_*` the infimum `m(V)` is attained.

The proof uses `thm:compactness` (`compactness_of_volume_perimeter_bounds`) and
`thm:decomposition` (`decomposition`), both proved. The two ingredients from other chapters
are packaged as named predicates:
* `ValueFunctionContinuous` — blueprint `prop:m-continuous` (Chapter 17), proved here as
  `valueFunctionContinuous` from `valueFunction_continuousOn`;
* `StrictBinding` — blueprint `prop:strict-binding` (Chapter 18), proved from the named
  hypothesis `SharpIsoperimetric` (`thm:sharp-isoperimetric`, Chapter 13) by `strict_binding`.
Hence the final statement `exists_minimizer_subcritical_of_sharp_isoperimetric` depends only on
`SharpIsoperimetric`. The finiteness half of `lem:m-finite` is the proved
`valueFunction_lt_top`; its positivity half is not used by this argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LiquidDrop

/-- Blueprint `prop:m-continuous` as a named hypothesis: `m` is continuous on `(0, ∞)`.
Its values there are finite (`valueFunction_lt_top`), so continuity in `ℝ≥0∞` is continuity
of the real-valued function `m : (0, ∞) → (0, ∞)`. -/
def ValueFunctionContinuous : Prop :=
  ContinuousOn valueFunction (Ioi 0)

/-- Blueprint `prop:strict-binding` (`eq:strict-binding`) as a named hypothesis:
`m(V) < m(sV) + m((1-s)V)` for `0 < V < V_*` and `s ∈ (0, 1)`. -/
def StrictBinding : Prop :=
  ∀ V : ℝ, 0 < V → V < criticalVolume → ∀ s ∈ Ioo (0 : ℝ) 1,
    valueFunction V < valueFunction (s * V) + valueFunction ((1 - s) * V)

/-- Blueprint `prop:m-continuous` in the form of `ValueFunctionContinuous`. -/
theorem valueFunctionContinuous : ValueFunctionContinuous := by
  refine (ENNReal.continuous_ofReal.comp_continuousOn valueFunction_continuousOn).congr ?_
  intro V hV
  exact (ENNReal.ofReal_toReal (valueFunction_lt_top hV).ne).symm

/-- Blueprint `prop:strict-binding` in the form of `StrictBinding`, modulo
`thm:sharp-isoperimetric`. -/
theorem strictBinding_of_sharpIsoperimetric (hiso : SharpIsoperimetric) : StrictBinding :=
  fun _ hV hVc _ hs => strict_binding hiso hV hVc hs.1 hs.2

/-- Finite perimeter gives local finiteness of perimeter. -/
theorem hasLocallyFinitePerimeter_of_perimeter_lt_top {E : Set AmbientSpace}
    (hmE : NullMeasurableSet E volume) (h : perimeter E < ∞) :
    HasLocallyFinitePerimeter E := by
  intro U _ _
  have hN : perimeterN E < ∞ := by rw [perimeterN_eq_perimeter E hmE]; exact h
  exact (variation_mono MeasurableSet.univ (subset_univ U)).trans_lt hN

/-- Cutting a finite-perimeter set along a good sphere leaves an outer piece of finite
perimeter (`perimeter_cut_add` and the finite area of the sphere). -/
theorem perimeter_sdiff_ball_lt_top {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {R : ℝ} (hR : IsGoodRadius E hE hmE 0 R)
    (hper : perimeter E < ∞) : perimeter (E \ ball 0 R) < ∞ := by
  have h := perimeter_cut_add E hE hmE hR
  have ha : hausdorffMeasure2 3 (densityOne E ∩ sphere 0 R) < ∞ := by
    refine (measure_mono inter_subset_right).trans_lt ?_
    rw [hausdorffMeasure2_sphere 0 hR.1]
    exact ENNReal.ofReal_lt_top
  have hle : perimeter (E \ ball 0 R) ≤
      perimeter E + 2 * hausdorffMeasure2 3 (densityOne E ∩ sphere 0 R) := by
    rw [← h]
    exact le_add_self
  exact hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hper, ENNReal.mul_lt_top (by simp) ha⟩)

private theorem energy_toReal_eq {X : Set AmbientSpace} (hP : perimeter X < ∞)
    (hD : coulombEnergy X < ∞) :
    (energy X).toReal = (perimeter X).toReal + (coulombEnergy X).toReal := by
  rw [energy]
  exact ENNReal.toReal_add hP.ne hD.ne

private theorem energy_lt_top {X : Set AmbientSpace} (hP : perimeter X < ∞)
    (hD : coulombEnergy X < ∞) : energy X < ∞ := by
  rw [energy]
  exact ENNReal.add_lt_top.mpr ⟨hP, hD⟩

/-- Blueprint `prop:existence-subcritical`, modulo `prop:m-continuous` and
`prop:strict-binding`: for `0 < V < V_*` the infimum `m(V)` is attained by a Borel set,
which is a fixed-volume minimiser among Lebesgue-measurable competitors. -/
theorem exists_minimizer_subcritical_of_m_continuous_of_strict_binding
    (hcont : ValueFunctionContinuous) (hbind : StrictBinding)
    {V : ℝ} (hV : 0 < V) (hVc : V < criticalVolume) :
    ∃ Ω : Set AmbientSpace, MeasurableSet Ω ∧ IsLebesgueFixedVolumeMinimizer V Ω ∧
      energy Ω = valueFunction V := by
  have hm : valueFunction V < ∞ := valueFunction_lt_top hV
  -- a minimising sequence
  have hseq : ∀ n : ℕ, ∃ E : Set AmbientSpace, NullMeasurableSet E volume ∧
      volume E = ENNReal.ofReal V ∧
      energy E < valueFunction V + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : 0 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := ENNReal.ofReal_pos.mpr (by positivity)
    have hlt : (⨅ (E : Set AmbientSpace) (_ : NullMeasurableSet E volume)
        (_ : volume E = ENNReal.ofReal V), energy E) <
          valueFunction V + ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ENNReal.lt_add_right hm.ne hpos.ne'
    obtain ⟨E, hE⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hmE, hE⟩ := iInf_lt_iff.mp hE
    obtain ⟨hvE, hE⟩ := iInf_lt_iff.mp hE
    exact ⟨E, hmE, hvE, hE⟩
  choose E hmE hvE hEn using hseq
  have hlim : Tendsto (fun n => energy (E n)) atTop (𝓝 (valueFunction V)) := by
    have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : Tendsto (fun n : ℕ => valueFunction V + ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (𝓝 (valueFunction V)) := by
      simpa using (tendsto_const_nhds (x := valueFunction V)).add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => valueFunction_le (hmE n) (hvE n)) (fun n => (hEn n).le)
  -- uniform bounds
  set C0 : ℝ := max V ((valueFunction V).toReal + 1) with hC0
  have hC0pos : 0 < C0 := lt_of_lt_of_le hV (le_max_left _ _)
  have hVC0 : ENNReal.ofReal V ≤ ENNReal.ofReal C0 :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have henergy_le : ∀ n, energy (E n) ≤ ENNReal.ofReal C0 := by
    intro n
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc energy (E n) ≤ valueFunction V + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := (hEn n).le
      _ ≤ ENNReal.ofReal (valueFunction V).toReal + ENNReal.ofReal 1 := by
        rw [ENNReal.ofReal_toReal hm.ne]
        exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal h1)
      _ = ENNReal.ofReal ((valueFunction V).toReal + 1) :=
        (ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one).symm
      _ ≤ ENNReal.ofReal C0 := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hper_le : ∀ n, perimeter (E n) ≤ ENNReal.ofReal C0 := fun n =>
    (le_self_add : perimeter (E n) ≤ perimeter (E n) + coulombEnergy (E n)).trans
      (henergy_le n)
  have hfinP : ∀ n, HasFinitePerimeter (E n) := fun n => by
    change perimeterN (E n) < ∞
    rw [perimeterN_eq_perimeter _ (hmE n)]
    exact (hper_le n).trans_lt ENNReal.ofReal_lt_top
  -- compactness
  obtain ⟨σ, hσ, w, F, hFmeas, -, hFfp, hFpos, hFle, hconv, -, -⟩ :=
    compactness_of_volume_perimeter_bounds hV hC0pos E hmE hfinP (fun n => (hvE n).ge)
      (fun n => (hvE n).le.trans hVC0) hper_le
  set A : ℕ → Set AmbientSpace := fun j => (fun y => w j + y) '' E (σ j) with hA
  have hmA : ∀ j, NullMeasurableSet (A j) volume := fun j =>
    nullMeasurableSet_image_of_differentiable (by fun_prop) (fun _ _ h => add_left_cancel h)
      (hmE (σ j))
  have hvA : ∀ j, volume (A j) = ENNReal.ofReal V := fun j => by
    simp only [hA]
    rw [volume_image_translate]
    exact hvE _
  have hpA : ∀ j, perimeter (A j) = perimeter (E (σ j)) := fun j =>
    perimeter_image_translate (hmE _) _
  have heA : ∀ j, energy (A j) = energy (E (σ j)) := fun j => energy_translate (hmE _) _
  have hPA : ∀ j, perimeter (A j) < ∞ := fun j => by
    rw [hpA]
    exact (hper_le _).trans_lt ENNReal.ofReal_lt_top
  have hlfpA : ∀ j, HasLocallyFinitePerimeter (A j) := fun j =>
    hasLocallyFinitePerimeter_of_perimeter_lt_top (hmA j) (hPA j)
  -- decomposition
  obtain ⟨R, -, hgood, -, -, hvolFn, hvolsplit, ⟨ε, hε, hperS⟩, ⟨δ, hδ, hDS⟩⟩ :=
    decomposition A F hlfpA hmA hFmeas.nullMeasurableSet
      (fun j => (hvA j).le.trans hVC0) hFle (fun j => (hpA j).le.trans (hper_le _)) hconv
  have hFnull : NullMeasurableSet F volume := hFmeas.nullMeasurableSet
  have hFfin : volume F < ∞ := hFle.trans_lt ENNReal.ofReal_lt_top
  have hPF : perimeter F < ∞ := by
    rw [← perimeterN_eq_perimeter F hFnull]
    exact hFfp
  have hDF : coulombEnergy F < ∞ := coulombEnergy_lt_top F hFfin
  have hvAfin : ∀ j, volume (A j) < ∞ := fun j => by
    rw [hvA]
    exact ENNReal.ofReal_lt_top
  have hDA : ∀ j, coulombEnergy (A j) < ∞ := fun j => coulombEnergy_lt_top _ (hvAfin j)
  have hvG : ∀ j, volume (A j \ ball 0 (R j)) < ∞ := fun j =>
    (measure_mono sdiff_subset).trans_lt (hvAfin j)
  have hvFn : ∀ j, volume (A j ∩ ball 0 (R j)) < ∞ := fun j =>
    (measure_mono inter_subset_left).trans_lt (hvAfin j)
  have hPG : ∀ j, perimeter (A j \ ball 0 (R j)) < ∞ := fun j =>
    perimeter_sdiff_ball_lt_top (hlfpA j) (hmA j) (hgood j) (hPA j)
  have hDG : ∀ j, coulombEnergy (A j \ ball 0 (R j)) < ∞ := fun j =>
    coulombEnergy_lt_top _ (hvG j)
  -- the energy splitting `𝓔(E_n) ≥ 𝓔(E) + 𝓔(G_n) + o(1)`
  have hkey : ∀ j, (energy F).toReal + (energy (A j \ ball 0 (R j))).toReal + (ε j + δ j) ≤
      (energy (A j)).toReal := by
    intro j
    rw [energy_toReal_eq hPF hDF, energy_toReal_eq (hPG j) (hDG j),
      energy_toReal_eq (hPA j) (hDA j)]
    linarith [hperS j, hDS j]
  have hlimA : Tendsto (fun j => (energy (A j)).toReal) atTop (𝓝 (valueFunction V).toReal) :=
    ((ENNReal.tendsto_toReal hm.ne).comp (hlim.comp hσ.tendsto_atTop)).congr
      (fun j => by simp only [Function.comp_apply, heA j])
  have hEF : energy F < ∞ := energy_lt_top hPF hDF
  -- lower semicontinuity: `𝓔(E) ≤ m(V)`
  have hEm : energy F ≤ valueFunction V := by
    have hlow : ∀ j, (energy F).toReal ≤ (energy (A j)).toReal - (ε j + δ j) := fun j => by
      have h0 : 0 ≤ (energy (A j \ ball 0 (R j))).toReal := ENNReal.toReal_nonneg
      linarith [hkey j]
    have hlim2 : Tendsto (fun j => (energy (A j)).toReal - (ε j + δ j)) atTop
        (𝓝 ((valueFunction V).toReal - (0 + 0))) := hlimA.sub (hε.add hδ)
    have hreal : (energy F).toReal ≤ (valueFunction V).toReal := by
      simpa only [add_zero, sub_zero] using ge_of_tendsto' hlim2 hlow
    exact (ENNReal.toReal_le_toReal hEF.ne hm.ne).mp hreal
  -- the volume `V₀ = |E| ∈ (0, V]`
  set V0 : ℝ := (volume F).toReal with hV0
  have hV0pos : 0 < V0 := ENNReal.toReal_pos hFpos.ne' hFfin.ne
  have hVF : volume F = ENNReal.ofReal V0 := (ENNReal.ofReal_toReal hFfin.ne).symm
  have hV0le : V0 ≤ V := by
    have hb : ∀ j, (volume (A j ∩ ball 0 (R j))).toReal ≤ V := fun j =>
      ENNReal.toReal_le_of_le_ofReal hV.le ((measure_mono inter_subset_left).trans (hvA j).le)
    exact le_of_tendsto' hvolFn hb
  by_cases hVeq : V0 = V
  · -- Case `V₀ = V`: `E` is a minimiser
    have hvolF : volume F = ENNReal.ofReal V := by rw [hVF, hVeq]
    refine ⟨F, hFmeas, ⟨hFnull, hvolF, hPF, fun G hG hvolG => ?_⟩,
      le_antisymm hEm (valueFunction_le hFnull hvolF)⟩
    exact hEm.trans (valueFunction_le hG hvolG)
  · -- Case `V₀ < V`: contradiction with strict binding
    exfalso
    have hlt : V0 < V := lt_of_le_of_ne hV0le hVeq
    have hVV0 : 0 < V - V0 := sub_pos.mpr hlt
    have hg : ∀ j, (volume (A j \ ball 0 (R j))).toReal =
        V - (volume (A j ∩ ball 0 (R j))).toReal := fun j => by
      have h := congrArg ENNReal.toReal (hvolsplit j)
      rw [ENNReal.toReal_add (hvG j).ne (hvFn j).ne, hvA j, ENNReal.toReal_ofReal hV.le] at h
      linarith
    have hglim : Tendsto (fun j => (volume (A j \ ball 0 (R j))).toReal) atTop
        (𝓝 (V - V0)) :=
      ((tendsto_const_nhds (x := V)).sub hvolFn).congr (fun j => (hg j).symm)
    have hcontAt : ContinuousAt valueFunction (V - V0) :=
      hcont.continuousAt (Ioi_mem_nhds hVV0)
    have hmG : Tendsto (fun j => (valueFunction (volume (A j \ ball 0 (R j))).toReal).toReal)
        atTop (𝓝 (valueFunction (V - V0)).toReal) :=
      (ENNReal.tendsto_toReal (valueFunction_lt_top hVV0).ne).comp
        (hcontAt.tendsto.comp hglim)
    have hmGle : ∀ j, (valueFunction (volume (A j \ ball 0 (R j))).toReal).toReal ≤
        (energy (A j \ ball 0 (R j))).toReal := fun j =>
      ENNReal.toReal_mono (energy_lt_top (hPG j) (hDG j)).ne
        (valueFunction_le ((hmA j).diff measurableSet_ball.nullMeasurableSet)
          (ENNReal.ofReal_toReal (hvG j).ne).symm)
    have hmF0 : (valueFunction V0).toReal ≤ (energy F).toReal :=
      ENNReal.toReal_mono hEF.ne (valueFunction_le hFnull hVF)
    have hineq : ∀ j, (valueFunction V0).toReal +
        (valueFunction (volume (A j \ ball 0 (R j))).toReal).toReal + (ε j + δ j) ≤
          (energy (A j)).toReal := fun j => by
      linarith [hkey j, hmGle j]
    have hlimit : (valueFunction V0).toReal + (valueFunction (V - V0)).toReal + (0 + 0) ≤
        (valueFunction V).toReal :=
      le_of_tendsto_of_tendsto'
        (((tendsto_const_nhds (x := (valueFunction V0).toReal)).add hmG).add (hε.add hδ))
        hlimA hineq
    -- strict binding with `s = V₀ / V`
    have hs : V0 / V ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hV0pos hV, (div_lt_one hV).mpr hlt⟩
    have hb := hbind V hV hVc (V0 / V) hs
    rw [div_mul_cancel₀ V0 hV.ne', sub_mul, one_mul, div_mul_cancel₀ V0 hV.ne'] at hb
    have hne0 := (valueFunction_lt_top hV0pos).ne
    have hne1 := (valueFunction_lt_top hVV0).ne
    have hreal := (ENNReal.toReal_lt_toReal hm.ne (ENNReal.add_ne_top.mpr ⟨hne0, hne1⟩)).mpr hb
    rw [ENNReal.toReal_add hne0 hne1] at hreal
    linarith

/-- Blueprint `prop:existence-subcritical`, modulo `prop:strict-binding`
(`prop:m-continuous` is proved). -/
theorem exists_minimizer_subcritical_of_strict_binding (hbind : StrictBinding)
    {V : ℝ} (hV : 0 < V) (hVc : V < criticalVolume) :
    ∃ Ω : Set AmbientSpace, MeasurableSet Ω ∧ IsLebesgueFixedVolumeMinimizer V Ω ∧
      energy Ω = valueFunction V :=
  exists_minimizer_subcritical_of_m_continuous_of_strict_binding valueFunctionContinuous hbind
    hV hVc

/-- Blueprint `prop:existence-subcritical`, modulo `thm:sharp-isoperimetric`: for
`0 < V < V_*` the infimum `m(V)` is attained. -/
theorem exists_minimizer_subcritical_of_sharp_isoperimetric (hiso : SharpIsoperimetric)
    {V : ℝ} (hV : 0 < V) (hVc : V < criticalVolume) :
    ∃ Ω : Set AmbientSpace, MeasurableSet Ω ∧ IsLebesgueFixedVolumeMinimizer V Ω ∧
      energy Ω = valueFunction V :=
  exists_minimizer_subcritical_of_strict_binding (strictBinding_of_sharpIsoperimetric hiso)
    hV hVc

end LiquidDrop
