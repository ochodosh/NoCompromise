import NoCompromise.Binding.Ratio
import NoCompromise.Existence.Subcritical

/-!
# Attainment of the relaxed ratio infimum (blueprint chapter 38)

Blueprint `lem:relaxed-attained`: for every `A > 0` the relaxed ratio infimum
`e_≤(A) = inf {𝓔(E)/|E| : 0 < |E| ≤ A}` (`relaxedEnergyRatio A`) is attained.

The proof follows the blueprint: a minimising sequence has volumes bounded below
(the isoperimetric inequality, `SharpIsoperimetric`) and above (by `A`) and bounded
perimeters, so `thm:compactness` (`compactness_of_volume_perimeter_bounds`) and
`thm:decomposition` (`decomposition`) apply after translations. The remainder `G_n`
satisfies `𝓔(G_n) ≥ e |G_n|` by the definition of `e`, and the energy splitting gives
`𝓔(E) ≤ e |E|` for the limit `E`, whose volume lies in `(0, A]`. The volumes of the
minimising sequence are not assumed to converge.

Blueprint `lem:stabilization` then follows from `stabilization_of_attained`.
The only hypothesis is `SharpIsoperimetric` (`thm:sharp-isoperimetric`).
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace LiquidDrop

/-- The isoperimetric lower volume bound for sets of bounded energy-to-volume ratio:
if `𝓔(E) ≤ M |E|` with `M > 0`, then `|E| ≥ ((36π)^{1/3} / M)^3`. -/
theorem volume_ge_of_energy_le_mul_volume (hiso : SharpIsoperimetric) {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (hpos : 0 < volume E) (hfin : volume E < ∞)
    {M : ℝ} (hM : 0 < M)
    (hratio : energy E ≤ ENNReal.ofReal M * volume E) :
    ENNReal.ofReal (((36 * Real.pi) ^ (1 / (3 : ℝ)) / M) ^ 3) ≤ volume E := by
  set k : ℝ := (36 * Real.pi) ^ (1 / (3 : ℝ)) with hk
  set v : ℝ := (volume E).toReal with hv
  have hk0 : 0 ≤ k := Real.rpow_nonneg (by positivity) _
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hvE : volume E = ENNReal.ofReal v := (ENNReal.ofReal_toReal hfin.ne).symm
  have h1 : ENNReal.ofReal (k * v ^ (2 / (3 : ℝ))) ≤ ENNReal.ofReal (M * v) := by
    calc ENNReal.ofReal (k * v ^ (2 / (3 : ℝ))) ≤ perimeter E := hiso E hE hfin
      _ ≤ energy E := le_self_add
      _ ≤ ENNReal.ofReal M * volume E := hratio
      _ = ENNReal.ofReal (M * v) := by rw [hvE, ENNReal.ofReal_mul hM.le]
  have h2 : k * v ^ (2 / (3 : ℝ)) ≤ M * v :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM.le hv0)).mp h1
  set t : ℝ := v ^ (1 / (3 : ℝ)) with ht
  have hvt : v = t ^ 3 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hv0]
    norm_num
  have hvt2 : v ^ (2 / (3 : ℝ)) = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hv0]
    norm_num
  rw [hvt2] at h2
  have htpos : 0 < t := Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos.ne' hfin.ne) _
  have h3 : k ≤ M * t := by
    have h4 : k * t ^ 2 ≤ (M * t) * t ^ 2 := by
      calc k * t ^ 2 ≤ M * v := h2
        _ = (M * t) * t ^ 2 := by rw [hvt]; ring
    exact le_of_mul_le_mul_right h4 (by positivity)
  have h5 : k / M ≤ t := (div_le_iff₀ hM).mpr (by linarith)
  rw [hvE]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hvt]
  exact pow_le_pow_left₀ (div_nonneg hk0 hM.le) h5 3

/-- Finite perimeter and finite Coulomb energy give finite energy. -/
theorem energy_lt_top_of_perimeter_coulomb {X : Set AmbientSpace} (hP : perimeter X < ∞)
    (hD : coulombEnergy X < ∞) : energy X < ∞ := by
  rw [energy]
  exact ENNReal.add_lt_top.mpr ⟨hP, hD⟩

/-- The real energy is the sum of the real perimeter and the real Coulomb energy. -/
theorem energy_toReal_eq_add {X : Set AmbientSpace} (hP : perimeter X < ∞)
    (hD : coulombEnergy X < ∞) :
    (energy X).toReal = (perimeter X).toReal + (coulombEnergy X).toReal := by
  rw [energy]
  exact ENNReal.toReal_add hP.ne hD.ne

/-- The definition of `e_≤(A)` in multiplicative form: `e_≤(A) |G| ≤ 𝓔(G)` for every
competitor with `|G| ≤ A`, including `|G| = 0`. -/
theorem relaxedEnergyRatio_mul_volume_le {A : ℝ} {G : Set AmbientSpace}
    (hG : NullMeasurableSet G volume) (hvol : volume G ≤ ENNReal.ofReal A) :
    relaxedEnergyRatio A * volume G ≤ energy G := by
  rcases eq_zero_or_pos (volume G) with h0 | hpos
  · rw [h0, mul_zero]
    exact zero_le
  · have hfin : volume G ≠ ∞ := (hvol.trans_lt ENNReal.ofReal_lt_top).ne
    have h := relaxedEnergyRatio_le hG hpos hvol
    calc relaxedEnergyRatio A * volume G ≤ energy G / volume G * volume G :=
          mul_le_mul_left h _
      _ = energy G := ENNReal.div_mul_cancel hpos.ne' hfin

/-- A minimising sequence for `e_≤(A)`, in real form: `𝓔(E_n) ≤ (e + 1/(n+1)) |E_n|`. -/
theorem exists_relaxed_minimizing_seq {A : ℝ} (hA : 0 < A) :
    ∃ E : ℕ → Set AmbientSpace, (∀ n, NullMeasurableSet (E n) volume) ∧
      (∀ n, 0 < volume (E n)) ∧ (∀ n, volume (E n) ≤ ENNReal.ofReal A) ∧
      (∀ n, energy (E n) < ∞) ∧
      ∀ n, (energy (E n)).toReal ≤
        ((relaxedEnergyRatio A).toReal + 1 / ((n : ℝ) + 1)) * (volume (E n)).toReal := by
  have he : relaxedEnergyRatio A < ∞ := relaxedEnergyRatio_lt_top hA
  have hseq : ∀ n : ℕ, ∃ E : Set AmbientSpace, NullMeasurableSet E volume ∧
      0 < volume E ∧ volume E ≤ ENNReal.ofReal A ∧
      energy E / volume E < relaxedEnergyRatio A + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : 0 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := ENNReal.ofReal_pos.mpr (by positivity)
    have hlt : relaxedEnergyRatio A <
        relaxedEnergyRatio A + ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ENNReal.lt_add_right he.ne hpos.ne'
    obtain ⟨E, hE⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hmE, hE⟩ := iInf_lt_iff.mp hE
    obtain ⟨hpE, hE⟩ := iInf_lt_iff.mp hE
    obtain ⟨hvE, hE⟩ := iInf_lt_iff.mp hE
    exact ⟨E, hmE, hpE, hvE, hE⟩
  choose E hmE hpE hvE hEn using hseq
  have hfin : ∀ n, volume (E n) < ∞ := fun n => (hvE n).trans_lt ENNReal.ofReal_lt_top
  have hb : ∀ n, relaxedEnergyRatio A + ENNReal.ofReal (1 / ((n : ℝ) + 1)) < ∞ := fun n =>
    ENNReal.add_lt_top.mpr ⟨he, ENNReal.ofReal_lt_top⟩
  have hle : ∀ n, energy (E n) ≤
      (relaxedEnergyRatio A + ENNReal.ofReal (1 / ((n : ℝ) + 1))) * volume (E n) := fun n => by
    calc energy (E n) = energy (E n) / volume (E n) * volume (E n) :=
          (ENNReal.div_mul_cancel (hpE n).ne' (hfin n).ne).symm
      _ ≤ _ := mul_le_mul_left (hEn n).le _
  have hEfin : ∀ n, energy (E n) < ∞ := fun n =>
    (hle n).trans_lt (ENNReal.mul_lt_top (hb n) (hfin n))
  refine ⟨E, hmE, hpE, hvE, hEfin, fun n => ?_⟩
  have h := ENNReal.toReal_mono (ENNReal.mul_lt_top (hb n) (hfin n)).ne (hle n)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_add he.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)] at h

/-- Blueprint `lem:relaxed-attained`: for every `A > 0` the relaxed ratio infimum
`e_≤(A) = inf {𝓔(E)/|E| : 0 < |E| ≤ A}` is attained, modulo `thm:sharp-isoperimetric`. -/
theorem relaxed_attained (hiso : SharpIsoperimetric) {A : ℝ} (hA : 0 < A) :
    ∃ E : Set AmbientSpace, IsRelaxedRatioMinimizer A E := by
  have he : relaxedEnergyRatio A < ∞ := relaxedEnergyRatio_lt_top hA
  set e : ℝ := (relaxedEnergyRatio A).toReal with he_def
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  obtain ⟨E, hmE, hpE, hvE, hEfin, hEle⟩ := exists_relaxed_minimizing_seq hA
  have hfin : ∀ n, volume (E n) < ∞ := fun n => (hvE n).trans_lt ENNReal.ofReal_lt_top
  have hvr : ∀ n, (volume (E n)).toReal ≤ A := fun n =>
    ENNReal.toReal_le_of_le_ofReal hA.le (hvE n)
  -- the uniform ratio bound `𝓔(E_n) ≤ (e + 1) |E_n|`
  have hinv : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hE1 : ∀ n, (energy (E n)).toReal ≤ (e + 1) * (volume (E n)).toReal := fun n =>
    (hEle n).trans (mul_le_mul_of_nonneg_right (by linarith [hinv n]) ENNReal.toReal_nonneg)
  have hE1' : ∀ n, energy (E n) ≤ ENNReal.ofReal (e + 1) * volume (E n) := fun n => by
    rw [← ENNReal.ofReal_toReal (hEfin n).ne, ← ENNReal.ofReal_toReal (hfin n).ne,
      ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal (hE1 n)
  -- the lower volume bound from the isoperimetric inequality
  set c : ℝ := ((36 * Real.pi) ^ (1 / (3 : ℝ)) / (e + 1)) ^ 3 with hc
  have hcpos : 0 < c := by
    have : 0 < (36 * Real.pi) ^ (1 / (3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    have : 0 < e + 1 := by linarith
    positivity
  have hlow : ∀ n, ENNReal.ofReal c ≤ volume (E n) := fun n =>
    volume_ge_of_energy_le_mul_volume hiso (hmE n) (hpE n) (hfin n) (by linarith) (hE1' n)
  -- uniform volume, energy and perimeter bounds
  set C0 : ℝ := (e + 1) * A + A with hC0
  have hC0pos : 0 < C0 := by
    have : 0 ≤ (e + 1) * A := mul_nonneg (by linarith) hA.le
    linarith
  have hAC0 : ENNReal.ofReal A ≤ ENNReal.ofReal C0 := by
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ (e + 1) * A := mul_nonneg (by linarith) hA.le
    linarith
  have henergy_le : ∀ n, energy (E n) ≤ ENNReal.ofReal C0 := fun n => by
    rw [← ENNReal.ofReal_toReal (hEfin n).ne]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hE1 n
    have h2 : (e + 1) * (volume (E n)).toReal ≤ (e + 1) * A :=
      mul_le_mul_of_nonneg_left (hvr n) (by linarith)
    linarith
  have hper_le : ∀ n, perimeter (E n) ≤ ENNReal.ofReal C0 := fun n =>
    (le_self_add : perimeter (E n) ≤ perimeter (E n) + coulombEnergy (E n)).trans
      (henergy_le n)
  have hfinP : ∀ n, HasFinitePerimeter (E n) := fun n => by
    change perimeterN (E n) < ∞
    rw [perimeterN_eq_perimeter _ (hmE n)]
    exact (hper_le n).trans_lt ENNReal.ofReal_lt_top
  -- compactness (`thm:compactness`)
  obtain ⟨σ, hσ, w, F, hFmeas, -, hFfp, hFpos, hFle, hconv, -, -⟩ :=
    compactness_of_volume_perimeter_bounds hcpos hC0pos E hmE hfinP hlow
      (fun n => (hvE n).trans hAC0) hper_le
  set B : ℕ → Set AmbientSpace := fun j => (fun y => w j + y) '' E (σ j) with hB
  have hmB : ∀ j, NullMeasurableSet (B j) volume := fun j =>
    nullMeasurableSet_image_of_differentiable (by fun_prop) (fun _ _ h => add_left_cancel h)
      (hmE (σ j))
  have hvB : ∀ j, volume (B j) = volume (E (σ j)) := fun j => volume_image_translate _ _
  have hpB : ∀ j, perimeter (B j) = perimeter (E (σ j)) := fun j =>
    perimeter_image_translate (hmE _) _
  have heB : ∀ j, energy (B j) = energy (E (σ j)) := fun j => energy_translate (hmE _) _
  have hPB : ∀ j, perimeter (B j) < ∞ := fun j => by
    rw [hpB]
    exact (hper_le _).trans_lt ENNReal.ofReal_lt_top
  have hlfpB : ∀ j, HasLocallyFinitePerimeter (B j) := fun j =>
    hasLocallyFinitePerimeter_of_perimeter_lt_top (hmB j) (hPB j)
  have hvBA : ∀ j, volume (B j) ≤ ENNReal.ofReal A := fun j => by
    rw [hvB]
    exact hvE _
  -- decomposition (`thm:decomposition`)
  obtain ⟨R, -, hgood, -, -, hvolFn, hvolsplit, ⟨ε, hε, hperS⟩, ⟨δ, hδ, hDS⟩⟩ :=
    decomposition B F hlfpB hmB hFmeas.nullMeasurableSet
      (fun j => (hvBA j).trans hAC0) hFle (fun j => (hpB j).le.trans (hper_le _)) hconv
  have hFnull : NullMeasurableSet F volume := hFmeas.nullMeasurableSet
  have hFfin : volume F < ∞ := hFle.trans_lt ENNReal.ofReal_lt_top
  have hPF : perimeter F < ∞ := by
    rw [← perimeterN_eq_perimeter F hFnull]
    exact hFfp
  have hDF : coulombEnergy F < ∞ := coulombEnergy_lt_top F hFfin
  have hvBfin : ∀ j, volume (B j) < ∞ := fun j => (hvBA j).trans_lt ENNReal.ofReal_lt_top
  have hDB : ∀ j, coulombEnergy (B j) < ∞ := fun j => coulombEnergy_lt_top _ (hvBfin j)
  have hvG : ∀ j, volume (B j \ ball 0 (R j)) < ∞ := fun j =>
    (measure_mono sdiff_subset).trans_lt (hvBfin j)
  have hvFn : ∀ j, volume (B j ∩ ball 0 (R j)) < ∞ := fun j =>
    (measure_mono inter_subset_left).trans_lt (hvBfin j)
  have hPG : ∀ j, perimeter (B j \ ball 0 (R j)) < ∞ := fun j =>
    perimeter_sdiff_ball_lt_top (hlfpB j) (hmB j) (hgood j) (hPB j)
  have hDG : ∀ j, coulombEnergy (B j \ ball 0 (R j)) < ∞ := fun j =>
    coulombEnergy_lt_top _ (hvG j)
  -- the energy splitting `𝓔(E_n) ≥ 𝓔(E) + 𝓔(G_n) + o(1)`
  have hkey : ∀ j, (energy F).toReal + (energy (B j \ ball 0 (R j))).toReal + (ε j + δ j) ≤
      (energy (B j)).toReal := by
    intro j
    rw [energy_toReal_eq_add hPF hDF, energy_toReal_eq_add (hPG j) (hDG j),
      energy_toReal_eq_add (hPB j) (hDB j)]
    linarith [hperS j, hDS j]
  -- the remainder: `e |G_n| ≤ 𝓔(G_n)`, by the definition of `e`
  have hGe : ∀ j, e * (volume (B j \ ball 0 (R j))).toReal ≤
      (energy (B j \ ball 0 (R j))).toReal := fun j => by
    have h := relaxedEnergyRatio_mul_volume_le (G := B j \ ball 0 (R j))
      ((hmB j).diff measurableSet_ball.nullMeasurableSet)
      ((measure_mono sdiff_subset).trans (hvBA j))
    have h' := ENNReal.toReal_mono
      (energy_lt_top_of_perimeter_coulomb (hPG j) (hDG j)).ne h
    rwa [ENNReal.toReal_mul] at h'
  -- the volume splitting `|E_n| = |G_n| + |F_n|`
  have hsplit : ∀ j, (volume (B j)).toReal =
      (volume (B j \ ball 0 (R j))).toReal + (volume (B j ∩ ball 0 (R j))).toReal := fun j => by
    rw [← hvolsplit j, ENNReal.toReal_add (hvG j).ne (hvFn j).ne]
  -- the minimising property along the subsequence
  have hBle : ∀ j, (energy (B j)).toReal ≤
      (e + 1 / ((σ j : ℝ) + 1)) * (volume (B j)).toReal := fun j => by
    rw [heB, hvB]
    exact hEle (σ j)
  -- combination: `𝓔(E) ≤ e |F_n| + A/(σ j + 1) - (ε_j + δ_j)`
  have hbound : ∀ j, (energy F).toReal ≤
      e * (volume (B j ∩ ball 0 (R j))).toReal + A * (1 / ((σ j : ℝ) + 1)) - (ε j + δ j) := by
    intro j
    have h1 := hkey j
    have h2 := hGe j
    have h3 := hBle j
    have h4 := hsplit j
    have h5 : (volume (B j)).toReal ≤ A := by
      rw [hvB]
      exact hvr _
    have h6 : 0 ≤ 1 / ((σ j : ℝ) + 1) := by positivity
    have h7 : 1 / ((σ j : ℝ) + 1) * (volume (B j)).toReal ≤ A * (1 / ((σ j : ℝ) + 1)) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h5 h6
    have h8 : (e + 1 / ((σ j : ℝ) + 1)) * (volume (B j)).toReal =
        e * (volume (B j \ ball 0 (R j))).toReal + e * (volume (B j ∩ ball 0 (R j))).toReal +
          1 / ((σ j : ℝ) + 1) * (volume (B j)).toReal := by
      rw [h4]
      ring
    linarith
  set V0 : ℝ := (volume F).toReal with hV0
  have hinv0 : Tendsto (fun j => 1 / ((σ j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop
  have hlim : Tendsto (fun j => e * (volume (B j ∩ ball 0 (R j))).toReal +
      A * (1 / ((σ j : ℝ) + 1)) - (ε j + δ j)) atTop (𝓝 (e * V0 + A * 0 - (0 + 0))) :=
    ((hvolFn.const_mul e).add (hinv0.const_mul A)).sub (hε.add hδ)
  have hEF : (energy F).toReal ≤ e * V0 := by
    have h := ge_of_tendsto' hlim hbound
    simpa using h
  -- `0 < |E| ≤ A`
  have hV0A : V0 ≤ A := le_of_tendsto' hvolFn fun j =>
    ENNReal.toReal_le_of_le_ofReal hA.le ((measure_mono inter_subset_left).trans (hvBA j))
  have hFA : volume F ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal hFfin.ne]
    exact ENNReal.ofReal_le_ofReal hV0A
  have hEFfin : energy F < ∞ := energy_lt_top_of_perimeter_coulomb hPF hDF
  have hle : energy F ≤ relaxedEnergyRatio A * volume F := by
    rw [← ENNReal.ofReal_toReal hEFfin.ne, ← ENNReal.ofReal_toReal he.ne,
      ← ENNReal.ofReal_toReal hFfin.ne, ← ENNReal.ofReal_mul he0]
    exact ENNReal.ofReal_le_ofReal hEF
  refine ⟨F, hFnull, hFpos, hFA, le_antisymm ?_ (relaxedEnergyRatio_le hFnull hFpos hFA)⟩
  exact ENNReal.div_le_of_le_mul hle

/-- Blueprint `lem:stabilization`, modulo `thm:sharp-isoperimetric`: `e_≤` is
nonincreasing, constant equal to `e_≤(8)` for `A ≥ 8`, the global ratio infimum equals
`e_≤(8)`, and it is attained. -/
theorem stabilization (hiso : SharpIsoperimetric) :
    Antitone relaxedEnergyRatio ∧
      (∀ A : ℝ, 8 ≤ A → relaxedEnergyRatio A = relaxedEnergyRatio 8) ∧
      globalEnergyRatio = relaxedEnergyRatio 8 ∧
      ∃ E : Set AmbientSpace, IsGlobalRatioOptimizer E :=
  stabilization_of_attained fun _ hA => relaxed_attained hiso hA

end LiquidDrop

#print axioms LiquidDrop.relaxed_attained
#print axioms LiquidDrop.stabilization
