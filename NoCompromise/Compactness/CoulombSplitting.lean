import NoCompromise.Energy.Coulomb

/-!
# Coulomb splitting across expanding balls

Blueprint `lem:coulomb-splitting`.
-/

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal symmDiff

namespace LiquidDrop

private theorem tendsto_volume_tail_ball_nat (F : Set AmbientSpace)
    (hmF : NullMeasurableSet F volume) (hF : volume F < ∞) :
    Tendsto (fun k : ℕ => volume (F \ ball 0 (k : ℝ))) atTop (𝓝 0) := by
  have hanti : Antitone (fun k : ℕ => F \ ball 0 (k : ℝ)) := by
    intro i j hij x hx
    exact ⟨hx.1, fun hxi => hx.2 (ball_subset_ball (by exact_mod_cast hij) hxi)⟩
  have hi : (⋂ k : ℕ, F \ ball 0 (k : ℝ)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_gt (dist x (0 : AmbientSpace))
    exact (mem_iInter.mp hx k).2 hk
  have ht := tendsto_measure_iInter_atTop
    (fun k : ℕ => hmF.diff measurableSet_ball.nullMeasurableSet) hanti
    ⟨0, ((measure_mono sdiff_subset).trans_lt hF).ne⟩
  simpa only [Function.comp_def, hi, measure_empty] using ht

private theorem coulombInteraction_mono_left {A B G : Set AmbientSpace} (h : A ⊆ B) :
    coulombInteraction A G ≤ coulombInteraction B G := by
  simp only [coulombInteraction_eq_lintegral_potential]
  exact lintegral_mono_set h

private theorem coulombInteraction_union_le (A B G : Set AmbientSpace) :
    coulombInteraction (A ∪ B) G ≤
      coulombInteraction A G + coulombInteraction B G := by
  simp only [coulombInteraction_eq_lintegral_potential]
  exact lintegral_union_le (coulombPotential G) A B

private theorem coulombInteraction_toReal_le_volume {C : ℝ} (hC : 0 ≤ C)
    (A G : Set AmbientSpace) (hA : volume A < ∞)
    (hG : volume G ≤ ENNReal.ofReal C) :
    (coulombInteraction A G).toReal ≤
      coulombBoundConstant * C ^ ((2 : ℝ) / 3) * volume.real A := by
  have hGfin : volume G < ∞ := hG.trans_lt ENNReal.ofReal_lt_top
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (coulombInteraction_le A G hA hGfin)
  have hnonneg : 0 ≤ coulombBoundConstant * volume.real G ^ ((2 : ℝ) / 3) *
      volume.real A := by
    have : 0 ≤ coulombBoundConstant := by unfold coulombBoundConstant; positivity
    positivity
  rw [ENNReal.toReal_ofReal hnonneg] at h
  have hCG : volume.real G ≤ C := ENNReal.toReal_le_of_le_ofReal hC hG
  have hp : volume.real G ^ ((2 : ℝ) / 3) ≤ C ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow measureReal_nonneg hCG (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hK : 0 ≤ coulombBoundConstant := by unfold coulombBoundConstant; positivity
  have hbound : coulombBoundConstant * volume.real G ^ ((2 : ℝ) / 3) * volume.real A ≤
      coulombBoundConstant * C ^ ((2 : ℝ) / 3) * volume.real A :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hK) measureReal_nonneg
  exact h.trans hbound

private theorem coulombInteraction_toReal_le_separated {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 < d) (A G : Set AmbientSpace)
    (hA : volume A ≤ ENNReal.ofReal C) (hG : volume G ≤ ENNReal.ofReal C)
    (hsep : ∀ x ∈ A, ∀ y ∈ G, d ≤ ‖x - y‖) :
    (coulombInteraction A G).toReal ≤ C * C / d := by
  have h := ENNReal.toReal_mono
    (show volume A * volume G / ENNReal.ofReal d ≠ ∞ by
      refine ENNReal.div_ne_top ?_ ?_
      · exact ENNReal.mul_ne_top
          (hA.trans_lt ENNReal.ofReal_lt_top).ne
          (hG.trans_lt ENNReal.ofReal_lt_top).ne
      · exact ENNReal.ofReal_ne_zero_iff.mpr hd)
    (coulombInteraction_le_of_separated A G hsep)
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le] at h
  have hA' : volume.real A ≤ C := ENNReal.toReal_le_of_le_ofReal hC hA
  have hG' : volume.real G ≤ C := ENNReal.toReal_le_of_le_ofReal hC hG
  calc
    _ ≤ volume.real A * volume.real G / d := h
    _ ≤ C * C / d := by
      gcongr

private theorem separated_ball_compl {M r d : ℝ} (hr : M + d ≤ r)
    {x y : AmbientSpace} (hx : x ∈ ball 0 M) (hy : y ∉ ball 0 r) :
    d ≤ ‖x - y‖ := by
  have hxM : ‖x‖ < M := by simpa using hx
  have hyr : r ≤ ‖y‖ := by simpa [mem_ball] using hy
  have htriangle : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by simp
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
  rw [norm_sub_rev] at htriangle
  linarith

private theorem coulombInteraction_cut_le (A F G : Set AmbientSpace) (M : ℝ) :
    coulombInteraction A G ≤
      coulombInteraction (F ∩ ball 0 M) G +
        coulombInteraction (F \ ball 0 M) G + coulombInteraction (A \ F) G := by
  have hA : A ⊆ F ∪ (A \ F) := by
    intro x hx
    by_cases h : x ∈ F
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have hF := coulombInteraction_union_le (F ∩ ball 0 M) (F \ ball 0 M) G
  rw [Set.inter_union_sdiff] at hF
  calc
    _ ≤ coulombInteraction (F ∪ (A \ F)) G := coulombInteraction_mono_left hA
    _ ≤ coulombInteraction F G + coulombInteraction (A \ F) G :=
      coulombInteraction_union_le F (A \ F) G
    _ ≤ _ := add_le_add hF le_rfl

private theorem coulombInteraction_cut_toReal_le {C : ℝ} (hC : 0 ≤ C)
    (A F G : Set AmbientSpace) (M : ℝ)
    (hA : volume A ≤ ENNReal.ofReal C) (hF : volume F ≤ ENNReal.ofReal C)
    (hG : volume G ≤ ENNReal.ofReal C) :
    (coulombInteraction A G).toReal ≤
      (coulombInteraction (F ∩ ball 0 M) G).toReal +
        coulombBoundConstant * C ^ ((2 : ℝ) / 3) * volume.real (F \ ball 0 M) +
        coulombBoundConstant * C ^ ((2 : ℝ) / 3) * volume.real (A ∆ F) := by
  have hAfin : volume A < ∞ := hA.trans_lt ENNReal.ofReal_lt_top
  have hFfin : volume F < ∞ := hF.trans_lt ENNReal.ofReal_lt_top
  have hGfin : volume G < ∞ := hG.trans_lt ENNReal.ofReal_lt_top
  have hinner : volume (F ∩ ball 0 M) < ∞ :=
    (measure_mono inter_subset_left).trans_lt hFfin
  have htail : volume (F \ ball 0 M) < ∞ :=
    (measure_mono sdiff_subset).trans_lt hFfin
  have hdiff : volume (A \ F) < ∞ :=
    (measure_mono sdiff_subset).trans_lt hAfin
  have hsymm : volume (A ∆ F) < ∞ :=
    (measure_mono symmDiff_subset_union).trans_lt
      ((measure_union_le A F).trans_lt (ENNReal.add_lt_top.mpr ⟨hAfin, hFfin⟩))
  have hdiffsymm : volume.real (A \ F) ≤ volume.real (A ∆ F) :=
    ENNReal.toReal_mono hsymm.ne (measure_mono
      (show A \ F ⊆ A ∆ F from fun x hx => Or.inl hx))
  have h1 : coulombInteraction (F ∩ ball 0 M) G ≠ ∞ :=
    (coulombInteraction_lt_top _ _ hinner hGfin).ne
  have h2 : coulombInteraction (F \ ball 0 M) G ≠ ∞ :=
    (coulombInteraction_lt_top _ _ htail hGfin).ne
  have h3 : coulombInteraction (A \ F) G ≠ ∞ :=
    (coulombInteraction_lt_top _ _ hdiff hGfin).ne
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨h1, h2⟩, h3⟩)
    (coulombInteraction_cut_le A F G M)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) h3,
    ENNReal.toReal_add h1 h2] at h
  have ht := coulombInteraction_toReal_le_volume hC (F \ ball 0 M) G htail hG
  have hd := coulombInteraction_toReal_le_volume hC (A \ F) G hdiff hG
  have hK : 0 ≤ coulombBoundConstant * C ^ ((2 : ℝ) / 3) := by
    have : 0 ≤ coulombBoundConstant := by unfold coulombBoundConstant; positivity
    positivity
  calc
    _ ≤ (coulombInteraction (F ∩ ball 0 M) G).toReal +
        (coulombInteraction (F \ ball 0 M) G).toReal +
        (coulombInteraction (A \ F) G).toReal := h
    _ ≤ _ := by
      have hd' := hd.trans (mul_le_mul_of_nonneg_left hdiffsymm hK)
      exact add_le_add (add_le_add le_rfl ht) hd'

/-- Blueprint `lem:coulomb-splitting`: `I(F_n, G_n) → 0`. -/
theorem tendsto_coulombInteraction_cut {C : ℝ} (hC : 0 ≤ C)
    (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (_hmE : ∀ n, NullMeasurableSet (E n) volume) (hmF : NullMeasurableSet F volume)
    (hvol : ∀ n, volume (E n) ≤ ENNReal.ofReal C) (hFvol : volume F ≤ ENNReal.ofReal C)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hconv : Tendsto (fun n => volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop (𝓝 0)) :
    Tendsto (fun n => (coulombInteraction (E n ∩ ball 0 (R n))
      (E n \ ball 0 (R n))).toReal) atTop (𝓝 0) := by
  have hFfin : volume F < ∞ := hFvol.trans_lt ENNReal.ofReal_lt_top
  have htail : Tendsto (fun k : ℕ => volume.real (F \ ball 0 (k : ℝ))) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_volume_tail_ball_nat F hmF hFfin)
  have hconvReal : Tendsto
      (fun n => volume.real ((E n ∩ ball 0 (R n)) ∆ F)) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  let K : ℝ := coulombBoundConstant * C ^ ((2 : ℝ) / 3)
  have htailK : Tendsto (fun k : ℕ => K * volume.real (F \ ball 0 (k : ℝ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using htail.const_mul K
  have hconvK : Tendsto (fun n => K * volume.real ((E n ∩ ball 0 (R n)) ∆ F))
      atTop (𝓝 0) := by simpa only [mul_zero] using hconvReal.const_mul K
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha ENNReal.toReal_nonneg
  · intro b hb
    obtain ⟨M, hM⟩ := ((tendsto_order.1 htailK).2 (b / 3) (by linarith)).exists
    obtain ⟨k, hk⟩ := exists_nat_gt (3 * C * C / b)
    have hk0 : 0 < (k : ℝ) := by
      have hnonneg : 0 ≤ 3 * C * C / b := by positivity
      have hk' : 3 * C * C / b < (k : ℝ) := by exact_mod_cast hk
      linarith
    have hsepbound : C * C / (k : ℝ) < b / 3 := by
      have hk' : 3 * C * C / b < (k : ℝ) := by exact_mod_cast hk
      have hmul : 3 * C * C < b * (k : ℝ) := by
        have h := (div_lt_iff₀ hb).mp hk'
        nlinarith
      apply (div_lt_iff₀ hk0).mpr
      nlinarith
    filter_upwards [hR.eventually_ge_atTop ((M : ℝ) + (k : ℝ)),
      (tendsto_order.1 hconvK).2 (b / 3) (by linarith)] with n hn hdiff
    have hinner : (coulombInteraction (F ∩ ball 0 (M : ℝ))
        (E n \ ball 0 (R n))).toReal ≤ C * C / (k : ℝ) := by
      apply coulombInteraction_toReal_le_separated hC hk0
        (F ∩ ball 0 (M : ℝ)) (E n \ ball 0 (R n))
        ((measure_mono inter_subset_left).trans hFvol)
        ((measure_mono sdiff_subset).trans (hvol n))
      intro x hx y hy
      exact separated_ball_compl hn hx.2 hy.2
    have hcut := coulombInteraction_cut_toReal_le hC
      (E n ∩ ball 0 (R n)) F (E n \ ball 0 (R n)) (M : ℝ)
      ((measure_mono inter_subset_left).trans (hvol n)) hFvol
      ((measure_mono sdiff_subset).trans (hvol n))
    change (coulombInteraction (E n ∩ ball 0 (R n))
      (E n \ ball 0 (R n))).toReal < b
    change K * volume.real ((E n ∩ ball 0 (R n)) ∆ F) < b / 3 at hdiff
    change K * volume.real (F \ ball 0 (M : ℝ)) < b / 3 at hM
    dsimp only [K] at hdiff hM
    linarith

/-- Blueprint `lem:coulomb-splitting`: `D(F_n) → D(E)`. -/
theorem tendsto_coulombEnergy_cut {C : ℝ} (hC : 0 ≤ C)
    (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (hmE : ∀ n, NullMeasurableSet (E n) volume) (hmF : NullMeasurableSet F volume)
    (hvol : ∀ n, volume (E n) ≤ ENNReal.ofReal C) (hFvol : volume F ≤ ENNReal.ofReal C)
    (R : ℕ → ℝ)
    (hconv : Tendsto (fun n => volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop (𝓝 0)) :
    Tendsto (fun n => (coulombEnergy (E n ∩ ball 0 (R n))).toReal) atTop
      (𝓝 (coulombEnergy F).toReal) := by
  apply tendsto_coulombEnergy_of_symmDiff
    (fun n => (hmE n).inter measurableSet_ball.nullMeasurableSet) hmF hC
    (fun n => (measure_mono inter_subset_left).trans (hvol n)) hFvol
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv

/-- Blueprint `lem:coulomb-splitting`: `D(E_n) = D(E) + D(G_n) + o(1)`. -/
theorem coulomb_splitting {C : ℝ} (hC : 0 ≤ C)
    (E : ℕ → Set AmbientSpace) (F : Set AmbientSpace)
    (hmE : ∀ n, NullMeasurableSet (E n) volume) (hmF : NullMeasurableSet F volume)
    (hvol : ∀ n, volume (E n) ≤ ENNReal.ofReal C) (hFvol : volume F ≤ ENNReal.ofReal C)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hconv : Tendsto (fun n => volume (symmDiff (E n ∩ ball 0 (R n)) F)) atTop (𝓝 0)) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ n,
      (coulombEnergy (E n)).toReal =
        (coulombEnergy F).toReal + (coulombEnergy (E n \ ball 0 (R n))).toReal + δ n := by
  let δ n := (coulombEnergy (E n ∩ ball 0 (R n))).toReal -
      (coulombEnergy F).toReal +
      (coulombInteraction (E n ∩ ball 0 (R n)) (E n \ ball 0 (R n))).toReal
  refine ⟨δ, ?_, ?_⟩
  · have henergy := tendsto_coulombEnergy_cut hC E F hmE hmF hvol hFvol R hconv
    have hinteraction := tendsto_coulombInteraction_cut hC E F hmE hmF hvol hFvol R hR hconv
    have hδ := (henergy.sub
      (tendsto_const_nhds (x := (coulombEnergy F).toReal))).add hinteraction
    simpa only [sub_self, zero_add] using hδ
  · intro n
    have hdisj : Disjoint (E n ∩ ball 0 (R n)) (E n \ ball 0 (R n)) := by
      apply disjoint_left.mpr
      intro x hx hy
      exact hy.2 hx.2
    have hcut := coulombEnergy_toReal_union (E n ∩ ball 0 (R n))
      (E n \ ball 0 (R n))
      ((hmE n).diff measurableSet_ball.nullMeasurableSet) hdisj
      ((measure_mono inter_subset_left).trans_lt
        ((hvol n).trans_lt ENNReal.ofReal_lt_top))
      ((measure_mono sdiff_subset).trans_lt
        ((hvol n).trans_lt ENNReal.ofReal_lt_top))
    rw [Set.inter_union_sdiff] at hcut
    dsimp [δ]
    linarith

end LiquidDrop
