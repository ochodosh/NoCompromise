import NoCompromise.Stationary.MinimizerContext
import NoCompromise.Energy.Scaling

/-!
# Connectedness of the minimizer

Blueprint `prop:connected`. A separation of the open minimizer into two relatively
open pieces has disjoint closures, because at a common boundary point the one-sided
`C¹` graph chart gives a connected local piece of the domain. The two pieces are then
at positive distance, so their perimeters add; translating one piece far away keeps
volume, perimeter and self-energies and strictly lowers the positive cross-interaction.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace LiquidDrop

/-- A bounded set whose closure is disjoint from the closure of another set is at
positive distance from it. -/
lemma areSeparated_of_disjoint_closure {s t : Set AmbientSpace}
    (hs : Bornology.IsBounded s) (hst : Disjoint (closure s) (closure t)) :
    AreSeparated s t := by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_lt_edist hs.isCompact_closure isClosed_closure hst
  refine ⟨r, by exact_mod_cast hr.ne', fun x hx y hy => ?_⟩
  exact (h x (subset_closure hx) y (subset_closure hy)).le

/-- Near a boundary point, a set with a one-sided `C¹` graph chart cannot be split by two
disjoint open sets both accumulating at that point. -/
lemma not_mem_closure_inter_of_hasC1Boundary {Ω A B : Set AmbientSpace}
    (hC : HasC1Boundary Ω) (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (hΩ : Ω = A ∪ B) {x : AmbientSpace} (hxA : x ∈ closure A) (hxB : x ∈ closure B) :
    False := by
  have hΩo : IsOpen Ω := hΩ ▸ hAo.union hBo
  -- `x` is not in `Ω`.
  have hxnA : x ∉ A := by
    intro hx
    obtain ⟨z, hzA, hzB⟩ := mem_closure_iff.mp hxB A hAo hx
    exact Set.disjoint_left.mp hAB hzA hzB
  have hxnB : x ∉ B := by
    intro hx
    obtain ⟨z, hzB, hzA⟩ := mem_closure_iff.mp hxA B hBo hx
    exact Set.disjoint_left.mp hAB hzA hzB
  have hxΩ : x ∉ Ω := by rw [hΩ]; rintro (h | h); exacts [hxnA h, hxnB h]
  have hxcl : x ∈ closure Ω := closure_mono (hΩ ▸ subset_union_left) hxA
  have hxfr : x ∈ frontier Ω := by rw [hΩo.frontier_eq]; exact ⟨hxcl, hxΩ⟩
  obtain ⟨c, hc, hxc⟩ := hC x hxfr
  have hf : Continuous c.height := c.height_contDiff.continuous
  let G : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ AmbientSpace :=
    (smoothGraphCoordinates hf).trans c.placement.toHomeomorph
  have hGapp : ∀ q, c.placement.symm (G q) = smoothGraphCoordinates hf q := by
    intro q
    change c.placement.symm (c.placement (smoothGraphCoordinates hf q)) = _
    simp
  have hO : IsOpen (G ⁻¹' c.region) := c.isOpen_region.preimage G.continuous
  -- Inside the chart preimage, membership in `Ω` is the sign of the vertical coordinate.
  have hmem : ∀ q ∈ G ⁻¹' c.region, (G q ∈ Ω ↔ q.2 < 0) := by
    intro q hq
    rw [hc (G q) hq, hGapp]
    change q ∈ smoothGraphCoordinates hf ⁻¹' smoothSubgraph c.height ↔ _
    rw [smoothGraphCoordinates_preimage_subgraph]
    simp
  set q0 := G.symm x with hq0
  have hq0O : q0 ∈ G ⁻¹' c.region := by
    change G (G.symm x) ∈ c.region
    simpa using hxc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO q0 hq0O
  let T : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := ball q0 ε ∩ {q | q.2 < 0}
  have hTconv : Convex ℝ T := by
    refine (convex_ball q0 ε).inter ?_
    exact (convex_Iio (0 : ℝ)).linear_preimage (LinearMap.snd ℝ _ ℝ)
  have hTpre : IsPreconnected T := hTconv.isPreconnected
  have hTsub : T ⊆ G ⁻¹' A ∪ G ⁻¹' B := by
    rintro q ⟨hq, hq2⟩
    have h1 : G q ∈ Ω := (hmem q (hball hq)).mpr hq2
    rw [hΩ] at h1
    exact h1
  have hnbhd : IsOpen (G.symm ⁻¹' ball q0 ε) := isOpen_ball.preimage G.symm.continuous
  have hxnbhd : x ∈ G.symm ⁻¹' ball q0 ε := by
    change G.symm x ∈ ball q0 ε
    rw [← hq0]
    exact mem_ball_self hε
  have hne : ∀ D : Set AmbientSpace, D ⊆ Ω → x ∈ closure D → (T ∩ G ⁻¹' D).Nonempty := by
    intro D hDΩ hxD
    obtain ⟨z, hzball, hzD⟩ := mem_closure_iff.mp hxD _ hnbhd hxnbhd
    refine ⟨G.symm z, ⟨hzball, ?_⟩, by simpa using hzD⟩
    have hzO : G.symm z ∈ G ⁻¹' c.region := hball hzball
    have := (hmem (G.symm z) hzO).mp (by simpa using hDΩ hzD)
    exact this
  obtain ⟨q, _, hqA, hqB⟩ := hTpre _ _ (hAo.preimage G.continuous) (hBo.preimage G.continuous)
    hTsub (hne A (hΩ ▸ subset_union_left) hxA) (hne B (hΩ ▸ subset_union_right) hxB)
  exact Set.disjoint_left.mp hAB hqA hqB

namespace MinimizerRep

variable {V : ℝ} {Ω : Set AmbientSpace}

/-- Blueprint `prop:connected`: the minimizer representative is connected. -/
theorem isConnected (h : MinimizerRep V Ω) : IsConnected Ω := by
  have hvolpos : 0 < volume Ω := by
    rw [h.volume_eq]; exact ENNReal.ofReal_pos.mpr h.volume_pos
  refine ⟨nonempty_of_measure_ne_zero hvolpos.ne', ?_⟩
  intro u v hu hv hsub hΩu hΩv
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  set A := Ω ∩ u with hAdef
  set B := Ω ∩ v with hBdef
  have hAo : IsOpen A := h.isOpen.inter hu
  have hBo : IsOpen B := h.isOpen.inter hv
  have hAB : Disjoint A B := by
    rw [Set.disjoint_iff_inter_eq_empty, ← hempty]
    ext z; simp only [hAdef, hBdef, mem_inter_iff]; tauto
  have hΩAB : Ω = A ∪ B := by
    ext z
    simp only [hAdef, hBdef, mem_union, mem_inter_iff]
    constructor
    · intro hz
      rcases hsub hz with h' | h'
      exacts [Or.inl ⟨hz, h'⟩, Or.inr ⟨hz, h'⟩]
    · rintro (h' | h'); exacts [h'.1, h'.1]
  -- Disjoint closures, hence positive separation.
  have hcl : Disjoint (closure A) (closure B) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact not_mem_closure_inter_of_hasC1Boundary h.c1Boundary hAo hBo hAB hΩAB hxA hxB
  have hAbdd : Bornology.IsBounded A := h.bounded.subset inter_subset_left
  have hBbdd : Bornology.IsBounded B := h.bounded.subset inter_subset_left
  have hsepAB : AreSeparated A B := areSeparated_of_disjoint_closure hAbdd hcl
  have hAm : NullMeasurableSet A volume := hAo.measurableSet.nullMeasurableSet
  have hBm : NullMeasurableSet B volume := hBo.measurableSet.nullMeasurableSet
  have hAfin : volume A < ∞ := hAbdd.measure_lt_top
  have hBfin : volume B < ∞ := hBbdd.measure_lt_top
  have hApos : 0 < volume A := hAo.measure_pos volume hΩu
  have hBpos : 0 < volume B := hBo.measure_pos volume hΩv
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : AmbientSpace)).mp h.bounded
  have hAR : A ⊆ ball 0 R := inter_subset_left.trans hR
  have hBR : B ⊆ ball 0 R := inter_subset_left.trans hR
  let e : AmbientSpace := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  -- The cross-interaction of the original pieces is positive and finite.
  have hIpos : 0 < (coulombInteraction A B).toReal :=
    coulombInteraction_toReal_pos A B hApos hBpos hAfin hBfin
  have hev := (tendsto_coulombInteraction_translate hAR hBR he).eventually
    (gt_mem_nhds hIpos)
  obtain ⟨t, ht, htlt⟩ := ((eventually_gt_atTop (2 * R)).and hev).exists
  set Bt := (fun y => y + t • e) '' B with hBtdef
  have hBt_eq : Bt = (fun y => t • e + y) '' B := by
    rw [hBtdef]
    congr 1
    funext y
    exact add_comm _ _
  have hBto : IsOpen Bt := (Homeomorph.addRight (t • e)).isOpenMap B hBo
  have hBtm : NullMeasurableSet Bt volume := hBto.measurableSet.nullMeasurableSet
  have hBtvol : volume Bt = volume B := by rw [hBt_eq, volume_image_translate]
  have hBtfin : volume Bt < ∞ := hBtvol ▸ hBfin
  -- The translated piece is far from `A`.
  have hsepABt : AreSeparated A Bt := by
    refine ⟨ENNReal.ofReal (t - 2 * R), (ENNReal.ofReal_pos.mpr (by linarith)).ne', ?_⟩
    rintro x hx _ ⟨z, hz, rfl⟩
    have hxR : ‖x‖ < R := by simpa using hAR hx
    have hzR : ‖z‖ < R := by simpa using hBR hz
    have ht0 : 0 ≤ t := by linarith [norm_nonneg x]
    have hnorm : ‖t • e‖ = t := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hid : t • e = (x - z) - (x - (z + t • e)) := by abel
    have htri := norm_sub_le (x - z) (x - (z + t • e))
    rw [← hid, hnorm] at htri
    have htri' := norm_sub_le x z
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hABt : Disjoint A Bt := hsepABt.disjoint
  -- Volume constraint for the competitor.
  have hvolF : volume (A ∪ Bt) = ENNReal.ofReal V := by
    rw [measure_union₀ hBtm hABt.aedisjoint, hBtvol, ← measure_union₀ hBm hAB.aedisjoint,
      ← hΩAB, h.volume_eq]
  have hFm : NullMeasurableSet (A ∪ Bt) volume := hAm.union hBtm
  have hle := h.le_energy hFm hvolF
  -- Energy decompositions.
  have hPΩ : perimeter Ω = perimeter A + perimeter B := by
    rw [hΩAB, ← perimeterN_eq_perimeter _ (hAm.union hBm),
      perimeterN_union_of_areSeparated hAm hBm hsepAB, perimeterN_eq_perimeter _ hAm,
      perimeterN_eq_perimeter _ hBm]
  have hPF : perimeter (A ∪ Bt) = perimeter A + perimeter B := by
    rw [← perimeterN_eq_perimeter _ hFm,
      perimeterN_union_of_areSeparated hAm hBtm hsepABt, perimeterN_eq_perimeter _ hAm,
      perimeterN_eq_perimeter _ hBtm, hBt_eq, perimeter_image_translate hBm]
  have hDΩ : coulombEnergy Ω = coulombEnergy A + coulombEnergy B + coulombInteraction A B := by
    rw [hΩAB, coulombEnergy_union A B hBm hAB]
  have hDF : coulombEnergy (A ∪ Bt) =
      coulombEnergy A + coulombEnergy B + coulombInteraction A Bt := by
    rw [coulombEnergy_union A Bt hBtm hABt, hBt_eq, coulombEnergy_translate]
  have hK : perimeter A + perimeter B + (coulombEnergy A + coulombEnergy B) ≠ ∞ := by
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · rw [← hPΩ]; exact h.perimeter_lt_top.ne
    · exact ENNReal.add_ne_top.mpr
        ⟨(LiquidDrop.coulombEnergy_lt_top A hAfin).ne,
          (LiquidDrop.coulombEnergy_lt_top B hBfin).ne⟩
  have hle' : coulombInteraction A B ≤ coulombInteraction A Bt := by
    have h2 : perimeter A + perimeter B + (coulombEnergy A + coulombEnergy B) +
          coulombInteraction A B ≤
        perimeter A + perimeter B + (coulombEnergy A + coulombEnergy B) +
          coulombInteraction A Bt :=
      calc
        _ = energy Ω := by rw [energy, hPΩ, hDΩ]; ring
        _ ≤ energy (A ∪ Bt) := hle
        _ = _ := by rw [energy, hPF, hDF]; ring
    exact (ENNReal.add_le_add_iff_left hK).mp h2
  have hlt : coulombInteraction A Bt < coulombInteraction A B := by
    rw [← ENNReal.toReal_lt_toReal (coulombInteraction_lt_top A Bt hAfin hBtfin).ne
      (coulombInteraction_lt_top A B hAfin hBfin).ne]
    exact htlt
  exact absurd hle' (not_le.mpr hlt)

end MinimizerRep

end LiquidDrop
