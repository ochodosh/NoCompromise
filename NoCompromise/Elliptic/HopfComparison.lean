module

public import NoCompromise.Elliptic.StrongMaximumHarmonic
public import NoCompromise.Sobolev.AnnulusDomain
public import NoCompromise.Elliptic.HopfBarrier

@[expose] public section

/-!
# Compact-domain harmonic comparison

The comparison is for actual continuous distributionally harmonic functions.
It will be applied on annuli whose closures lie strictly inside the given domain.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace LiquidDrop

theorem harmonic_le_zero_of_boundary {n : ℕ} (hn : n < 4)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hconn : IsPreconnected D) (hb : Bornology.IsBounded D)
    (hfront : (frontier D).Nonempty)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContinuousOn u (closure D))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) D)
    (hboundary : ∀ x ∈ frontier D, u x ≤ 0) : ∀ x ∈ closure D, u x ≤ 0 := by
  obtain ⟨p, hp⟩ := hfront
  obtain ⟨y, hy, hmax⟩ := hb.isCompact_closure.exists_isMaxOn
    ⟨p, frontier_subset_closure hp⟩ hu
  have hym : u y ≤ 0 := by
    by_cases hyD : y ∈ D
    · have heq : EqOn u (fun _ => u y) D :=
        strong_maximum hn hD hconn (hu.mono subset_closure) hh hyD
          (fun x hx => hmax (subset_closure hx))
      have heqcl : EqOn u (fun _ => u y) (closure D) :=
        heq.of_subset_closure hu continuousOn_const subset_closure Subset.rfl
      exact (heqcl (frontier_subset_closure hp)).symm.le.trans (hboundary p hp)
    · exact hboundary y (by rw [frontier, hD.interior_eq]; exact ⟨hy, hyD⟩)
  intro x hx
  exact (hmax hx).trans hym

lemma closure_roundAnnulus_subset (q : AmbientSpace) (r t : ℝ) :
    closure (roundAnnulus q r t) ⊆ {x | r ≤ dist x q ∧ dist x q ≤ t} := by
  apply closure_minimal
  · intro x hx
    exact ⟨(mem_roundAnnulus.mp hx).1.le, (mem_roundAnnulus.mp hx).2.le⟩
  · exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)

lemma frontier_roundAnnulus_subset (q : AmbientSpace) {r t : ℝ} :
    frontier (roundAnnulus q r t) ⊆ sphere q r ∪ sphere q t := by
  intro x hx
  have hd := closure_roundAnnulus_subset q r t (frontier_subset_closure hx)
  have hnot : x ∉ roundAnnulus q r t := by
    rw [frontier, (isOpen_roundAnnulus q r t).interior_eq] at hx
    exact hx.2
  by_cases heq : dist x q = r
  · exact Or.inl heq
  · exact Or.inr (le_antisymm hd.2 (by
      by_contra h
      exact hnot (mem_roundAnnulus.mpr ⟨lt_of_le_of_ne hd.1 (Ne.symm heq),
        lt_of_not_ge h⟩)))

theorem hopf_truncated_annulus_comparison (q : AmbientSpace) {R t ε : ℝ}
    (hR : 0 < R) (ht : R / 2 < t) (htR : t < R) (hε : 0 ≤ ε)
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (ball q R))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (ball q R))
    (hpos : ∀ x ∈ ball q R, 0 < u x)
    (hinner : ∀ x ∈ sphere q (R / 2), ε ≤ u x)
    {x : AmbientSpace} (hx : x ∈ roundAnnulus q (R / 2) t) :
    ε * (hopfBarrier q R x - (R / t - 1)) ≤ u x := by
  have hr : 0 < R / 2 := half_pos hR
  have ht0 : 0 < t := hr.trans ht
  let D := roundAnnulus q (R / 2) t
  have hsub : closure D ⊆ ball q R := by
    intro y hy
    exact (closure_roundAnnulus_subset q (R / 2) t hy).2.trans_lt htR
  have hq : q ∉ closure D := by
    intro h
    have he := (closure_roundAnnulus_subset q (R / 2) t h).1
    simp only [dist_self] at he
    exact hr.not_ge he
  have havoid : closure D ⊆ {q}ᶜ := by
    intro y hy heq
    have he : y = q := heq
    exact hq (he ▸ hy)
  have hfront : (frontier D).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨x, hx⟩, fun he => hq (subset_closure (he ▸ mem_univ q))⟩
  let v : AmbientSpace → ℝ := fun y => ε * (hopfBarrier q R y - (R / t - 1)) - u y
  have hv : ContinuousOn v (closure D) :=
    (continuousOn_const.mul (((continuousOn_hopfBarrier q R).mono havoid).sub
      continuousOn_const)).sub (hu.mono hsub)
  have hvh : HasDistributionalLaplacianOn v (fun _ => 0) D := by
    simpa only [v, sub_zero, mul_zero] using
      (((hasDistributionalLaplacianOn_hopfBarrier q R
        (fun h => hq (subset_closure h))).sub
        (hasDistributionalLaplacianOn_const D (R / t - 1))).const_mul ε).sub
          (hh.mono (subset_closure.trans hsub))
  have hboundary : ∀ y ∈ frontier D, v y ≤ 0 := by
    intro y hy
    have hypos := hpos y (hsub (frontier_subset_closure hy))
    rcases frontier_roundAnnulus_subset q hy with hyinner | hyouter
    · have hyn : ‖y - q‖ = R / 2 := by
        simpa only [mem_sphere, dist_eq_norm] using hyinner
      have hb : hopfBarrier q R y = 1 := by
        rw [hopfBarrier, hyn]
        field_simp
        ring
      have houter : 0 ≤ R / t - 1 := sub_nonneg.mpr ((one_le_div ht0).mpr htR.le)
      dsimp only [v]
      rw [hb]
      nlinarith [hinner y hyinner, mul_nonneg hε houter]
    · have hyn : ‖y - q‖ = t := by
        simpa only [mem_sphere, dist_eq_norm] using hyouter
      dsimp only [v, hopfBarrier]
      rw [hyn]
      nlinarith
  have hvx := harmonic_le_zero_of_boundary (by omega)
    (isOpen_roundAnnulus q (R / 2) t) (isPreconnected_roundAnnulus q hr)
    (isBounded_roundAnnulus q (R / 2) t) hfront hv hvh hboundary
    x (subset_closure hx)
  exact sub_nonpos.mp hvx

theorem hopf_annulus_comparison (q : AmbientSpace) {R ε : ℝ}
    (hR : 0 < R) (hε : 0 ≤ ε)
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (ball q R))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (ball q R))
    (hpos : ∀ x ∈ ball q R, 0 < u x)
    (hinner : ∀ x ∈ sphere q (R / 2), ε ≤ u x)
    {x : AmbientSpace} (hx : x ∈ roundAnnulus q (R / 2) R) :
    ε * hopfBarrier q R x ≤ u x := by
  have hxc := mem_roundAnnulus.mp hx
  have hcont : ContinuousAt (fun t : ℝ =>
      ε * (hopfBarrier q R x - (R / t - 1))) R := by fun_prop (disch := positivity)
  have hlim : Tendsto (fun t : ℝ => ε * (hopfBarrier q R x - (R / t - 1)))
      (𝓝[<] R) (𝓝 (ε * hopfBarrier q R x)) := by
    have hlim' : Tendsto (fun t : ℝ => ε * (hopfBarrier q R x - (R / t - 1)))
        (𝓝[<] R) (𝓝 (ε * (hopfBarrier q R x - (R / R - 1)))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [div_self hR.ne', sub_self, sub_zero] using
      hlim'
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hxc.2] with t ht
  exact hopf_truncated_annulus_comparison q hR (hxc.1.trans ht.1) ht.2 hε
    hu hh hpos hinner (mem_roundAnnulus.mpr ⟨hxc.1, ht.1⟩)

end LiquidDrop
