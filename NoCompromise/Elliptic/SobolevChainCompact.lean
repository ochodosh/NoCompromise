import NoCompromise.Elliptic.SobolevChainBounds
import NoCompromise.Sobolev.ExtensionPartition

/-!
# Sobolev embedding on relatively compact domains

Finite ball covers and smooth partitions patch compatible local representatives.
Their local agreement preserves the derivative bounds on the prescribed compact set.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

/-- Compatible continuous representatives agree on every open overlap. -/
lemma sobolevChain_representatives_eqOn {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {u v w : EuclideanSpace ℝ (Fin n) → ℝ} (hv : Continuous v) (hw : Continuous w)
    (heqv : v =ᵐ[volume.restrict U] u) (heqw : w =ᵐ[volume.restrict V] u) :
    EqOn v w (U ∩ V) := by
  have hv' : v =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left heqv
  have hw' : w =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right heqw
  exact Measure.eqOn_open_of_ae_eq (hv'.trans hw'.symm) (hU.inter hV)
    hv.continuousOn hw.continuousOn

/-- A finite weighted sum of compatible representatives equals each local representative
where the weights sum to one. -/
lemma sobolevChain_partition_sum_eq {n : ℕ} {ι : Type*} [Fintype ι]
    {U : ι → Set (EuclideanSpace ℝ (Fin n))} (hU : ∀ i, IsOpen (U i))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {w ζ : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    (hw : ∀ i, Continuous (w i)) (heq : ∀ i, w i =ᵐ[volume.restrict (U i)] u)
    (hsζ : ∀ i, tsupport (ζ i) ⊆ U i) {i : ι} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ U i) (hone : ∑ j, ζ j x = 1) : (∑ j, ζ j x * w j x) = w i x := by
  classical
  calc
    (∑ j, ζ j x * w j x) = ∑ j, ζ j x * w i x := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hz : ζ j x = 0
      · simp [hz]
      · rw [sobolevChain_representatives_eqOn (hU j) (hU i) (hw j) (hw i)
          (heq j) (heq i) ⟨hsζ j (subset_tsupport _ hz), hx⟩]
    _ = (∑ j, ζ j x) * w i x := (Finset.sum_mul ..).symm
    _ = w i x := by rw [hone, one_mul]

/-- The finite partition sum realizes the original L² class on every measurable set
where the scalar weights sum to one. -/
lemma sobolevChain_partition_sum_ae {n : ℕ} {ι : Type*} [Fintype ι]
    {U : ι → Set (EuclideanSpace ℝ (Fin n))} (hU : ∀ i, IsOpen (U i))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {w ζ : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    (heq : ∀ i, w i =ᵐ[volume.restrict (U i)] u)
    (hsζ : ∀ i, tsupport (ζ i) ⊆ U i)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : MeasurableSet V)
    (hone : ∀ x ∈ V, ∑ j, ζ j x = 1) :
    (fun x => ∑ j, ζ j x * w j x) =ᵐ[volume.restrict V] u := by
  have heq' : ∀ᵐ x ∂volume, ∀ i, x ∈ U i → w i x = u x :=
    ae_all_iff.mpr fun i => (ae_restrict_iff' (hU i).measurableSet).mp (heq i)
  filter_upwards [ae_restrict_of_ae heq', ae_restrict_mem hV] with x hx hxV
  calc
    (∑ j, ζ j x * w j x) = ∑ j, ζ j x * u x := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hz : ζ j x = 0
      · simp [hz]
      · rw [hx j (hsζ j (subset_tsupport _ hz))]
    _ = (∑ j, ζ j x) * u x := (Finset.sum_mul ..).symm
    _ = u x := by rw [hone x hxV, one_mul]

/-- The quantitative Sobolev estimate on any compact subset of an open domain.
The constant precedes the function, its derivative data, and the measurable region of agreement. -/
theorem compact_sobolev_contDiff_bound {n k m : ℕ} (hn : n < 4) (hkm : k + 2 ≤ m)
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ)
      (d : SobolevDerivativeData U m u) (V : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet V → V ⊆ K →
      ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ k w ∧
        w =ᵐ[volume.restrict V] u ∧
        ∀ j ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ j w x‖ ≤ C * d.norm := by
  classical
  obtain ⟨η, _, hcη, hsη, hηone, _⟩ :=
    exists_smooth_cutoff_one_near_compact hK hU hKU
  have hKK : K ⊆ tsupport η := by
    intro x hx
    have hηx : η x = 1 := (hηone.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
    exact subset_tsupport _ (by simp [hηx])
  choose R hR hRU using fun c : tsupport η =>
    Metric.isOpen_iff.mp hU c (hsη c.property)
  obtain ⟨t, ht⟩ := hcη.elim_finite_subcover
    (fun c : tsupport η => ball (c : EuclideanSpace ℝ (Fin n)) (R c / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hR ⟨x, hx⟩))⟩)
  let c (i : t) : EuclideanSpace ℝ (Fin n) := i.val.val
  let A (i : t) := ball (c i) (R i.val / 2)
  have hcover : tsupport η ⊆ ⋃ i : t, A i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hi, hxi⟩ := mem_iUnion.mp hxi
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ζ, B, hζ, hone, _⟩ := exists_finite_smooth_partition_of_bounded_open_cover
    hcη A (fun _ => isOpen_ball) (fun _ => isBounded_ball) hcover
  choose C hC hb using fun i : t =>
    interior_sobolev_contDiff_bound_of_le (k := k) hn (c i) (half_lt_self (hR i.val)) hkm
  let M := 1 + ∑ i : t, C i
  have hM : 0 < M := by
    dsimp [M]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => (hC i).le)
  refine ⟨M, hM, ?_⟩
  intro u d V hV hVK
  choose w hw hweq hwb using fun i : t => hb i u (d.mono (hRU i.val))
  let v (x : EuclideanSpace ℝ (Fin n)) := ∑ i : t, ζ i x * w i x
  have hv : ContDiff ℝ k v :=
    ContDiff.sum fun i _ => ((hζ i).1.of_le (by simp)).mul (hw i)
  have hveq : v =ᵐ[volume.restrict V] u :=
    sobolevChain_partition_sum_ae (fun _ => isOpen_ball) hweq (fun i => (hζ i).2.2.1)
      hV (fun x hx => hone x (hKK (hVK hx)))
  refine ⟨v, hv, hveq, ?_⟩
  intro j hj x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover (hKK hx))
  have hnear : v =ᶠ[𝓝 x] w i := by
    have hηnear : ∀ᶠ y in 𝓝 x, η y = 1 := hηone.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [hηnear, isOpen_ball.mem_nhds hxi] with y hy hyi
    exact sobolevChain_partition_sum_eq (fun _ => isOpen_ball)
      (fun i => (hw i).continuous) hweq (fun i => (hζ i).2.2.1) hyi
      (hone y (subset_tsupport _ (by simp [hy])))
  rw [(hnear.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
  have hCi : C i ≤ M := by
    have hsum : C i ≤ ∑ l : t, C l :=
      Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => (hC l).le) (Finset.mem_univ i)
    exact hsum.trans (le_add_of_nonneg_left zero_le_one)
  exact (hwb i j hj x hxi).trans
    ((mul_le_mul_of_nonneg_left (d.norm_mono (hRU i.val)) (hC i).le).trans
      (mul_le_mul_of_nonneg_right hCi d.norm_nonneg))

end LiquidDrop
