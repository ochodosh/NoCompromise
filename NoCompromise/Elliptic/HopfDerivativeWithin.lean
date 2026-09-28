import NoCompromise.Elliptic.Hopf

/-!
# Hopf's sign for a derivative taken from the domain

This applies to C¹ functions on the closure of a domain without requiring
any prescribed extension of the function across its boundary.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace LiquidDrop

theorem hopf_boundary_derivative_within {G : Set AmbientSpace}
    {q p : AmbientSpace} {R : ℝ} (hR : 0 < R)
    (hball : ball q R ⊆ G) (hp : p ∈ sphere q R)
    {u : AmbientSpace → ℝ} (hu : ContinuousOn u (G ∪ {p}))
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) G)
    (hpos : ∀ x ∈ G, 0 < u x) (hup : u p = 0)
    {L : AmbientSpace →L[ℝ] ℝ} (hd : HasFDerivWithinAt u L G p) :
    L ((1 / R) • (p - q)) < 0 := by
  obtain ⟨c, hc, hquot⟩ := (hopf_boundary hR hball hp hu hh hpos hup).1
  let v : AmbientSpace := (1 / R) • (q - p)
  have hpath : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hmaps : MapsTo (fun s : ℝ => p + s • v) (Ioo 0 (R / 2)) G := by
    intro s hs
    have hsR : s < R := hs.2.trans (half_lt_self hR)
    apply hball
    change p + s • v ∈ ball q R
    have heq : p + s • v = p + (s / R) • (q - p) := by
      simp only [v, smul_smul, mul_one_div]
    rw [heq, mem_ball, dist_eq_norm, norm_hopf_inward_point q p hR hp hs.1.le hsR.le]
    linarith [hs.1]
  have hdu : HasDerivWithinAt (fun s : ℝ => u (p + s • v)) (L v) (Ioo 0 (R / 2)) 0 :=
    hd.comp_hasDerivWithinAt_of_eq 0 hpath.hasDerivWithinAt hmaps (by simp)
  have hlim : Tendsto
      (fun s : ℝ => (u (p + (s / R) • (q - p)) - u p) / s)
      (𝓝[>] 0) (𝓝 (L v)) := by
    have hh := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioo 0 (R / 2))).mp hdu
    rw [nhdsWithin_Ioo_eq_nhdsGT (half_pos hR)] at hh
    change Tendsto (fun s => slope (fun t : ℝ => u (p + t • v)) 0 s)
      (𝓝[>] 0) (𝓝 (L v)) at hh
    simpa [slope_def_field, v, smul_smul, div_eq_mul_inv, mul_comm] using hh
  have hcL : c ≤ L v := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (half_pos hR)] with s hs
    exact hquot s hs
  have hneg : L v = -L ((1 / R) • (p - q)) := by
    dsimp only [v]
    rw [← neg_sub p q, smul_neg, map_neg]
  rw [hneg] at hcL
  linarith

end LiquidDrop
