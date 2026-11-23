import ProductionBoundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import HeightSqueeze
import HeightShift

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions
open GlobalTheory.Mem.Top.Bl GlobalTheory.EX.OB GeometryAudit.ProductionHeight

namespace GeometryAudit.SectionMetric

/-- The genuine base certificate identifies the actual model record. Each
    nonterminal row has a component with the library's zero section height. -/
theorem zero_at_base {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7}
    {J : Formalism.L2.Pj.Core D} {X : DivX D} (g : geoOf Q D J X)
    (j : ℕ) (hj : 1 ≤ j) (hm : j < D.R.m) :
    ∃ c : X.Comp j, componentHeight X j c = 0 := by
  obtain ⟨⟨n, _, T, law, Φ, seed, iM, reg, _, rfl, reads, _⟩, _⟩ := g
  obtain ⟨c, _, _, zero⟩ := ProductionBoundary.earlier_row_obstruction Φ seed iM reg reads j hj hm
  exact ⟨c, zero⟩

theorem zero_after_transport {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7}
    {J : Formalism.L2.Pj.Core D} {X : DivX D} (g : GeoCl (geoOf Q) D J X) :
    ∀ j, 1 ≤ j → j < D.R.m → ∃ c : X.Comp j, componentHeight X j c = 0 := by
  induction g with
  | base h => exact zero_at_base h
  | step N h _ ih =>
    intro j hj hm
    obtain ⟨c, hc⟩ := ih j hj hm
    exact ⟨c, hc⟩

/-- On a genuine row with a valid production link, keep the chosen section
    metric and all its components. One formula normalization exceeds every
    component height in rows 1 through m at the distinguished word. The full
    divisor link holds with a single new allowance on this row. -/
theorem link_above_components {Q : ∀ D : D7, GlobalTheory.ShFam.KitClass D} {D : D7}
    {J : Formalism.L2.Pj.Core D} {X : DivX D} (g : GeoCl (geoOf Q) D J X)
    (L : SizeData₂ D) {C CH k₀ : ℝ}
    (link : LinkDIV_at L C 2 CH) (formula : ∀ v, D.div.h v = hExpl6 D L X k₀ v) :
    ∃ (k s : ℝ), k₀ < k ∧ 0 < s ∧
      let N := fun v => (D.div.Nu v).L
      let h := hExpl6 D L X k
      let D' := setDiv D N h
      let X' := divTr N h X
      let L' := ledTr N h L
      GeoCl (geoOf Q) D' (coreS N h J) X' ∧ LinkDIV_at L' (C + s) 2 CH ∧
      (∀ v, D'.div.h v = hExpl6 D' L' X' k v) ∧
      (∃ c : X'.Comp 1, componentHeight X' 1 c = 0) ∧
      ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c : X'.Comp j, componentHeight X' j c < D'.div.h D.u₀ := by
  classical
  let values (i : Σ j : Fin (D.R.m + 1), X.Comp j.val) := componentHeight X i.1.val i.2
  obtain ⟨M, hM⟩ := (Set.finite_range values).bddAbove
  let s := max 0 (M - D.div.h D.u₀) + 1
  have hs : 0 < s := by dsimp [s]; linarith [le_max_left 0 (M - D.div.h D.u₀)]
  have gap : M < D.div.h D.u₀ + s := by dsimp [s]; linarith [le_max_right 0 (M - D.div.h D.u₀)]
  obtain ⟨k, target, _⟩ := HeightSqueeze.existsUnique_constant D L X D.u₀ (D.div.h D.u₀ + s)
  have hk : k₀ < k := (formula_strictMono D L X D.u₀).lt_iff_lt.mp (by rw [target, ← formula]; linarith)
  have allWords : hExpl6 D L X k = fun v => D.div.h v + s := by
    funext v
    linarith only [HeightSqueeze.formula_shift D L X k k₀ D.u₀ v, target, formula D.u₀, formula v]
  obtain ⟨c, hc⟩ := zero_after_transport g 1 le_rfl (lt_of_lt_of_le Nat.one_lt_two D.R.two_le_m)
  refine ⟨k, s, hk, hs, GeoCl.step _ _ g, ?_, fun _ => rfl, ⟨c, hc⟩, ?_⟩
  · rw [allWords]
    exact HeightShift.link_after_shift L link (by norm_num) s hs.le
  · intro j _ hj c
    have upper := hM (Set.mem_range_self (f := values) ⟨⟨j, by omega⟩, c⟩)
    change componentHeight X j c < hExpl6 D L X k D.u₀
    rw [target]
    exact lt_of_le_of_lt upper gap

#print axioms zero_after_transport
#print axioms link_above_components
end GeometryAudit.SectionMetric
