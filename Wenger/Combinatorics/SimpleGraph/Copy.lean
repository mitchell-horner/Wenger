import Mathlib


namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

-- TODO https://github.com/leanprover-community/mathlib4/pull/42138
protected abbrev Copy.map {V' : Type*} (f : V ↪ V') : Copy G (G.map f) := sorry

/-- If `H` has no isolated vertices, then a copy of `H` in `G.map f` gives rise
to a copy of `H` in `G`. -/
theorem IsContained.of_isContained_map (hH_iso : ∀ {w}, ¬H.IsIsolated w)
    {V' : Type*} {f : V ↪ V'} (h : H ⊑ G.map f) : H ⊑ G := by
  obtain ⟨c⟩ := h
  have hrange : ∀ w : W, c.toHom w ∈ Set.range f := fun x ↦ by
    obtain ⟨w', hww'⟩ := exists_adj_iff_not_isIsolated.mpr hH_iso
    obtain ⟨v, -, -, hv, -⟩ := (map_adj f G ..).mp (c.toHom.map_adj hww')
    exact ⟨v, hv⟩
  choose g hg using hrange
  refine ⟨⟨⟨g, fun {w w'} hww' ↦ ?_⟩, fun w w' hww' ↦ ?_⟩⟩
  · rw [← map_adj_apply, hg w, hg w']
    exact c.toHom.map_adj hww'
  · rw [RelHom.coeFn_mk] at hww'
    apply c.injective
    rw [← hg w, ← hg w', hww']

/-- For `H` without isolated vertices, `H` is contained in `G.map f` exactly
when it is contained in `G`. -/
theorem isContained_map_iff (h_iso : ∀ {w}, ¬H.IsIsolated w) {V' : Type*} {f : V ↪ V'} :
    H ⊑ G.map f ↔ H ⊑ G :=
  ⟨IsContained.of_isContained_map h_iso, (Copy.map f).isContained.trans'⟩

end SimpleGraph
