import Mathlib
import Wenger.Combinatorics.SimpleGraph.Copy


open Finset

namespace SimpleGraph

variable {W : Type*} {H : SimpleGraph W}

/-- For `H` without isolated vertices, `ex(·, H)` is monotone. -/
theorem extremalNumber_mono (hH_iso : ∀ {w}, ¬H.IsIsolated w) {m n : ℕ} (hm_le_n : m ≤ n) :
    extremalNumber m H ≤ extremalNumber n H := by
  rw [← Fintype.card_fin m, extremalNumber_le_iff]
  intro G _ hH_free
  rw [← card_edgeFinset_map (Fin.castLEEmb hm_le_n) G]
  have hH_free' : H.Free (G.map (Fin.castLEEmb hm_le_n)) :=
    fun hH_con ↦ hH_free <| hH_con.of_isContained_map hH_iso
  have hcard_map := card_edgeFinset_le_extremalNumber hH_free'
  rw [Fintype.card_fin] at hcard_map
  convert hcard_map

@[inherit_doc extremalNumber_mono]
theorem monotone_extremalNumber (hH : ∀ {w}, ¬H.IsIsolated w) :
    Monotone (extremalNumber · H) :=
  fun _ _ ↦ extremalNumber_mono hH

end SimpleGraph
