module

public import WeightedMIS.EdgeTransport
public import WeightedMIS.Incidence

/-!
# Faithful relabelling of endpoint walks and adjacency
-/

@[expose] public section

namespace WeightedMIS.Incidence

variable {U V D E : Type*} {leftU rightU : D → U} {leftV rightV : E → V}
    (ev : U ≃ V) (ee : D ≃ E)
    (hl : ∀ e, ev (leftU e) = leftV (ee e))
    (hr : ∀ e, ev (rightU e) = rightV (ee e))

include hl hr in
/-- Relabel every actual edge traversal in a finite walk. -/
theorem relabel_walk {a b : U} {n : ℕ} (p : Walk leftU rightU a b n) :
    Walk leftV rightV (ev a) (ev b) n := by
  induction p with
  | nil => exact .nil _
  | @forward b n e hb p ih =>
      rw [hr]
      exact .forward (ee e) ((congrArg ev hb).trans (hl e)) ih
  | @backward b n e hb p ih =>
      rw [hl]
      exact .backward (ee e) ((congrArg ev hb).trans (hr e)) ih

include hl hr in
/-- Connectivity is unchanged by actual vertex and edge bijections. -/
theorem connected_relabel (hc : Connected leftV rightV) : Connected leftU rightU := by
  have hl' (e : E) : ev.symm (leftV e) = leftU (ee.symm e) := by
    apply ev.injective
    rw [Equiv.apply_symm_apply, hl, Equiv.apply_symm_apply]
  have hr' (e : E) : ev.symm (rightV e) = rightU (ee.symm e) := by
    apply ev.injective
    rw [Equiv.apply_symm_apply, hr, Equiv.apply_symm_apply]
  intro a b
  obtain ⟨n, p⟩ := hc (ev a) (ev b)
  exact ⟨n, by simpa only [Equiv.symm_apply_apply] using relabel_walk ev.symm ee.symm hl' hr' p⟩

include hl hr in
/-- A proper two-coloring transports across the same genuine endpoint bijections. -/
theorem bipartite_relabel (hb : Bipartite leftU rightU) : Bipartite leftV rightV := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨fun v => c (ev.symm v), ?_⟩
  intro e
  have h := hc (ee.symm e)
  have hl' : leftU (ee.symm e) = ev.symm (leftV e) := by
    apply ev.injective
    rw [hl, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hr' : rightU (ee.symm e) = ev.symm (rightV e) := by
    apply ev.injective
    rw [hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rwa [hl', hr'] at h

include hl hr in
/-- Adjacency uses the same original edge after relabelling its endpoints. -/
theorem adj_relabel (u v : U) :
    EdgeTransport.Adj leftU rightU u v ↔ EdgeTransport.Adj leftV rightV (ev u) (ev v) := by
  constructor
  · rintro ⟨e, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · exact ⟨ee e, Or.inl ⟨(hl e).symm.trans (congrArg ev hu),
        (hr e).symm.trans (congrArg ev hv)⟩⟩
    · exact ⟨ee e, Or.inr ⟨(hl e).symm.trans (congrArg ev hu),
        (hr e).symm.trans (congrArg ev hv)⟩⟩
  · rintro ⟨e, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · refine ⟨ee.symm e, Or.inl ⟨?_, ?_⟩⟩ <;> apply ev.injective
      · simpa only [hl, Equiv.apply_symm_apply] using hu
      · simpa only [hr, Equiv.apply_symm_apply] using hv
    · refine ⟨ee.symm e, Or.inr ⟨?_, ?_⟩⟩ <;> apply ev.injective
      · simpa only [hl, Equiv.apply_symm_apply] using hu
      · simpa only [hr, Equiv.apply_symm_apply] using hv

/-- Actual finite endpoint adjacency is decided by scanning the finite edge set. -/
def endpointAdjDecidable [Fintype E] [DecidableEq V] :
    DecidableRel (EdgeTransport.Adj leftV rightV) := by
  intro u v
  unfold EdgeTransport.Adj
  infer_instance

/-- A nonbipartite endpoint graph has an actual edge. -/
theorem nonempty_edges_of_nonbipartite (hnb : ¬Bipartite leftV rightV) : Nonempty E := by
  by_contra h
  have hi : IsEmpty E := not_nonempty_iff.mp h
  exact hnb ⟨fun _ => false, fun e => isEmptyElim e⟩

end WeightedMIS.Incidence
