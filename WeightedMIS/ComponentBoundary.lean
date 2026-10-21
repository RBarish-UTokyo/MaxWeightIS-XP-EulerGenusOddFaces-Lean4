module

public import WeightedMIS.GraphComponents

/-!
# Every deleted-edge component meets a retained edge

In a connected endpoint graph, retaining at least one edge makes every
component of the complementary edge set incident to a retained edge. The
proof follows genuine edge walks and identifies the first retained edge;
no topological region incidence is assumed.
-/

@[expose] public section

namespace WeightedMIS.Incidence

variable {V E : Type*} (left right : E → V) (keep : E → Prop)

/-- The component map for the graph with precisely the complementary edges. -/
def deletedComponentOf (v : V) :
    Component (fun e : {e : E // ¬keep e} => left e.val) (fun e => right e.val) :=
  componentOf _ _ v

/-- A deleted-edge component meets one of the retained edge endpoints. -/
def MeetsRetained (q : Component (fun e : {e : E // ¬keep e} => left e.val)
    (fun e => right e.val)) : Prop :=
  ∃ e : E, keep e ∧
    (deletedComponentOf left right keep (left e) = q ∨
      deletedComponentOf left right keep (right e) = q)

/-- A walk either encounters a retained edge or stays in one deleted component. -/
theorem walk_meets_or_same {a b : V} {n : ℕ} (p : Walk left right a b n) :
    MeetsRetained left right keep (deletedComponentOf left right keep a) ∨
      deletedComponentOf left right keep a = deletedComponentOf left right keep b := by
  classical
  induction p with
  | nil => exact Or.inr rfl
  | @forward b n e hb p ih =>
      subst b
      rcases ih with ih | ih
      · exact Or.inl ih
      · by_cases he : keep e
        · exact Or.inl ⟨e, he, Or.inl ih.symm⟩
        · exact Or.inr (ih.trans (componentOf_endpoints _ _ (⟨e, he⟩ : {e : E // ¬keep e})))
  | @backward b n e hb p ih =>
      subst b
      rcases ih with ih | ih
      · exact Or.inl ih
      · by_cases he : keep e
        · exact Or.inl ⟨e, he, Or.inr ih.symm⟩
        · exact Or.inr (ih.trans (componentOf_endpoints _ _ (⟨e, he⟩ : {e : E // ¬keep e})).symm)

/-- Every actual complementary component meets the retained graph when the
original graph is connected and at least one edge is retained. -/
theorem every_deleted_component_meets (hc : Connected left right)
    (hne : Nonempty {e : E // keep e})
    (q : Component (fun e : {e : E // ¬keep e} => left e.val) (fun e => right e.val)) :
    MeetsRetained left right keep q := by
  obtain ⟨e⟩ := hne
  let a := Quotient.out q
  have ha : deletedComponentOf left right keep a = q := Quotient.out_eq q
  obtain ⟨n, p⟩ := hc a (left e.val)
  rcases walk_meets_or_same left right keep p with h | h
  · rwa [ha] at h
  · exact ⟨e.val, e.property, Or.inl (h.symm.trans ha)⟩

end WeightedMIS.Incidence
