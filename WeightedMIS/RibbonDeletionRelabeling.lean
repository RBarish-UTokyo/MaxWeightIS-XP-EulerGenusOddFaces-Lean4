module

public import WeightedMIS.RibbonRestrictionCompatibility
public import WeightedMIS.NestedRetention

/-!
# Exact geometry of nested computed component restrictions

An edge relabelling commutes with the bounded deletion trace. Selecting a
corner-closed part after deletion gives the same actual corner matching as
retaining its original edge labels in one step.
-/

@[expose] public section

namespace WeightedMIS.EmbeddingFaces.Ribbon

open SidePairing

variable {U V D E : Type*} [Fintype D] [Fintype E]
    {leftU rightU : D → U} {leftV rightV : E → V}

/-- The computed deletion construction commutes with any actual corner
conjugacy and the corresponding edge-retention predicates. -/
theorem computedRestrict_map (S : Ribbon leftU rightU) (R : Ribbon leftV rightV)
    (ee : D ≃ E) (hc : ∀ x, Flag.mapEquiv ee (S.corner x) = R.corner (Flag.mapEquiv ee x))
    (p : D → Prop) (q : E → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ∀ e, p e ↔ q (ee e)) (x : Flag {e : D // p e}) :
    Flag.mapEquiv (ee.subtypeEquiv hp) ((S.computedRestrict p).corner x) =
      (R.computedRestrict q).corner (Flag.mapEquiv (ee.subtypeEquiv hp) x) := by
  apply (Flag.retainedEquiv q).injective
  apply Subtype.ext
  have hσ : Function.Semiconj (Flag.mapEquiv ee) (S.corner.trans across) (R.corner.trans across) := by
    intro a
    change Flag.mapEquiv ee (across (S.corner a)) = across (R.corner (Flag.mapEquiv ee a))
    rw [Flag.mapEquiv_across, hc]
  have ht := PermutationDeletion.firstReturn_map (S.corner.trans across) (R.corner.trans across)
    (Flag.mapEquiv ee) hσ (fun a => p a.edge) (fun a => q a.edge)
    (fun a => hp a.edge) (Flag.retainedEquiv p x)
  have hs := congrArg (Flag.mapEquiv ee) (S.computedRestrict_corner_val p x)
  rw [Flag.mapEquiv_across, ht] at hs
  exact hs.trans (R.computedRestrict_corner_val q (Flag.mapEquiv (ee.subtypeEquiv hp) x)).symm

/-- A corner-closed second restriction is exactly one restriction of the
original edge labels, including its inherited cyclic orders. -/
theorem computedRestrict_nested_closed (R : Ribbon leftV rightV)
    (p : E → Prop) [DecidablePred p] (r : {e : E // p e} → Prop) [DecidablePred r]
    [DecidablePred (NestedRetention.keep p r)]
    (hclosed : ∀ x : Flag {e : E // p e}, r x.edge → r ((R.computedRestrict p).corner x).edge)
    (x : Flag {e : {e : E // p e} // r e}) :
    Flag.mapEquiv (NestedRetention.edgeEquiv p r).symm
      (((R.computedRestrict p).computedRestrict r).corner x) =
        (R.computedRestrict (NestedRetention.keep p r)).corner
          (Flag.mapEquiv (NestedRetention.edgeEquiv p r).symm x) := by
  let y := (Flag.retainedEquiv r x).val
  let z := Flag.mapEquiv (NestedRetention.edgeEquiv p r).symm x
  let σ := R.corner.trans across
  let a := Flag.retainedEquiv p y
  have hnext : NestedRetention.keep p r (PermutationDeletion.firstReturn σ
      (fun t => p t.edge) a).val.edge := by
    refine ⟨(PermutationDeletion.firstReturn σ (fun t => p t.edge) a).property, ?_⟩
    intro h
    have hr := hclosed y x.edge.property
    have he := congrArg Flag.edge (R.computedRestrict_corner_val p y)
    have he' : ((R.computedRestrict p).corner y).edge =
        ⟨(PermutationDeletion.firstReturn σ (fun t => p t.edge) a).val.edge, h⟩ :=
      Subtype.ext he
    rwa [← he']
  have ht := PermutationDeletion.firstReturn_subpredicate σ (fun t => p t.edge)
    (fun t => NestedRetention.keep p r t.edge) (fun _ h => h.1)
    (Flag.retainedEquiv (NestedRetention.keep p r) z) hnext
  apply (Flag.retainedEquiv (NestedRetention.keep p r)).injective
  apply Subtype.ext
  have hn := (R.computedRestrict p).computedRestrict_corner_closed r hclosed x
  have hn' := congrArg (fun t : Flag {e : E // p e} => (Flag.retainedEquiv p t).val) hn
  have hs := R.computedRestrict_corner_val p y
  have hq := R.computedRestrict_corner_val (NestedRetention.keep p r) z
  rw [ht] at hq
  exact hn'.trans (hs.trans hq.symm)

/-- Arbitrary successive band deletions give exactly the original one-step
deletion, including every retained cyclic successor. -/
theorem computedRestrict_nested (R : Ribbon leftV rightV)
    (p : E → Prop) [DecidablePred p] (r : {e : E // p e} → Prop) [DecidablePred r]
    [DecidablePred (NestedRetention.keep p r)]
    (x : Flag {e : {e : E // p e} // r e}) :
    Flag.mapEquiv (NestedRetention.edgeEquiv p r).symm
      (((R.computedRestrict p).computedRestrict r).corner x) =
        (R.computedRestrict (NestedRetention.keep p r)).corner
          (Flag.mapEquiv (NestedRetention.edgeEquiv p r).symm x) := by
  let σ := R.corner.trans across
  let q := NestedRetention.keep p r
  have hσ : Function.Semiconj (Flag.retainedEquiv p)
      ((R.computedRestrict p).corner.trans across)
      (PermutationDeletion.firstReturn σ (fun a => p a.edge)) := by
    intro a
    apply Subtype.ext
    change across (Flag.retainedEquiv p ((R.computedRestrict p).corner a)).val = _
    rw [R.computedRestrict_corner_val, across_across]
  have hp : ∀ a : Flag {e : E // p e}, r a.edge ↔ q (Flag.retainedEquiv p a).val.edge := by
    intro a
    exact ⟨fun ha => ⟨a.edge.property, fun _ => ha⟩, fun ha => ha.2 a.edge.property⟩
  let y := (Flag.retainedEquiv p).subtypeEquiv
    (p := fun a => r a.edge) (q := fun a => q a.val.edge) hp (Flag.retainedEquiv r x)
  have ht := PermutationDeletion.firstReturn_map ((R.computedRestrict p).corner.trans across)
    (PermutationDeletion.firstReturn σ (fun a => p a.edge)) (Flag.retainedEquiv p) hσ
    (fun a => r a.edge) (fun a => q a.val.edge) hp (Flag.retainedEquiv r x)
  have hn := PermutationDeletion.firstReturn_nested σ (fun a => p a.edge)
    (fun a => q a.edge) (fun _ h => h.1) y
  apply (Flag.retainedEquiv q).injective
  apply Subtype.ext
  have hs := (R.computedRestrict p).computedRestrict_corner_val r x
  have hs' := congrArg (fun a : Flag {e : E // p e} => (Flag.retainedEquiv p a).val) hs
  have hv := congrArg Subtype.val ht
  have ha (a : Flag {e : E // p e}) :
      (Flag.retainedEquiv p (across a)).val = across (Flag.retainedEquiv p a).val := rfl
  rw [ha] at hs'
  rw [hv, hn] at hs'
  exact hs'.trans (R.computedRestrict_corner_val q
    (Flag.mapEquiv (NestedRetention.edgeEquiv p r).symm x)).symm

end WeightedMIS.EmbeddingFaces.Ribbon
