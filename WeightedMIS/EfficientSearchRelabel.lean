module

public import WeightedMIS.EfficientSearchRecovery
public import WeightedMIS.SparseSearchLabeled

/-!
# Sparse search is independent of arc labels

The sparse search reads only targets and weights of adjacency entries. Labels
are copied into predecessor records but never inspected. Mapping every label
through a function before the search therefore maps the queue, settled table,
looked-up result and recovered path in the same way.
-/

@[expose] public section

namespace WeightedMIS.EfficientSearch

variable {α β γ : Type*} {Label Label' : Type*} {vbits cbits : ℕ}

namespace Radix

/-- Apply a function to every stored payload, preserving the trie shape. -/
def map (f : α → β) : {n : ℕ} → Radix α n → Radix β n
  | _, .empty => .empty
  | _, .bucket xs => .bucket (xs.map f)
  | _, .fork l r => .fork (map f l) (map f r)

@[simp] theorem map_empty (f : α → β) {n : ℕ} : map f (.empty : Radix α n) = .empty := rfl

theorem map_map (f : α → β) (g : β → γ) {n : ℕ} (t : Radix α n) :
    map g (map f t) = map (g ∘ f) t := by
  induction t with
  | empty => rfl
  | bucket xs => simp [map]
  | fork l r ihl ihr => simp [map, ihl, ihr]

theorem map_id {n : ℕ} (t : Radix α n) : map id t = t := by
  induction t with
  | empty => rfl
  | bucket xs => simp [map]
  | fork l r ihl ihr => simp [map, ihl, ihr]

theorem map_congr {f g : α → β} (hfg : ∀ a, f a = g a) {n : ℕ} (t : Radix α n) :
    map f t = map g t := by
  rw [show f = g from funext hfg]

@[simp] theorem emptyRoot_map (f : α → β) {n : ℕ} (t : Radix α n) :
    emptyRoot (map f t) = emptyRoot t := by
  cases t <;> rfl

theorem canonical_map (f : α → β) {n : ℕ} (t : Radix α n) :
    canonical (map f t) ↔ canonical t := by
  induction t with
  | empty => exact Iff.rfl
  | bucket xs => simp [map, canonical]
  | fork l r ihl ihr => simp [map, canonical, ihl, ihr]

theorem map_leaf (f : α → β) (xs : List α) : map f (leaf xs) = leaf (xs.map f) := by
  cases xs <;> rfl

theorem map_join (f : α → β) {n : ℕ} (l r : Radix α n) :
    map f (join l r) = join (map f l) (map f r) := by
  unfold join
  simp only [emptyRoot_map]
  split <;> rfl

theorem elements_map (f : α → β) {n : ℕ} (t : Radix α n) :
    elements (map f t) = (elements t).map (fun x => (x.1, f x.2)) := by
  induction t with
  | empty => rfl
  | bucket xs => simp [map, elements]
  | fork l r ihl ihr => simp [map, elements, ihl, ihr, Function.comp_def]

theorem insert_map (f : α → β) {n : ℕ} (key : Bits n) (a : α) (t : Radix α n) :
    insert key (f a) (map f t) = (map f (insert key a t).1, (insert key a t).2) := by
  induction key with
  | nil => cases t <;> rfl
  | @cons n b key ih =>
    cases t with
    | empty =>
      have h := ih (.empty : Radix α n)
      simp only [map_empty] at h
      cases b <;> simp [insert, map, h]
    | fork l r =>
      cases b <;> simp [insert, map, ih]

theorem lookup_map (f : α → β) {n : ℕ} (key : Bits n) (t : Radix α n) :
    lookup key (map f t) = ((lookup key t).1.map f, (lookup key t).2) := by
  induction key with
  | nil => cases t <;> rfl
  | cons b key ih =>
    cases t with
    | empty => rfl
    | fork l r => cases b <;> simp [lookup, map, ih]

theorem pop_map (f : α → β) {n : ℕ} (t : Radix α n) :
    pop (map f t) = ((pop t).1.map (fun x => (x.1, f x.2.1, map f x.2.2)), (pop t).2) := by
  induction t with
  | empty => rfl
  | bucket xs =>
    cases xs with
    | nil => rfl
    | cons a xs => simp [map, pop, map_leaf]
  | fork l r ihl ihr =>
    simp only [map, pop, ihl, ihr]
    cases hl : (pop l).1 with
    | some x =>
      obtain ⟨key, a, l'⟩ := x
      simp [map_join]
    | none =>
      cases hr : (pop r).1 with
      | some x =>
        obtain ⟨key, a, r'⟩ := x
        simp [map_join]
      | none => simp

theorem countEntries_map (f : α → β) {n : ℕ} (t : Radix α n) :
    countEntries (map f t) = countEntries t := by
  induction t with
  | empty => rfl
  | bucket xs => simp [map, countEntries]
  | fork l r ihl ihr => simp [map, countEntries, ihl, ihr]

theorem insertEntries_map (f : α → β) {n : ℕ} (entries : List (Bits n × α)) (t : Radix α n) :
    insertEntries (entries.map (fun x => (x.1, f x.2))) (map f t) =
      map f (insertEntries entries t) := by
  induction entries with
  | nil => rfl
  | cons e rest ih => simp [insertEntries, ih, insert_map]

theorem fromEntries_map (f : α → β) {n : ℕ} (entries : List (Bits n × α)) :
    fromEntries (entries.map (fun x => (x.1, f x.2))) = map f (fromEntries entries) := by
  simpa [fromEntries] using insertEntries_map f entries (.empty : Radix α n)

end Radix

/-- Relabel one adjacency entry. -/
def Arc.relabel (f : Label → Label') (a : Arc Label vbits cbits) : Arc Label' vbits cbits :=
  ⟨a.target, a.weight, f a.label⟩

@[simp] theorem Arc.relabel_target (f : Label → Label') (a : Arc Label vbits cbits) :
    (a.relabel f).target = a.target := rfl

@[simp] theorem Arc.relabel_weight (f : Label → Label') (a : Arc Label vbits cbits) :
    (a.relabel f).weight = a.weight := rfl

@[simp] theorem Arc.relabel_label (f : Label → Label') (a : Arc Label vbits cbits) :
    (a.relabel f).label = f a.label := rfl

/-- Relabel a stored source-tagged entry. -/
def rawRelabel (f : Label → Label') (e : Bits vbits × Arc Label vbits cbits) :
    Bits vbits × Arc Label' vbits cbits := (e.1, e.2.relabel f)

/-- Relabel every predecessor record of a reverse path. -/
def traceRelabel (f : Label → Label') (t : Trace Label vbits cbits) : Trace Label' vbits cbits :=
  t.map (rawRelabel f)

@[simp] theorem traceRelabel_nil (f : Label → Label') :
    traceRelabel f ([] : Trace Label vbits cbits) = [] := rfl

@[simp] theorem traceRelabel_cons (f : Label → Label') (e : Bits vbits × Arc Label vbits cbits)
    (t : Trace Label vbits cbits) :
    traceRelabel f (e :: t) = rawRelabel f e :: traceRelabel f t := rfl

theorem traceRelabel_reverse (f : Label → Label') (t : Trace Label vbits cbits) :
    traceRelabel f t.reverse = (traceRelabel f t).reverse := by
  simp [traceRelabel, List.map_reverse]

theorem traceRelabel_length (f : Label → Label') (t : Trace Label vbits cbits) :
    (traceRelabel f t).length = t.length := by simp [traceRelabel]

def Candidate.relabel (f : Label → Label') (c : Candidate Label vbits cbits) :
    Candidate Label' vbits cbits := ⟨c.vertex, traceRelabel f c.reversePath⟩

def Graph.relabel (f : Label → Label') (g : Graph Label vbits cbits) : Graph Label' vbits cbits :=
  Radix.map (Arc.relabel f) g

def Queue.relabel (f : Label → Label') (q : Queue Label vbits cbits) : Queue Label' vbits cbits :=
  Radix.map (Candidate.relabel f) q

def Settled.relabel (f : Label → Label') (s : Settled Label vbits cbits) :
    Settled Label' vbits cbits :=
  Radix.map (fun x => (x.1, traceRelabel f x.2)) s

def Result.relabel (f : Label → Label') (r : Result Label vbits cbits) : Result Label' vbits cbits :=
  ⟨r.status, Settled.relabel f r.settled, Queue.relabel f r.queue, r.work⟩

theorem relax_relabel (f : Label → Label') (u : Candidate Label vbits cbits) (distance : Bits cbits)
    (edges : List (Arc Label vbits cbits)) (queue : Queue Label vbits cbits) :
    relax (u.relabel f) distance (edges.map (Arc.relabel f)) (Queue.relabel f queue) =
      (Queue.relabel f (relax u distance edges queue).1, (relax u distance edges queue).2) := by
  induction edges generalizing queue with
  | nil => rfl
  | cons e rest ih =>
    have hi := Radix.insert_map (Candidate.relabel f) (Bits.add distance e.weight).1
      (⟨e.target, (u.vertex, e) :: u.reversePath⟩ : Candidate Label vbits cbits) queue
    have hc : ({ vertex := e.target, reversePath := ((Candidate.relabel f u).vertex,
        Arc.relabel f e) :: (Candidate.relabel f u).reversePath } : Candidate Label' vbits cbits) =
        Candidate.relabel f { vertex := e.target, reversePath := (u.vertex, e) :: u.reversePath } :=
      rfl
    simp only [Queue.relabel] at ih ⊢
    simp only [relax, List.map_cons, Arc.relabel_weight, Arc.relabel_target]
    rw [hc, hi]
    dsimp only
    rw [ih]

@[simp] theorem Candidate.relabel_vertex (f : Label → Label') (c : Candidate Label vbits cbits) :
    (c.relabel f).vertex = c.vertex := rfl

@[simp] theorem Candidate.relabel_reversePath (f : Label → Label')
    (c : Candidate Label vbits cbits) :
    (c.relabel f).reversePath = traceRelabel f c.reversePath := rfl

theorem run_relabel (f : Label → Label') (graph : Graph Label vbits cbits) (fuel : ℕ)
    (queue : Queue Label vbits cbits) (settled : Settled Label vbits cbits) :
    run (Graph.relabel f graph) fuel (Queue.relabel f queue) (Settled.relabel f settled) =
      (run graph fuel queue settled).relabel f := by
  induction fuel generalizing queue settled with
  | zero => rfl
  | succ fuel ih =>
    have hpop := Radix.pop_map (Candidate.relabel f) queue
    simp only [Queue.relabel, Settled.relabel] at ih ⊢
    cases hp : (Radix.pop queue).1 with
    | none =>
      simp only [run, hpop, hp, Option.map_none]
      rfl
    | some item =>
      obtain ⟨distance, candidate, queue'⟩ := item
      have hk := Radix.lookup_map (fun x : Bits cbits × Trace Label vbits cbits =>
        (x.1, traceRelabel f x.2)) candidate.vertex settled
      have hg := Radix.lookup_map (Arc.relabel f) candidate.vertex graph
      cases hl : (Radix.lookup candidate.vertex settled).1 with
      | cons x xs =>
        simp only [run, hpop, hp, Option.map_some, Candidate.relabel_vertex, hk, hl, List.map_cons, ih]
        rfl
      | nil =>
        have hs := Radix.insert_map (fun x : Bits cbits × Trace Label vbits cbits =>
          (x.1, traceRelabel f x.2)) candidate.vertex (distance, candidate.reversePath) settled
        have hr := relax_relabel f candidate distance (Radix.lookup candidate.vertex graph).1 queue'
        simp only [Queue.relabel] at hr
        simp only [run, hpop, hp, Option.map_some, Candidate.relabel_vertex,
          Candidate.relabel_reversePath, hk, hl, List.map_nil, Graph.relabel, hg, hr]
        simp only [Graph.relabel] at ih
        rw [hs]
        cases hov : (relax candidate distance (Radix.lookup candidate.vertex graph).1 queue').2.1
        · simp only [Bool.false_eq_true, ↓reduceIte, ih]
          rfl
        · simp only [↓reduceIte]
          rfl

theorem solve_relabel (f : Label → Label') (graph : Graph Label vbits cbits) (source : Bits vbits) :
    solve (Graph.relabel f graph) source = (solve graph source).relabel f := by
  have hi : (Radix.insert (Bits.zero cbits) (Candidate.mk source ([] : Trace Label' vbits cbits))
      .empty) = (Queue.relabel f (Radix.insert (Bits.zero cbits)
        (Candidate.mk source ([] : Trace Label vbits cbits)) .empty).1,
      (Radix.insert (Bits.zero cbits) (Candidate.mk source ([] : Trace Label vbits cbits))
        (.empty : Queue Label vbits cbits)).2) :=
    Radix.insert_map (Candidate.relabel f) (Bits.zero cbits)
      (Candidate.mk source ([] : Trace Label vbits cbits)) .empty
  have he : (Radix.empty : Settled Label' vbits cbits) = Settled.relabel f .empty := rfl
  have hc : Radix.countEntries (Graph.relabel f graph) = Radix.countEntries graph :=
    Radix.countEntries_map _ _
  unfold solve
  rw [hi, hc]
  dsimp only
  rw [he, run_relabel]
  rfl

theorem lookupResult_relabel (f : Label → Label') (result : Result Label vbits cbits)
    (target : Bits vbits) :
    lookupResult (result.relabel f) target =
      (lookupResult result target).map (fun x => (x.1, traceRelabel f x.2)) := by
  simp only [lookupResult, Result.relabel, Settled.relabel, Radix.lookup_map, List.head?_map]

theorem recover_relabel (f : Label → Label') (result : Result Label vbits cbits)
    (target : Bits vbits) :
    recover (result.relabel f) target =
      ((recover result target).1.map (fun x => (x.1, traceRelabel f x.2)),
        (recover result target).2) := by
  unfold recover
  simp only [Result.relabel, Settled.relabel, Radix.lookup_map]
  cases (Radix.lookup target result.settled).1 with
  | nil => rfl
  | cons x xs =>
    simp only [List.map_cons, reverseCount_value, reverseCount_steps, List.append_nil,
      Option.map_some, traceRelabel_reverse, traceRelabel_length]

/-- Search on a relabelled graph, followed by lookup, yields the relabelled
distance and reverse path of the search on the original graph. -/
theorem solve_lookup_relabel (f : Label → Label') (graph : Graph Label vbits cbits)
    (source target : Bits vbits) :
    lookupResult (solve (Graph.relabel f graph) source) target =
      (lookupResult (solve graph source) target).map (fun x => (x.1, traceRelabel f x.2)) := by
  rw [solve_relabel, lookupResult_relabel]

end WeightedMIS.EfficientSearch

namespace WeightedMIS.SparseSearchGraph.Labeled

open WeightedMIS.EfficientSearch

theorem entries_comp {Label Label' : Type*} {r m d : ℕ} (η : Option (Fin m) → Label)
    (f : Label → Label') (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    entries (f ∘ η) C W π radius w =
      (entries η C W π radius w).map (rawRelabel f) := by
  simp only [entries, List.map_flatMap, List.map_map]
  rfl

/-- The labeled sparse graph with labels `f ∘ η` is the relabelled graph. -/
theorem graph_comp {Label Label' : Type*} {r m d : ℕ} (η : Option (Fin m) → Label)
    (f : Label → Label') (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    graph (f ∘ η) C W π radius w = Graph.relabel f (graph η C W π radius w) := by
  rw [graph, entries_comp, graph, Graph.relabel, ← Radix.fromEntries_map]
  rfl

theorem graph_eq_relabel_id {Label : Type*} {r m d : ℕ} (η : Option (Fin m) → Label)
    (C : Fin m → Walks.Column (Fin r))
    (W : Fin m → Fin d → ℤ) (π : Fin m → ZMod 2) (radius : ℕ) (w : Fin m → ℕ) :
    graph η C W π radius w = Graph.relabel η (graph id C W π radius w) :=
  graph_comp id η C W π radius w

end WeightedMIS.SparseSearchGraph.Labeled
