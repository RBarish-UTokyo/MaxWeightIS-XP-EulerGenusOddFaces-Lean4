module

public import WeightedMIS.CompiledTrie
public import WeightedMIS.EfficientSearchCodeBounds
public import WeightedMIS.PointerRepresentations
public import WeightedMIS.Walks

/-!
# Finite register programs for signed-column arc templates

A signed stub is a sign bit pointing to its row's two stored state keys.
Columns are nil, bucket(stub), or pair(stub,stub). Each input edge pairs a
column with a shared metadata record. Output templates pair source and target
state keys with that same metadata pointer; no coefficient arithmetic or
host-language function occurs in the finite command syntax.
-/

@[expose] public section

namespace WeightedMIS.CompiledTemplates

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.CompiledTrie WeightedMIS.Walks

variable {p : ℕ}

/-- Arguments 0=source, 1=target, 2=metadata, 3=tail. Prepend one template. -/
def emitBody : Command p :=
  .allocate 4 (.pair (.register 1) (.register 2))
    (.allocate 5 (.pair (.register 0) (.register 4))
      (.allocate 6 (.cons (.register 5) (.register 3)) (.ret [.register 6])))

/-- Read a signed stub and return its opposite-state key and own-state key. -/
def stubBody : Command p :=
  .load (.register 0) 2 3 4 {
    failCases with
    bit := .load (.register 2) 5 6 7 {
      failCases with
      pair := .branch (.register 4) (.ret [.register 5, .register 6])
        (.ret [.register 6, .register 5])
    }
  }

def oneBody (stub emit : Fin p) : Command p :=
  .call stub [.register 4] [5, 6]
    (.call emit [.register 5, .register 2, .register 1, .register 3] [9]
      (.call emit [.register 2, .register 6, .register 1, .register 9] [9] (.ret [.register 9])))

def twoBody (stub emit : Fin p) : Command p :=
  .call stub [.register 4] [5, 6]
    (.call stub [.register 10] [7, 8]
      (.call emit [.register 7, .register 6, .register 1, .register 3] [9]
        (.call emit [.register 5, .register 8, .register 1, .register 9] [9] (.ret [.register 9]))))

/-- Arguments 0=column, 1=metadata, 2=hub key, 3=tail. The output order is the
forward template followed by the reverse template when the column is nonzero. -/
def columnBody (stub emit : Fin p) : Command p :=
  .load (.register 0) 4 10 15 {failCases with
    nil := .call emit [.register 2, .register 2, .register 1, .register 3] [9] (.ret [.register 9])
    bucket := oneBody stub emit
    pair := twoBody stub emit}

/-- Arguments 0=edge-record list, 1=hub key, 2=output tail. Recursively prepend
the actual one-or-two templates of each edge record. -/
def listBody (self column : Fin p) : Command p :=
  .load (.register 0) 3 4 5 {failCases with
    nil := .ret [.register 2]
    cons := .load (.register 3) 6 7 8 {
      failCases with
      pair := .call self [.register 4, .register 1, .register 2] [9]
        (.call column [.register 6, .register 7, .register 1, .register 9] [10] (.ret [.register 10]))
    }
  }

/-- Logical templates retain the full shared metadata value. -/
structure Template (Row Metadata : Type*) where
  source : State Row
  target : State Row
  metadata : Metadata

/-- Exact logical output of the finite column procedure. -/
def templates {Row Metadata : Type*} (c : Column Row) (metadata : Metadata) : List (Template Row Metadata) :=
  match c with
  | .zero => [⟨none, none, metadata⟩]
  | .one s => [⟨none, some s, metadata⟩, ⟨some (opposite s), none, metadata⟩]
  | .two s t => [⟨some (opposite s), some t, metadata⟩,
      ⟨some (opposite t), some s, metadata⟩]

theorem templates_length_le_two {Row Metadata : Type*} (c : Column Row) (metadata : Metadata) :
    (templates c metadata).length ≤ 2 := by cases c <;> simp [templates]

/-- The actual one-or-two arcs of a single signed column in forward/reverse order. -/
def columnArcs {Row : Type*} (c : Column Row) : List (Arc (fun _ : Unit => c)) :=
  match c with
  | .zero => [⟨((), false), Or.inr rfl⟩]
  | .one _ => [⟨((), false), Or.inr rfl⟩, ⟨((), true), Or.inl (by simp)⟩]
  | .two _ _ => [⟨((), false), Or.inr rfl⟩, ⟨((), true), Or.inl (by simp)⟩]

theorem templates_eq_arcs {Row Metadata : Type*} (c : Column Row) (metadata : Metadata) :
    templates c metadata = (columnArcs c).map (fun a =>
      ⟨source (fun _ : Unit => c) a, target (fun _ : Unit => c) a, metadata⟩) := by
  cases c <;> rfl

/-- Actual stored signed-row state keys; all bits are supplied data. -/
def StubAt {Row : Type*} {width : ℕ} (key : State Row → Bits width)
    (h : Heap) (ptr : Ptr) (s : Stub Row) : Prop :=
  ∃ row minus plus, h[ptr]? = some (.bit s.2 row) ∧ h[row]? = some (.pair minus plus) ∧
    BitsAt h minus (key (some (s.1, false))) ∧ BitsAt h plus (key (some (s.1, true)))

inductive ColumnAt {Row : Type*} {width : ℕ} (key : State Row → Bits width) (h : Heap) :
    Ptr → Column Row → Prop
  | zero {ptr} (cell : h[ptr]? = some .nil) : ColumnAt key h ptr .zero
  | one {ptr sp s} (cell : h[ptr]? = some (.bucket sp)) (stub : StubAt key h sp s) :
      ColumnAt key h ptr (.one s)
  | two {ptr sp tp s t} (cell : h[ptr]? = some (.pair sp tp))
      (first : StubAt key h sp s) (second : StubAt key h tp t) : ColumnAt key h ptr (.two s t)

/-- The output record has the exact source/target/metadata sharing layout. -/
def TemplateAt {Row Metadata : Type*} {width : ℕ} (key : State Row → Bits width)
    (metaAt : Heap → Ptr → Metadata → Prop) (h : Heap) (ptr : Ptr) (a : Template Row Metadata) : Prop :=
  ∃ source target mp inside, h[ptr]? = some (.pair source inside) ∧
    h[inside]? = some (.pair target mp) ∧ BitsAt h source (key a.source) ∧
    BitsAt h target (key a.target) ∧ metaAt h mp a.metadata

/-- Stored input edge records associate each actual column with its metadata. -/
def EdgeAt {Row Metadata : Type*} {width : ℕ} (key : State Row → Bits width)
    (metaAt : Heap → Ptr → Metadata → Prop) (h : Heap) (ptr : Ptr) (a : Column Row × Metadata) : Prop :=
  ∃ column mp, h[ptr]? = some (.pair column mp) ∧ ColumnAt key h column a.1 ∧ metaAt h mp a.2

end WeightedMIS.CompiledTemplates
