module

public import WeightedMIS.RegisterEdgeMetadata
public import WeightedMIS.RegisterExpandedParameters
public import WeightedMIS.ExpandedSourceSemantics
public import WeightedMIS.SearchHistogramProjection
public import WeightedMIS.SparseGraphConstruction

/-!
# Exact premises of the sparse graph construction

This file supplies the remaining inputs of `SparseGraphConstruction.compiled`
and the hypotheses of `ExpandedWords.SourceInterface`:

* a fixed procedure that counts the cost list at the working width `G` and
  enumerates the canonical label keys `0, ..., m-1` with the binary counter of
  `RegisterWordRange`; the count word itself is the connector key `m`;
* the label-pointer map `labelPtr`, sending an edge to the address of its key
  word and the connector to the count word, with an explicit decoder from
  addresses to keys (`exists_encode`);
* `source_interface`: the edge records built by `RegisterEdgeMetadata`, at the
  vertex and cost widths and with the parameter words of
  `RegisterExpandedParameters`, satisfy every field of `SourceInterface`, so the
  generated adjacency trie is exactly `SparseSearchGraph.Labeled.graph`.
-/

@[expose] public section

namespace WeightedMIS.RegisterGenerationInputs

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.Walks WeightedMIS.CompiledTemplates
open WeightedMIS.ExpandedWords WeightedMIS.ExpandedParameters WeightedMIS.SparseSearchGraph
open WeightedMIS.NodeEncoding WeightedMIS.Expanded WeightedMIS.RegisterColumnResize
open WeightedMIS.SearchHistogramProjection

variable {p : ℕ}

/-! ## Lists given by functions on `Fin m` -/

theorem forall₂_ofFn {α β : Type*} {R : α → β → Prop} :
    ∀ {m : ℕ} {xs : List α} {g : Fin m → β}, List.Forall₂ R xs (List.ofFn g) →
      ∃ f : Fin m → α, xs = List.ofFn f ∧ ∀ e, R (f e) (g e)
  | 0, xs, g, hf => by
    simp only [List.ofFn_zero, List.forall₂_nil_right_iff] at hf
    exact ⟨Fin.elim0, by simp [hf], fun e => e.elim0⟩
  | m + 1, xs, g, hf => by
    rw [List.ofFn_succ] at hf
    cases hf with
    | @cons x _ xs' _ hx hrest =>
      obtain ⟨f, hxs, hfr⟩ := forall₂_ofFn hrest
      refine ⟨Fin.cons x f, by simp [List.ofFn_succ, hxs], ?_⟩
      intro e
      refine Fin.cases ?_ (fun i => ?_) e
      · simpa using hx
      · simpa using hfr i

theorem bitsAt_unique {h : Heap} {n : ℕ} {ptr : Ptr} {a b : Bits n}
    (ha : BitsAt h ptr a) (hb : BitsAt h ptr b) : a = b := by
  induction ha with
  | nil cell =>
    cases hb with
    | nil _ => rfl
  | cons cell rest ih =>
    cases hb with
    | cons cell' rest' =>
      rw [cell] at cell'
      simp only [Option.some.injEq, Cell.bit.injEq] at cell'
      obtain ⟨rfl, rfl⟩ := cell'
      rw [ih rest']

/-! ## Label keys -/

/-- Arguments: cost list, zero word of width `G`. Results: the key words
`0, ..., m-1` and the count word `m`, all of width `G`. -/
def keysBody (count add range : Fin p) : Command p :=
  .call count [.register 0, .register 1, .register 1] [2]
  (.call add [.register 1, .register 1, .flag true] [3, 15]
  (.call range [.register 1, .register 2, .register 3] [4]
  (.ret [.register 4, .register 2])))

structure Procedures (p : ℕ) where
  parameters : RegisterExpandedParameters.Procedures p
  cmp : Fin p
  range : Fin p
  keys : Fin p

def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  ids.parameters.Matches code ∧ code ids.cmp = RegisterComparator.comparatorBody ids.cmp ∧
  code ids.range = RegisterWordRange.rangeBody ids.range ids.parameters.add ids.cmp ∧
  code ids.keys = keysBody ids.parameters.countFold ids.parameters.add ids.range

def keysBudget (G m : ℕ) : ℕ :=
  RegisterExpandedParameters.countFoldBudget G m + RegisterExpandedParameters.addBudget G +
    RegisterWordRange.budget G m + 30

theorem edgeKey_none {m G : ℕ} (hm : m < 2 ^ G) :
    edgeKey G (none : Option (Fin m)) = word G m := by
  rw [edgeKey, word, Nat.mod_eq_of_lt hm]

theorem keys_compiled (code : Code p) (ids : Procedures p) (hc : ids.Matches code)
    {h : Heap} (hh : Valid h) {cp zp : Ptr} {G wc m : ℕ} {costs : List (Bits wc)}
    (hcs : WordsAt h cp costs) (hlen : costs.length = m) (hz : BitsAt h zp (Bits.zero G))
    (hm : m < 2 ^ G) (hG : 1 < 2 ^ G) :
    ∃ out kp mp, Extends h out ∧ Valid out ∧
      WordsAt out kp (List.ofFn (fun e : Fin m => edgeKey G (some e))) ∧
      BitsAt out mp (edgeKey G (none : Option (Fin m))) ∧
      Within code h (initialRegisters [.pointer cp, .pointer zp]) (code ids.keys)
        [.pointer kp, .pointer mp] out (keysBudget G m) := by
  obtain ⟨hpar, hcmp, hrange, hkeys⟩ := hc
  have hs := hpar.1
  have hadd : code ids.parameters.add = RegisterAdder.adderBody ids.parameters.add :=
    hs.2.2.2.2.2.2.2.2.2.1
  obtain ⟨h1, q1, e1, v1, hq1, run1⟩ :=
    RegisterExpandedParameters.countFold_compiled code ids.parameters hs hh hcs hz
  rw [hlen] at hq1 run1
  have hz' : BitsAt h1 zp (word G 0) := by rw [← zero_eq_word]; exact hz.mono e1
  obtain ⟨h2, q2, f2, e2, v2, hq2, run2⟩ :=
    RegisterExpandedParameters.add_word_compiled code ids.parameters.add hadd v1 hz' hz' true
      (v := 1) rfl
  have hone : (word G 1).value = 1 := word_value_of_lt hG
  obtain ⟨h3, q3, words, e3, v3, hq3, hvals, run3⟩ := RegisterWordRange.compiled code ids.range
    ids.parameters.add ids.cmp hrange hadd hcmp v2 (hz.mono (e1.trans e2)) (hq1.mono e2) hq2 hone
  have hmv : (word G m).value = m := word_value_of_lt hm
  rw [hmv, Bits.value_zero, Nat.sub_zero] at hvals run3
  have hwords : words = List.ofFn (fun e : Fin m => edgeKey G (some e)) := by
    have hl : words.length = m := by simpa using congrArg List.length hvals
    apply List.ext_getElem (by simp [hl])
    intro i h1' h2'
    apply ScalarNodeCodec.bits_value_injective
    have hi := List.getElem_of_eq hvals (i := i) (by simpa using h1')
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul] at hi
    rw [hi, List.getElem_ofFn, edgeKey, encodeBits_value _ _ (by simp at h2'; omega)]
  rw [hwords] at hq3
  refine ⟨h3, q3, q1, (e1.trans e2).trans e3, v3, hq3, ?_, ?_⟩
  · rw [edgeKey_none hm]
    exact (hq1.mono e2).mono e3
  let regs := initialRegisters [Value.pointer cp, .pointer zp]
  let r1 := bindResults regs [2] [Value.pointer q1]
  let r2 := bindResults r1 [3, 15] [Value.pointer q2, .flag f2]
  let r3 := bindResults r2 [4] [Value.pointer q3]
  have last : Within code h3 r3 (.ret [.register 4, .register 2]) [.pointer q3, .pointer q1]
      h3 5 := by
    simpa [r3, r2, r1, values, Atom.eval, bindResults] using
      Within.ret code h3 r3 [.register 4, .register 2]
  have a3 : values r2 [.register 1, .register 2, .register 3] =
      [.pointer zp, .pointer q1, .pointer q2] := by
    simp [r2, r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c3 := Within.call (procedure := ids.range) (regs := r2)
    (arguments := [.register 1, .register 2, .register 3]) (results := [4])
    (by simpa only [a3] using run3) last
  have a2 : values r1 [.register 1, .register 1, .flag true] =
      [.pointer zp, .pointer zp, .flag true] := by
    simp [r1, regs, values, Atom.eval, bindResults, initialRegisters]
  have c2 := Within.call (procedure := ids.parameters.add) (regs := r1)
    (arguments := [.register 1, .register 1, .flag true]) (results := [3, 15])
    (by simpa only [a2] using run2) c3
  have a1 : values regs [.register 0, .register 1, .register 1] =
      [.pointer cp, .pointer zp, .pointer zp] := by
    simp [regs, values, Atom.eval, initialRegisters]
  have c1 := Within.call (procedure := ids.parameters.countFold) (regs := regs)
    (arguments := [.register 0, .register 1, .register 1]) (results := [2])
    (by simpa only [a1] using run1) c2
  rw [hkeys]
  exact c1.mono (by simp only [keysBudget, List.length_cons, List.length_nil]; omega)

/-- Label addresses: an edge's key word, and the count word for the connector. -/
def labelPtr {m : ℕ} (L : Fin m → Ptr) (connector : Ptr) : Option (Fin m) → Ptr
  | some e => L e
  | none => connector

theorem labelPtr_bitsAt {m G : ℕ} {h : Heap} {L : Fin m → Ptr} {connector : Ptr}
    (hL : ∀ e, BitsAt h (L e) (edgeKey G (some e)))
    (hc : BitsAt h connector (edgeKey G (none : Option (Fin m)))) :
    ∀ l, BitsAt h (labelPtr L connector l) (edgeKey G l)
  | some e => hL e
  | none => hc

theorem labelPtr_injective {m G : ℕ} {h : Heap} {L : Fin m → Ptr} {connector : Ptr}
    (hm : m < 2 ^ G) (hb : ∀ l, BitsAt h (labelPtr L connector l) (edgeKey G l)) :
    Function.Injective (labelPtr L connector) := by
  intro a b hab
  have ha := hb a
  rw [hab] at ha
  exact edgeKey_injective hm (bitsAt_unique ha (hb b))

/-- A decoder from stored label addresses to their keys. -/
theorem exists_encode {m G : ℕ} {η : Option (Fin m) → Ptr} (hinj : Function.Injective η) :
    ∃ encode : Ptr → Bits G, ∀ l, encode (η l) = edgeKey G l := by
  classical
  refine ⟨fun ptr => if hx : ∃ l, η l = ptr then edgeKey G hx.choose else Bits.zero G,
    fun l => ?_⟩
  have hx : ∃ l', η l' = η l := ⟨l, rfl⟩
  simp only [hx, dite_true]
  rw [hinj hx.choose_spec]

/-- The key words, read as label addresses. -/
theorem labels_of_keys {m G : ℕ} {h : Heap} {kp : Ptr}
    (hk : WordsAt h kp (List.ofFn (fun e : Fin m => edgeKey G (some e)))) :
    ∃ L : Fin m → Ptr, ListAt h kp (List.ofFn L) ∧ ∀ e, BitsAt h (L e) (edgeKey G (some e)) := by
  obtain ⟨ptrs, hl, hf⟩ := hk
  obtain ⟨L, rfl, hL⟩ := forall₂_ofFn hf
  exact ⟨L, hl, hL⟩

/-! ## The source interface of the generated records -/

theorem natAbs_value {n : ℕ} (a : SignedWord n) : a.value.natAbs = a.magnitude.value := by
  unfold SignedWord.value
  split <;> simp

theorem two_lt_vertexWidth (r d m : ℕ) : 2 < 2 ^ vertexWidth r d m := by
  have h4 := (nodeCount_ge r d m).1
  have := Nat.lt_size_self (nodeCount r d m)
  unfold vertexWidth
  omega

/-- The edge metadata stored for the generator at the canonical widths. -/
def edgeMetadata {r m d n1 n2 wc : ℕ} (cost : Fin m → ℕ) (D : Fin m → Fin d → SignedWord n1)
    (P : Fin m → RegisterPotentialStep.Word n2) (K : Fin m → Bits wc) (η : Option (Fin m) → Ptr) :
    Fin m → ArcMetadata (vertexWidth r d m) (costWidth r d m cost) :=
  RegisterEdgeMetadata.metadata (vertexWidth r d m) (costWidth r d m cost)
    (fun e => List.ofFn (D e)) P K (fun e => η (some e))

/-- The generation record packed by the construction. -/
def generationData {r m d n1 n2 wc : ℕ} (C : Fin m → Column (Fin r)) (cost : Fin m → ℕ)
    (D : Fin m → Fin d → SignedWord n1) (P : Fin m → RegisterPotentialStep.Word n2)
    (K : Fin m → Bits wc) (η : Option (Fin m) → Ptr) :
    GenerationData (Fin r) (vertexWidth r d m) (costWidth r d m cost) :=
  SparseGraphConstruction.data C (edgeMetadata (r := r) cost D P K η) (arithmetic r d m)
    (List.replicate d (Bits.zero (vertexWidth r d m))) (Bits.zero (costWidth r d m cost)) (η none)

theorem source_interface {r m d n0 n1 n2 wc : ℕ} (key : State (Fin r) → Bits n0)
    (hkey : ∀ v, (key v).value = (stateEquiv r v).val) (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (hW : ∀ e i, |W e i| ≤ 2) (π : Fin m → ZMod 2) (cost : Fin m → ℕ)
    (D : Fin m → Fin d → SignedWord n1) (hD : ∀ e i, (D e i).value = W e i)
    (P : Fin m → RegisterPotentialStep.Word n2)
    (hP : ∀ e, (RegisterPotentialStep.value (P e) : ZMod 2) = π e)
    (K : Fin m → Bits wc) (hK : ∀ e, (K e).value = cost e) (η : Option (Fin m) → Ptr) :
    SourceInterface m (resizeKey (vertexWidth r d m) key) C W π
      (generationData C cost D P K η)
      (fun l => encodeBits (costWidth r d m cost) (labelValue cost l)) η
      (edgeMetadata cost D P K η) (fun e i => (D e i).resizeTo (vertexWidth r d m)) := by
  have hcap := ExpandedWords.capacity_vertexWidth r d m
  have h2 := two_lt_vertexWidth r d m
  have hmag : ∀ e i, (D e i).magnitude.value < 2 ^ vertexWidth r d m := by
    intro e i
    have ha : ((D e i).value).natAbs ≤ 2 := by
      have h1 := hW e i
      have h2 := Int.abs_eq_natAbs (W e i)
      rw [hD]
      omega
    rw [natAbs_value] at ha
    omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, arithmetic_represents r d m,
    List.length_replicate .., hcap⟩
  · intro v
    have hv := (stateEquiv r v).isLt
    have hn := (nodeCount_ge r d m).2.2
    rw [resizeKey_value v (by rw [hkey]; omega), hkey]
  · intro e
    simp [edgeMetadata, RegisterEdgeMetadata.metadata, List.map_ofFn]
    rfl
  · intro e i
    rw [SignedWord.resizeTo_value _ (hmag e i), hD]
  · intro e
    rw [← hP]
    exact RegisterEdgeMetadata.lowBit_value (P e)
  · intro e
    show Bits.resizeTo _ (K e) = _
    unfold Bits.resizeTo
    have hlt : cost e < 2 ^ costWidth r d m cost := weight_lt_capacity r d m cost (some e)
    rw [hK, Nat.mod_eq_of_lt hlt]
    rfl
  · intro e
    rfl
  · show Bits.zero _ = encodeBits _ 0
    rw [zero_eq_word, word, Nat.zero_mod]

/-- The generated adjacency trie is the labelled sparse search graph. -/
theorem graph_eq {r m d n0 n1 n2 wc : ℕ} (key : State (Fin r) → Bits n0)
    (hkey : ∀ v, (key v).value = (stateEquiv r v).val) (C : Fin m → Column (Fin r))
    (W : Fin m → Fin d → ℤ) (hW : ∀ e i, |W e i| ≤ 2) (π : Fin m → ZMod 2) (cost : Fin m → ℕ)
    (D : Fin m → Fin d → SignedWord n1) (hD : ∀ e i, (D e i).value = W e i)
    (P : Fin m → RegisterPotentialStep.Word n2)
    (hP : ∀ e, (RegisterPotentialStep.value (P e) : ZMod 2) = π e)
    (K : Fin m → Bits wc) (hK : ∀ e, (K e).value = cost e) (η : Option (Fin m) → Ptr) :
    Radix.fromEntries (RegisterGraphEnumeration.entries (resizeKey (vertexWidth r d m) key)
      (generationData C cost D P K η) (encodeBits (vertexWidth r d m) (nodeCount r d m))) =
      SparseSearchGraph.Labeled.graph η C W π m cost := by
  rw [entries_eq_labeled cost (source_interface key hkey C W hW π cost D hD P hP K hK η) _
    (limit_value r d m)]
  rfl

end WeightedMIS.RegisterGenerationInputs
