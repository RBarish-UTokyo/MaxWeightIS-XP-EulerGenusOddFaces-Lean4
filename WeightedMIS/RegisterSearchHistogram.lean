module

public import WeightedMIS.RegisterSearchReadback

/-! # Executable readback and multiplicities of the stored predecessor path -/

@[expose] public section

namespace WeightedMIS.RegisterSearchHistogram

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch.RegisterCode

variable {p : ℕ}

def readbackBody (select labels histogram : Fin p) : Command p :=
  .call select [.register 0, .register 1] [3, 4]
    (.call labels [.register 4] [5]
      (.call histogram [.register 5, .null, .register 2] [6, 7]
        (.ret [.register 3, .register 6, .register 7])))

structure Procedures (p : ℕ) where
  lookup : Fin p
  insert : Fin p
  add : Fin p
  select : Fin p
  labels : Fin p
  histogram : Fin p

def Procedures.Matches (d : Procedures p) (code : Code p) : Prop :=
  code d.lookup = WeightedMIS.CompiledTrie.lookupBody d.lookup ∧
  code d.insert = WeightedMIS.CompiledTrie.insertBody d.insert ∧
  code d.add = WeightedMIS.RegisterAdder.adderBody d.add ∧
  code d.select = RegisterSearchReadback.selectBody d.lookup ∧
  code d.labels = RegisterPathLabels.labelsBody d.labels ∧
  code d.histogram = histogramBody d.lookup d.add d.insert d.histogram

def budget (vb lb cb length : ℕ) : ℕ :=
  300 * (vb + 1) + (2000 * (lb + cb + 2) + 54) * length + 100

theorem lookup_compiled (code : Code p) (self : Fin p)
    (hself : code self = WeightedMIS.CompiledTrie.lookupBody self)
    {h : Heap} {key tree : Ptr} {result : Run (Option Ptr)} (he : LookupEval h key tree result) :
    Within code h (initialRegisters [.pointer key, .pointer tree]) (code self)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_lookup hself he
    (initialRegisters [.pointer key, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv, hself]
  exact hc.mono (by omega)

theorem insert_compiled (code : Code p) (self : Fin p)
    (hself : code self = WeightedMIS.CompiledTrie.insertBody self)
    {h : Heap} {key a tree : Ptr} {result : Run (Option Ptr)} (he : InsertEval h key a tree result) :
    Within code h (initialRegisters [.pointer key, .pointer a, .pointer tree]) (code self)
      (pointerOutput result.value) result.heap (100 * result.trace.length) := by
  obtain ⟨out, hv, hc⟩ := WeightedMIS.CompiledTrie.compile_insert hself he
    (initialRegisters [.pointer key, .pointer a, .pointer tree])
    (by simp [initialRegisters]) (by simp [initialRegisters]) (by simp [initialRegisters])
  rw [hv, hself]
  exact hc.mono (by omega)

theorem label_relation {h : Heap} {vb cb lb : ℕ} (encode : Ptr → Bits lb)
    (path : Trace Ptr vb cb)
    (hlabels : ∀ e ∈ path, BitsAt h e.2.label (encode e.2.label)) :
    List.Forall₂ (BitsAt h) (path.map (fun e => e.2.label))
      (path.map (fun e => encode e.2.label)) := by
  induction path with
  | nil => exact .nil
  | cons e path ih =>
    exact .cons (hlabels e (by simp)) (ih (fun e he => hlabels e (by simp [he])))

/-- The code follows the actual stored result and returns its represented
cost and exact label multiplicities. Every dependency is a specified finite
body, including the binary adder, trie operations and predecessor traversal. -/
theorem compiled (code : Code p) (d : Procedures p) (hm : d.Matches code)
    {vb cb lb countbits : ℕ} {h : Heap} (hh : Valid h)
    {settledPtr targetPtr zeroPtr : Ptr} {settled : Settled Ptr vb cb}
    {target : Bits vb} {distance : Bits cb} {path : Trace Ptr vb cb}
    (hs : SettledAt h settledPtr settled) (ht : BitsAt h targetPtr target)
    (hz : BitsAt h zeroPtr (Bits.zero countbits))
    (hfound : (Radix.lookup target settled).1.head? = some (distance, path))
    (encode : Ptr → Bits lb) (hlabels : ∀ e ∈ path, BitsAt h e.2.label (encode e.2.label))
    (hwidth : path.length < 2 ^ countbits) :
    ∃ (out : Heap) (dp tablePtr : Ptr) (table : Histogram.Table lb countbits),
      Extends h out ∧ Valid out ∧ BitsAt out dp distance ∧ Histogram.TableAt out tablePtr table ∧
      (∀ key, (Histogram.count key table).value = (path.map (fun e => encode e.2.label)).count key) ∧
      Within code h (initialRegisters [.pointer settledPtr, .pointer targetPtr, .pointer zeroPtr])
        (readbackBody d.select d.labels d.histogram) [.pointer dp, .pointer tablePtr, .flag false]
        out (budget vb lb countbits path.length) := by
  rcases hm with ⟨hlookup, hinsert, hadd, hselect, hlabelCode, hhist⟩
  obtain ⟨dp, pp, hd, hp, hse⟩ := RegisterSearchReadback.select_compiled code d.lookup
    hlookup hh hs ht hfound
  rw [← hselect] at hse
  obtain ⟨labelsPtr, labelledHeap, hle, hlext, hlrep⟩ :=
    RegisterPathLabels.compiled code d.labels hlabelCode hh hp
  have hlvalid : Valid labelledHeap := by
    obtain ⟨events, he, _⟩ := hle
    have ha : ValuesBound h.length [.pointer pp] := by
      intro v hv; simp only [List.mem_singleton] at hv; subst v; exact hp.allocated
    exact (he.safe hh (initialRegisters_bounded (null_allocated hh) ha)).1.2.1
  let keys := path.map (fun e => encode e.2.label)
  have hlkeys : Histogram.LabelsAt labelledHeap labelsPtr keys :=
    ⟨_, hlrep, label_relation encode path (fun e he => (hlabels e he).mono hlext)⟩
  have hempty : Histogram.TableAt labelledHeap 0 (.empty : Histogram.Table lb countbits) :=
    ⟨.empty, .empty hlvalid.1, .empty⟩
  obtain ⟨out, tablePtr, hext, hv, htable, hhe⟩ := Histogram.collect_compiled hhist
    (lookup_compiled code d.lookup hlookup) (RegisterAdder.compiled code d.add hadd)
    (insert_compiled code d.insert hinsert) hlvalid hempty (hz.mono hlext) hlkeys
  obtain ⟨hflag, hcounts⟩ := Histogram.empty_correct keys (by simpa [keys] using hwidth)
  rw [hflag] at hhe
  let regs := initialRegisters [Value.pointer settledPtr, .pointer targetPtr, .pointer zeroPtr]
  let selected := bindResults regs [3, 4] [Value.pointer dp, .pointer pp]
  let labelled := bindResults selected [5] [Value.pointer labelsPtr]
  let counted := bindResults labelled [6, 7] [Value.pointer tablePtr, .flag false]
  have last : Within code out counted (.ret [.register 3, .register 6, .register 7])
      [.pointer dp, .pointer tablePtr, .flag false] out 7 := by
    simpa [counted, labelled, selected, bindResults, values, Atom.eval] using
      Within.ret code out counted [.register 3, .register 6, .register 7]
  have hhargs : values labelled [.register 5, .null, .register 2] =
      [.pointer labelsPtr, .pointer 0, .pointer zeroPtr] := by
    simp [labelled, selected, regs, bindResults, initialRegisters, values, Atom.eval]
  have histCall := Within.call (procedure := d.histogram) (regs := labelled)
    (arguments := [.register 5, .null, .register 2]) (results := [6, 7])
    (by simpa only [hhargs] using hhe) last
  have hlargs : values selected [.register 4] = [.pointer pp] := by
    simp [selected, bindResults, values, Atom.eval]
  have labelsCall := Within.call (procedure := d.labels) (regs := selected)
    (arguments := [.register 4]) (results := [5])
    (by simpa only [hlargs] using hle) histCall
  have hsargs : values regs [.register 0, .register 1] = [.pointer settledPtr, .pointer targetPtr] := by
    simp [regs, initialRegisters, values, Atom.eval]
  have selectCall := Within.call (procedure := d.select) (regs := regs)
    (arguments := [.register 0, .register 1]) (results := [3, 4])
    (by simpa only [hsargs] using hse) labelsCall
  refine ⟨out, dp, tablePtr, _, hlext.trans hext, hv, hd.mono (hlext.trans hext), htable,
    hcounts, selectCall.mono ?_⟩
  simp only [List.length_cons, List.length_nil, Histogram.budget, budget, keys, List.length_map]
  simp only [Nat.add_mul]
  omega

end WeightedMIS.RegisterSearchHistogram
