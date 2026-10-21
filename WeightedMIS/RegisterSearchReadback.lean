module

public import WeightedMIS.EfficientSearchHistogramRuntime
public import WeightedMIS.RegisterPathLabels

/-!
# Reading the actual shortest-path result

The finite selector follows the settled dictionary's lookup list and stored
record. It returns the actual distance word and predecessor chain, without
reconstructing an existential witness outside the machine.
-/

@[expose] public section

namespace WeightedMIS.RegisterSearchReadback

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.EfficientSearch.Pointer
open WeightedMIS.EfficientSearch.RegisterCode

variable {p : ℕ}

def selectBody (lookup : Fin p) : Command p :=
  .call lookup [.register 1, .register 0] [2]
    (.load (.register 2) 3 4 15
      ⟨.fail, .fail,
        .load (.register 3) 5 6 15
          ⟨.fail, .fail, .fail, .fail, .fail, .ret [.register 5, .register 6]⟩,
        .fail, .fail, .fail⟩)

/-- Exact pointer-level selection of a present settled result. Dictionary
lookup and both record reads are charged in the executable bound. -/
theorem select_compiled (code : Code p) (lookup : Fin p)
    (hlookup : code lookup = WeightedMIS.CompiledTrie.lookupBody lookup)
    {vb cb : ℕ} {h : Heap} (hh : Valid h) {settledPtr targetPtr : Ptr}
    {settled : Settled Ptr vb cb} {target : Bits vb} {distance : Bits cb}
    {path : Trace Ptr vb cb} (hs : SettledAt h settledPtr settled)
    (ht : BitsAt h targetPtr target)
    (hfound : (Radix.lookup target settled).1.head? = some (distance, path)) :
    ∃ dp pp, BitsAt h dp distance ∧ TraceAt h pp path ∧
      Within code h (initialRegisters [.pointer settledPtr, .pointer targetPtr])
        (selectBody lookup) [.pointer dp, .pointer pp] h (300 * (vb + 1) + 30) := by
  obtain ⟨_, items, hvalue, hheap, hitems, hcost⟩ := lookup_tree_refines hh ht hs
  obtain ⟨result, hresult, hexec⟩ := WeightedMIS.CompiledTrie.compile_lookup
    hlookup (lookup_tree_eval ht hs) (initialRegisters [.pointer targetPtr, .pointer settledPtr])
    (by simp [initialRegisters]) (by simp [initialRegisters])
  have heq : result = items := by rw [hvalue] at hresult; exact Option.some.inj hresult.symm
  subst result
  rw [hheap] at hexec
  cases hlist : (Radix.lookup target settled).1 with
  | nil => simp [hlist] at hfound
  | cons stored rest =>
    have hid : stored = (distance, path) := by simpa [hlist] using hfound
    subst stored
    rw [hlist] at hitems
    obtain ⟨raw, hlistRep, hrel⟩ := hitems
    cases hrel with
    | @cons storedPtr rawRest _ _ hstored hrest =>
      cases hlistRep with
      | @cons _ _ tailPtr _ hcell htail =>
        obtain ⟨dp, pp, hstoredCell, hd, hp⟩ := hstored
        let regs := initialRegisters [Value.pointer settledPtr, .pointer targetPtr]
        let looked := bindResults regs [2] [Value.pointer items]
        let loaded := loadRegisters looked 3 4 15 (.cons storedPtr tailPtr)
        let record := loadRegisters loaded 5 6 15 (.pair dp pp)
        have last : Within code h record (.ret [.register 5, .register 6])
            [.pointer dp, .pointer pp] h 5 := by
          simpa [record, loadRegisters, decoded, values, Atom.eval] using
            Within.ret code h record [.register 5, .register 6]
        have loadRecord := Within.load (regs := loaded) (address := .register 3)
          (first := 5) (second := 6) (bit := 15)
          (branches := ⟨.fail, .fail, .fail, .fail, .fail, .ret [.register 5, .register 6]⟩)
          (by simp [loaded, loadRegisters, decoded, Atom.eval]) hstoredCell last
        have loadList := Within.load (regs := looked) (address := .register 2)
          (first := 3) (second := 4) (bit := 15)
          (branches := ⟨.fail, .fail,
            .load (.register 3) 5 6 15
              ⟨.fail, .fail, .fail, .fail, .fail, .ret [.register 5, .register 6]⟩,
            .fail, .fail, .fail⟩)
          (by simp [looked, bindResults, Atom.eval]) hcell loadRecord
        have hargs : values regs [.register 1, .register 0] = [.pointer targetPtr, .pointer settledPtr] := by
          simp [regs, initialRegisters, values, Atom.eval]
        have call := Within.call (procedure := lookup) (regs := regs)
          (arguments := [.register 1, .register 0]) (results := [2])
          (by simpa only [hargs, hlookup] using hexec) loadList
        refine ⟨dp, pp, hd, hp, call.mono ?_⟩
        have hsteps := Radix.lookup_steps target settled
        simp only [List.length_cons, List.length_nil]
        omega

end WeightedMIS.RegisterSearchReadback
