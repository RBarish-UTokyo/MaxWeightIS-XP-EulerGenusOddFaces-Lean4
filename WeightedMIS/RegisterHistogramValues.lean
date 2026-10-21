module

public import WeightedMIS.RegisterSearchReadback
public import WeightedMIS.ExpandedWords

/-!
# Extracting count words in a supplied edge-label order

The fixed procedure traverses an actual key list, looks up each key in the
computed histogram, and emits the represented count word. Missing keys emit
the supplied zero word. This provides a concrete array input to subsequent
integer-potential recovery.
-/

@[expose] public section

namespace WeightedMIS.RegisterHistogramValues

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch WeightedMIS.ExpandedWords
open WeightedMIS.EfficientSearch.RegisterCode

variable {p : ℕ}

def finishBody (self : Fin p) (head : Atom) : Command p :=
  .call self [.register 4, .register 1, .register 2] [8]
    (.allocate 9 (.cons head (.register 8)) (.ret [.register 9]))

def valuesBody (self lookup : Fin p) : Command p :=
  .load (.register 0) 3 4 15 (listCases (.ret [.null])
    (.call lookup [.register 3, .register 1] [5]
      (.load (.register 5) 6 7 15 (listCases
        (finishBody self (.register 2)) (finishBody self (.register 6))))))

def budget (keybits length : ℕ) : ℕ := 200 * (keybits + 1) * length + 13

theorem finish_compiled {code : Code p} {self : Fin p} {h out : Heap} {regs : Registers}
    {head : Atom} {headPtr tailPtr tablePtr zeroPtr result : Ptr}
    {cb : ℕ} {word : Bits cb} {words : List (Bits cb)} {cost : ℕ}
    (hh : Valid out) (hext : Extends h out)
    (hw : BitsAt h headPtr word) (hwords : WordsAt out result words)
    (hhead : head.eval (bindResults regs [8] [.pointer result]) = .pointer headPtr)
    (h1 : regs 1 = .pointer tablePtr) (h2 : regs 2 = .pointer zeroPtr)
    (h4 : regs 4 = .pointer tailPtr)
    (child : Within code h (initialRegisters [.pointer tailPtr, .pointer tablePtr, .pointer zeroPtr])
      (code self) [.pointer result] out cost) :
    Extends h (out ++ [.cons headPtr result]) ∧ Valid (out ++ [.cons headPtr result]) ∧
      WordsAt (out ++ [.cons headPtr result]) out.length (word :: words) ∧
      Within code h regs (finishBody self head) [.pointer out.length]
        (out ++ [.cons headPtr result]) (cost + 18) := by
  have hs := allocate_word_cons hh (hw.mono hext) hwords
  let recursed := bindResults regs [8] [Value.pointer result]
  have last : Within code (out ++ [.cons headPtr result])
      (Function.update recursed 9 (.pointer out.length)) (.ret [.register 9])
      [.pointer out.length] (out ++ [.cons headPtr result]) 3 := by
    simpa [values, Atom.eval] using Within.ret code (out ++ [.cons headPtr result])
      (Function.update recursed 9 (.pointer out.length)) [.register 9]
  have headStill : head.eval recursed = .pointer headPtr := hhead
  have alloc := Within.allocate (dst := 9) (expr := .cons head (.register 8))
    (by
      simp only [CellExpr.eval, headStill]
      simp [Atom.eval, recursed, bindResults, Value.asPointer]) last
  have hargs : values regs [.register 4, .register 1, .register 2] =
      [.pointer tailPtr, .pointer tablePtr, .pointer zeroPtr] := by
    simp [values, Atom.eval, h4, h1, h2]
  have call := Within.call (procedure := self) (regs := regs)
    (arguments := [.register 4, .register 1, .register 2]) (results := [8])
    (by simpa only [hargs] using child) alloc
  exact ⟨hext.trans hs.1.1, hs.1.2.1, hs.2, call.mono (by simp [CellExpr.args]; omega)⟩

/-- Emit exactly the histogram values in the supplied key order. -/
theorem compiled (code : Code p) (self lookup : Fin p)
    (hself : code self = valuesBody self lookup)
    (hlookup : code lookup = WeightedMIS.CompiledTrie.lookupBody lookup)
    {lb cb : ℕ} {h : Heap} (hh : Valid h) {keysPtr tablePtr zeroPtr : Ptr}
    {keys : List (Bits lb)} {table : Histogram.Table lb cb}
    (hk : WordsAt h keysPtr keys) (ht : Histogram.TableAt h tablePtr table)
    (hz : BitsAt h zeroPtr (Bits.zero cb)) :
    ∃ out result, Extends h out ∧ Valid out ∧
      WordsAt out result (keys.map (fun key => Histogram.count key table)) ∧
      Within code h (initialRegisters [.pointer keysPtr, .pointer tablePtr, .pointer zeroPtr])
        (code self) [.pointer result] out (budget lb keys.length) := by
  induction keys generalizing h keysPtr tablePtr zeroPtr with
  | nil =>
    have hcell := WordsAt.nil_iff.mp hk
    let regs := initialRegisters [Value.pointer keysPtr, .pointer tablePtr, .pointer zeroPtr]
    have last := Within.ret code h (loadRegisters regs 3 4 15 .nil) [.null]
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 3) (second := 4) (bit := 15)
      (branches := listCases (.ret [.null])
        (.call lookup [.register 3, .register 1] [5]
          (.load (.register 5) 6 7 15 (listCases
            (finishBody self (.register 2)) (finishBody self (.register 6))))))
      (by simp [regs, initialRegisters, Atom.eval]) hcell last
    refine ⟨h, 0, Extends.refl h, hh, WordsAt.nil hh.1, ?_⟩
    rw [hself]
    exact load
  | cons key keys ih =>
    obtain ⟨keyPtr, tailPtr, hcell, hkey, htail⟩ := WordsAt.cons_iff.mp hk
    obtain ⟨out, result, hext, hv, hwords, hchild⟩ := ih hh htail ht hz
    obtain ⟨_, itemsPtr, hlookValue, hlookHeap, hitems, hlookCost⟩ :=
      Pointer.lookup_tree_refines hh hkey ht
    obtain ⟨lookupResult, hlookupResult, hlookupCode⟩ := WeightedMIS.CompiledTrie.compile_lookup
      hlookup (Pointer.lookup_tree_eval hkey ht) (initialRegisters [.pointer keyPtr, .pointer tablePtr])
      (by simp [initialRegisters]) (by simp [initialRegisters])
    have hid : lookupResult = itemsPtr := by
      rw [hlookValue] at hlookupResult; exact Option.some.inj hlookupResult.symm
    subst lookupResult
    rw [hlookHeap, ← hlookup] at hlookupCode
    let regs := initialRegisters [Value.pointer keysPtr, .pointer tablePtr, .pointer zeroPtr]
    let loaded := loadRegisters regs 3 4 15 (.cons keyPtr tailPtr)
    let looked := bindResults loaded [5] [Value.pointer itemsPtr]
    have choose : ∃ final resultPtr, Extends h final ∧ Valid final ∧
        WordsAt final resultPtr (Histogram.count key table :: keys.map (fun k => Histogram.count k table)) ∧
        Within code h looked (.load (.register 5) 6 7 15 (listCases
          (finishBody self (.register 2)) (finishBody self (.register 6))))
          [.pointer resultPtr] final (10 + (budget lb keys.length + 18)) := by
      obtain ⟨pointers, hlist, hrel⟩ := hitems
      cases hs : (Radix.lookup key table).1 with
      | nil =>
        rw [hs] at hrel
        cases hrel
        cases hlist with
        | nil hitemsCell =>
          let headRegs := loadRegisters looked 6 7 15 .nil
          have hword : BitsAt h zeroPtr (Histogram.count key table) := by
            simpa [Histogram.count, hs] using hz
          obtain ⟨hfinalExt, hfinalValid, hfinalWords, hfinish⟩ :=
            finish_compiled (regs := headRegs) (head := .register 2) hv hext hword hwords
              (by simp [headRegs, looked, loaded, regs, loadRegisters, decoded, bindResults, initialRegisters, Atom.eval])
              (by simp [headRegs, looked, loaded, regs, loadRegisters, decoded, bindResults, initialRegisters])
              (by simp [headRegs, looked, loaded, regs, loadRegisters, decoded, bindResults, initialRegisters])
              (by simp [headRegs, looked, loaded, regs, loadRegisters, decoded, bindResults, initialRegisters]) hchild
          refine ⟨_, _, hfinalExt, hfinalValid, hfinalWords, ?_⟩
          apply Within.load (budget := budget lb keys.length + 18) (pointer := itemsPtr) (c := .nil)
          · simp [looked, bindResults, Atom.eval]
          · exact hitemsCell
          · exact hfinish
      | cons word words =>
        rw [hs] at hrel
        cases hrel with
        | @cons wordPtr rawWords _ _ hword hrestWords =>
          cases hlist with
          | @cons _ _ restPtr _ hitemsCell hrest =>
            let headRegs := loadRegisters looked 6 7 15 (.cons wordPtr restPtr)
            have hcount : BitsAt h wordPtr (Histogram.count key table) := by
              simpa [Histogram.count, hs] using hword
            obtain ⟨hfinalExt, hfinalValid, hfinalWords, hfinish⟩ :=
              finish_compiled (regs := headRegs) (head := .register 6) hv hext hcount hwords
                (by simp [headRegs, loadRegisters, decoded, bindResults, Atom.eval])
                (by simp [headRegs, looked, loaded, regs, loadRegisters, decoded, bindResults, initialRegisters])
                (by simp [headRegs, looked, loaded, regs, loadRegisters, decoded, bindResults, initialRegisters])
                (by simp [headRegs, looked, loaded, regs, loadRegisters, decoded, bindResults, initialRegisters]) hchild
            refine ⟨_, _, hfinalExt, hfinalValid, hfinalWords, ?_⟩
            apply Within.load (budget := budget lb keys.length + 18) (pointer := itemsPtr) (c := .cons wordPtr restPtr)
            · simp [looked, bindResults, Atom.eval]
            · exact hitemsCell
            · exact hfinish
    obtain ⟨final, resultPtr, he, hvalid, hresult, hchoose⟩ := choose
    have hargs : values loaded [.register 3, .register 1] = [.pointer keyPtr, .pointer tablePtr] := by
      simp [loaded, regs, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have call := Within.call (procedure := lookup) (regs := loaded)
      (arguments := [.register 3, .register 1]) (results := [5])
      (by simpa only [hargs] using hlookupCode) hchoose
    have load := Within.load (regs := regs) (address := .register 0)
      (first := 3) (second := 4) (bit := 15)
      (branches := listCases (.ret [.null])
        (.call lookup [.register 3, .register 1] [5]
          (.load (.register 5) 6 7 15 (listCases
            (finishBody self (.register 2)) (finishBody self (.register 6))))))
      (by simp [regs, initialRegisters, Atom.eval]) hcell call
    refine ⟨final, resultPtr, he, hvalid, hresult, ?_⟩
    rw [hself]
    apply load.mono
    have hs := Radix.lookup_steps key table
    simp only [budget, List.length_cons, List.length_nil, Nat.mul_add]
    omega

end WeightedMIS.RegisterHistogramValues
