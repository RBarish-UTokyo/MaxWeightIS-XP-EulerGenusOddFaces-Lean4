module

public import WeightedMIS.ExpandedContext
public import WeightedMIS.EfficientSearchCodeBounds

/-! # Constant-size packing of a decoded working context -/

@[expose] public section

namespace WeightedMIS.RegisterContextPack

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.ExpandedWords

variable {p n : ℕ}

def body : Command p :=
  .allocate 6 (.pair (.register 3) (.register 4))
    (.allocate 6 (.pair (.register 2) (.register 6))
      (.allocate 6 (.pair (.register 1) (.register 6))
        (.allocate 6 (.pair (.register 0) (.register 6))
          (.allocate 7 (.pair (.register 6) (.register 5)) (.ret [.register 7])))))

theorem safe_pair {h : Heap} (hh : Valid h) {a b : Ptr} (ha : a < h.length) (hb : b < h.length) :
    Extends h (h ++ [.pair a b]) ∧ Valid (h ++ [.pair a b]) := by
  have hs := safe_allocate h hh (.pair a b) (by
    intro p hp
    simp only [Cell.references,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> assumption)
  exact ⟨hs.1,hs.2.1⟩

theorem last_cell (h : Heap) (c : Cell) : (h ++ [c])[h.length]? = some c := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem compiled (code : Code p) {h : Heap} (hh : Valid h) {ctx : WorkContext n}
    {sp ap cp pp dp arp : Ptr} (hs : BitsAt h sp ctx.source) (ha : BitsAt h ap ctx.anchor)
    (hc : BitsAt h cp ctx.current) (hp : BitsAt h pp ctx.parity)
    (hd : WordsAt h dp ctx.digits) (har : ArithmeticAt h arp ctx.arithmetic) :
    ∃ out q, Extends h out ∧ Valid out ∧ ContextAt out q ctx ∧
      Within code h (initialRegisters [.pointer sp,.pointer ap,.pointer cp,.pointer pp,.pointer dp,.pointer arp])
        body [.pointer q] out 43 := by
  have harp : arp < h.length := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hcell,_⟩ := har
    exact List.getElem?_eq_some_iff.mp hcell |>.1
  let h1 := h ++ [.pair pp dp]
  have s1 := safe_pair hh hp.allocated hd.allocated
  have e1 : Extends h h1 := s1.1
  let h2 := h1 ++ [.pair cp h.length]
  have s2 := safe_pair s1.2 (hc.mono e1).allocated (show h.length < h1.length by simp [h1])
  have e2 : Extends h h2 := e1.trans s2.1
  let h3 := h2 ++ [.pair ap h1.length]
  have s3 := safe_pair s2.2 (ha.mono e2).allocated (show h1.length < h2.length by simp [h2])
  have e3 : Extends h h3 := e2.trans s3.1
  let h4 := h3 ++ [.pair sp h2.length]
  have s4 := safe_pair s3.2 (hs.mono e3).allocated (show h2.length < h3.length by simp [h3])
  have e4 : Extends h h4 := e3.trans s4.1
  let h5 := h4 ++ [.pair h3.length arp]
  have s5 := safe_pair s4.2 (show h3.length < h4.length by simp [h4]) (harp.trans_le e4.length_le)
  have e5 : Extends h h5 := e4.trans s5.1
  refine ⟨h5,h4.length,e5,s5.2,?_,?_⟩
  · refine ⟨h3.length,arp,sp,h2.length,ap,h1.length,cp,h.length,pp,dp,?_,?_,?_,?_,?_,
      hs.mono e5,ha.mono e5,hc.mono e5,hp.mono e5,hd.mono e5,har.mono e5⟩
    · simp [h5]
    · exact s5.1.lookup (last_cell h3 (.pair sp h2.length))
    · exact (s4.1.trans s5.1).lookup (last_cell h2 (.pair ap h1.length))
    · exact (s3.1.trans (s4.1.trans s5.1)).lookup (last_cell h1 (.pair cp h.length))
    · exact (s2.1.trans (s3.1.trans (s4.1.trans s5.1))).lookup (last_cell h (.pair pp dp))
  · unfold body
    apply Within.allocate (budget := 35) (c := .pair pp dp)
    · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer]
    · apply Within.allocate (budget := 27) (c := .pair cp h.length)
      · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer]
      · apply Within.allocate (budget := 19) (c := .pair ap h1.length)
        · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer,h1]
        · apply Within.allocate (budget := 11) (c := .pair sp h2.length)
          · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer,h1,h2]
          · apply Within.allocate (budget := 3) (c := .pair h3.length arp)
            · simp [CellExpr.eval,Atom.eval,initialRegisters,Value.asPointer,h1,h2,h3]
            · simpa [values,Atom.eval,h1,h2,h3,h4,h5,List.append_assoc] using
                Within.ret code h5
                  (Function.update (Function.update (Function.update (Function.update (Function.update
                    (initialRegisters [.pointer sp,.pointer ap,.pointer cp,.pointer pp,.pointer dp,.pointer arp])
                      6 (.pointer h.length)) 6 (.pointer h1.length)) 6 (.pointer h2.length))
                      6 (.pointer h3.length)) 7 (.pointer h4.length)) [.register 7]

end WeightedMIS.RegisterContextPack
