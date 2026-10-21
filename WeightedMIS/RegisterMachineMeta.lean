module

public import WeightedMIS.RegisterMachineBounds

/-!
# Memory safety and concrete stack execution of closed register programs

All stored, returned, loaded, and saved pointers are proved allocated. Every
procedure call saves exactly the actual sixteen caller registers. The resulting
symbol-stack execution has the same heap trace as the finite-code interpreter
and charges each saved and restored bit.
-/

@[expose] public section

namespace WeightedMIS.RegisterMachine

open WeightedMIS.PointerMemory

/-- Execution preserves valid heaps and bounds all output values by the final
allocated heap. Allocation counts and every traced address are included. -/
theorem Exec.safe {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {command : Command p} {result : Run (List Value)} (he : Exec code h regs command result) :
    Valid h → RegistersBound h.length regs →
      SafeRun h result ∧ ValuesBound result.heap.length result.value := by
  induction he with
  | ret h regs outputs =>
      intro hh hr
      have hv := values_bounded hr (null_allocated hh) outputs
      refine ⟨⟨Extends.refl h, hh, traceBound_control_cons (moves_bound hv), ?_⟩, hv⟩
      simp
  | @copy h regs dst src next result rest ih =>
      intro hh hr
      have hs := src.bounded hr (null_allocated hh)
      obtain ⟨hsafe, hvalue⟩ := ih hh (update_bounded hr dst hs)
      exact ⟨safe_prefix hsafe _ (traceBound_control_cons (Value.moves_bound hs)), hvalue⟩
  | @allocate h regs dst expr c next result evaluated rest ih =>
      intro hh hr
      have hc := CellExpr.fits hr (null_allocated hh) evaluated
      have ha := safe_allocate h hh c hc
      have hbound : RegistersBound (h ++ [c]).length
          (Function.update regs dst (.pointer h.length)) := by
        apply update_bounded (registersBound_mono hr ha.1.length_le)
        simp [Value.Bounded, Value.word, Word.Bounded, Program.allocate]
      obtain ⟨hsafe, hvalue⟩ := ih ha.2.1 hbound
      have hp : (Value.pointer h.length).Bounded (h ++ [c]).length := by
        simp [Value.Bounded, Value.word, Word.Bounded, Program.allocate]
      have hj := safe_join ha (safe_prefix hsafe _ (Value.moves_bound hp))
      have hb := traceBound_control_cons (moves_bound (values_bounded hr (null_allocated hh) expr.args))
      have hall := safe_prefix hj _ hb
      refine ⟨?_, hvalue⟩
      simpa only [withEvents, Program.allocate, List.cons_append, List.append_assoc] using hall
  | @load h regs address addr c first second bit branches result evaluated loaded rest ih =>
      intro hh hr
      have hc : c.Fits h.length := hh.2 addr c loaded
      have hz := null_allocated hh
      have hp : addr < h.length := (List.getElem?_eq_some_iff.mp loaded).1
      have ha := safe_load h hh addr hp
      obtain ⟨hsafe, hvalue⟩ := ih hh (loadRegisters_bounded hr hz hc first second bit)
      have hread : TraceBound [Event.load addr (some c)] h.length := by
        simpa only [Program.load, loaded] using ha.2.2.1
      have hm : (Value.pointer addr).Bounded h.length := hp
      have hb := traceBound_control_cons (traceBound_append (traceBound_append
        (Value.moves_bound hm) hread) (decodedMoves_bound hz hc))
      refine ⟨?_, hvalue⟩
      simpa only [withEvents, List.append_assoc] using safe_prefix hsafe _ hb
  | @branch h regs test b yes no result evaluated rest ih =>
      intro hh hr
      obtain ⟨hsafe, hvalue⟩ := ih hh hr
      have hb : (Value.flag b).Bounded h.length := trivial
      exact ⟨safe_prefix hsafe _ (traceBound_control_cons (Value.moves_bound hb)), hvalue⟩
  | @call h regs procedure arguments results next callee continuation body rest ihbody ihrest =>
      intro hh hr
      have hv := values_bounded hr (null_allocated hh) arguments
      obtain ⟨hc, hcv⟩ := ihbody hh (initialRegisters_bounded (null_allocated hh) hv)
      obtain ⟨hs, hsv⟩ := ihrest hc.2.1
        (bindResults_bounded (registersBound_mono hr hc.1.length_le) hcv)
      exact ⟨safe_prefix (safe_join hc hs) _ (traceBound_control_cons (moves_bound hv)), hsv⟩

end WeightedMIS.RegisterMachine
