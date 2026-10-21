module

public import WeightedMIS.EfficientSearchPointerEvaluation

/-! # Authentic heap traces of the fixed search evaluator -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.Pointer

open WeightedMIS.PointerMemory

theorem controls_exec (h : Heap) (n : ℕ) : HeapExec h (List.replicate n .control) h := by
  induction n with
  | zero => exact .nil h
  | succ n ih => exact .cons (.control h) ih

theorem ReadPairEval.exec {h : Heap} {p : Ptr} {r : Run (Option (Ptr × Ptr))}
    (he : ReadPairEval h p r) : HeapExec h r.trace r.heap := by
  cases he
  exact readBefore_exec _ _

theorem EmptyListEval.exec {h : Heap} {p : Ptr} {r : Run (Option Bool)}
    (he : EmptyListEval h p r) : HeapExec h r.trace r.heap := by
  cases he <;> exact readBefore_exec _ _

theorem LookupEmptyEval.exec {h : Heap} {key tree : Ptr} {r : Run (Option Bool)}
    (he : LookupEmptyEval h key tree r) : HeapExec h r.trace r.heap := by
  cases he with
  | inspect lookup found inspect => exact lookup.exec.append inspect.exec

theorem extendCandidate_exec (h : Heap) (vertex path arc target : Ptr) :
    HeapExec h (extendCandidate vertex path arc target h).trace
      (extendCandidate vertex path arc target h).heap := by
  exact ((allocate_exec h (.pair vertex arc)).append
    (allocate_exec _ (.cons h.length path))).append (allocate_exec _ (.pair target (h ++ [Cell.pair vertex arc]).length))

theorem PushEdgeEval.exec {h : Heap} {vertex path distance arc queue : Ptr}
    {r : Run (Option (Ptr × Bool))} (he : PushEdgeEval h vertex path distance arc queue r) :
    HeapExec h r.trace r.heap := by
  cases he with
  | push arcCell weightCell addition insertion =>
    exact .cons (.control h) ((((load_exec _ _).append (load_exec _ _)).append
      addition.exec).append (extendCandidate_exec _ _ _ _ _) |>.append insertion.exec)

theorem RelaxEval.exec {h : Heap} {vertex path distance edges queue : Ptr}
    {r : Run (Option (Ptr × Bool))} (he : RelaxEval h vertex path distance edges queue r) :
    HeapExec h r.trace r.heap := by
  induction he with
  | nil => exact (controls_exec _ 2).append (load_exec _ _)
  | cons cell edge value next ih =>
    exact (((controls_exec _ 2).append (load_exec _ _)).append edge.exec).append ih

theorem FreshEval.exec {h : Heap} {graph vertex path distance queue settled : Ptr}
    {r : Run (Option FreshValue)} (he : FreshEval h graph vertex path distance queue settled r) :
    HeapExec h r.trace r.heap := by
  cases he with
  | expand insertion insertValue lookup lookupValue relax =>
    exact .cons (.control h) ((((allocate_exec h (.pair distance path)).append
      insertion.exec).append lookup.exec).append relax.exec)

theorem SearchEval.exec {h : Heap} {graph queue settled : Ptr} {r : Run (Option SearchRecord)}
    (he : SearchEval h graph queue settled r) : HeapExec h r.trace r.heap := by
  induction he with
  | finished heapValid pop empty => exact (controls_exec _ 3).append pop.exec
  | stale heapValid pop popValue read readValue lookup knownValue next ih =>
    exact ((((controls_exec _ 3).append pop.exec).append read.exec).append lookup.exec).append ih
  | overflow heapValid pop popValue read readValue lookup knownValue expand freshValue =>
    exact ((((controls_exec _ 3).append pop.exec).append read.exec).append lookup.exec).append expand.exec
  | advance heapValid pop popValue read readValue lookup knownValue expand freshValue next ih =>
    exact (((((controls_exec _ 3).append pop.exec).append read.exec).append lookup.exec).append expand.exec).append ih

end WeightedMIS.EfficientSearch.Pointer
