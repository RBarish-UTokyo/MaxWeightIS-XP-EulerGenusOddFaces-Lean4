module

public import WeightedMIS.PermutationDeletion
public import Mathlib.Tactic.Linarith

/-!
# Deterministic bounded traces and first-unseen orbit representatives

All executable definitions use finite lists, supplied decidable equality, and
actual permutation applications. No quotient representative or classical
choice is evaluated. Representatives are selected by scanning the supplied
order and marking every flag on both orientations of each new boundary.
-/

@[expose] public section

namespace WeightedMIS.FiniteCycleEnumeration

variable {α : Type*}

/-- Follow a function for exactly the supplied number of positions. -/
def trace (f : α → α) : ℕ → α → List α
  | 0, _ => []
  | n + 1, x => x :: trace f n (f x)

@[simp] theorem trace_length (f : α → α) (n : ℕ) (x : α) : (trace f n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [trace, List.length_cons, ih]

/-- A bounded trace contains exactly its actual bounded iterates. -/
theorem mem_trace_iff (f : α → α) (n : ℕ) (x y : α) :
    y ∈ trace f n x ↔ ∃ i < n, f^[i] x = y := by
  induction n generalizing x with
  | zero => simp [trace]
  | succ n ih =>
      simp only [trace, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨i, hi, he⟩)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨i + 1, by omega, by simpa only [Function.iterate_succ_apply] using he⟩
      · rintro ⟨i, hi, he⟩
        cases i with
        | zero => exact Or.inl he.symm
        | succ i => exact Or.inr ⟨i, by omega, by simpa only [Function.iterate_succ_apply] using he⟩

/-- Following a finite permutation for its carrier cardinality reaches every
member of the starting oriented orbit. -/
theorem mem_full_trace_iff [Fintype α] (σ : Equiv.Perm α) (x y : α) :
    y ∈ trace σ (Fintype.card α) x ↔ σ.SameCycle x y := by
  rw [mem_trace_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨(i : ℤ), by simpa only [zpow_natCast, Equiv.Perm.coe_pow] using hi⟩
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
    refine ⟨i % Function.minimalPeriod σ x,
      lt_of_lt_of_le (Nat.mod_lt _ hp) Function.minimalPeriod_le_card, ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq]
    simpa only [Equiv.Perm.coe_pow] using hi

/-- Trace one orientation and then reflect all its actual positions. -/
def bothTrace (σ τ : α → α) (n : ℕ) (x : α) : List α :=
  trace σ n x ++ (trace σ n x).map τ

@[simp] theorem bothTrace_length (σ τ : α → α) (n : ℕ) (x : α) :
    (bothTrace σ τ n x).length = 2 * n := by simp [bothTrace]; omega

/-- The two traced orientations implement the actual unoriented cycle
relation of a reversing involution. -/
theorem mem_bothTrace_iff [Fintype α] (σ : Equiv.Perm α) (τ : α → α)
    (ht : Function.Involutive τ) (x y : α) :
    y ∈ bothTrace σ τ (Fintype.card α) x ↔ σ.SameCycle x y ∨ σ.SameCycle x (τ y) := by
  simp only [bothTrace, List.mem_append, List.mem_map, mem_full_trace_iff]
  constructor
  · rintro (h | ⟨z, hz, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [ht]; exact hz)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨τ y, h, ht y⟩

section Scan

variable [DecidableEq α]

/-- Scan in the supplied deterministic order, tracing a block only at its
first unseen flag. The seen list records exactly the previously traced blocks. -/
def representatives (block : α → List α) : List α → List α → List α
  | _, [] => []
  | seen, x :: xs =>
      if x ∈ seen then representatives block seen xs
      else x :: representatives block (seen ++ block x) xs

/-- Every selected root is a supplied flag. -/
theorem representatives_subset (block : α → List α) (seen order : List α) :
    ∀ x ∈ representatives block seen order, x ∈ order := by
  induction order generalizing seen with
  | nil => simp [representatives]
  | cons y ys ih =>
      intro x hx
      by_cases hy : y ∈ seen
      · simp only [representatives, hy, ite_true] at hx
        exact List.mem_cons_of_mem _ (ih seen x hx)
      · simp only [representatives, hy, ite_false, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (seen ++ block y) x hx)

/-- A selected root has not already been visited. -/
theorem representatives_not_seen (block : α → List α) (seen order : List α) :
    ∀ x ∈ representatives block seen order, x ∉ seen := by
  induction order generalizing seen with
  | nil => simp [representatives]
  | cons y ys ih =>
      intro x hx
      by_cases hy : y ∈ seen
      · simp only [representatives, hy, ite_true] at hx
        exact ih seen x hx
      · simp only [representatives, hy, ite_false, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hy
        · exact fun hm => ih (seen ++ block y) x hx (List.mem_append_left _ hm)

/-- At most one new root is chosen at each outer scan position. -/
theorem representatives_length_le (block : α → List α) (seen order : List α) :
    (representatives block seen order).length ≤ order.length := by
  induction order generalizing seen with
  | nil => simp [representatives]
  | cons x xs ih =>
      by_cases hx : x ∈ seen <;> simp only [representatives, hx, ite_true, ite_false,
        List.length_cons]
      · exact (ih seen).trans (by omega)
      · exact Nat.add_le_add_right (ih _) 1

/-- Every scanned flag is already visited or belongs to an actually selected
root's traced block. -/
theorem representatives_cover (block : α → List α) (hrefl : ∀ x, x ∈ block x)
    (seen order : List α) :
    ∀ y ∈ order, y ∈ seen ∨ ∃ x ∈ representatives block seen order, y ∈ block x := by
  induction order generalizing seen with
  | nil => simp
  | cons z zs ih =>
      intro y hy
      by_cases hz : z ∈ seen
      · simp only [representatives, hz, ite_true]
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl hz
        · exact ih seen y hy
      · simp only [representatives, hz, ite_false]
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inr ⟨y, List.mem_cons_self, hrefl y⟩
        · rcases ih (seen ++ block z) y hy with hy | ⟨x, hx, hy⟩
          · rcases List.mem_append.mp hy with hy | hy
            · exact Or.inl hy
            · exact Or.inr ⟨z, List.mem_cons_self, hy⟩
          · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hy⟩

/-- Distinct selected roots do not belong to the same traced block. -/
theorem representatives_pairwise (block : α → List α) (seen order : List α) :
    (representatives block seen order).Pairwise (fun x y => y ∉ block x) := by
  induction order generalizing seen with
  | nil => simp [representatives]
  | cons x xs ih =>
      by_cases hx : x ∈ seen
      · simpa only [representatives, hx, ite_true] using ih seen
      · simp only [representatives, hx, ite_false, List.pairwise_cons]
        refine ⟨?_, ih _⟩
        intro y hy hm
        exact representatives_not_seen block (seen ++ block x) xs y hy (List.mem_append_right _ hm)

/-- Structural work of the scan: a full membership pass, the actual block
trace, and copying the old visited list when a fresh block is appended. -/
def scanWork (block : α → List α) (blockWork : α → ℕ) : List α → List α → ℕ
  | _, [] => 0
  | seen, x :: xs =>
      seen.length + 1 + if x ∈ seen then scanWork block blockWork seen xs
      else blockWork x + seen.length + 1 + scanWork block blockWork (seen ++ block x) xs

/-- Bounded block traces give a polynomial bound for the complete deterministic
first-unseen scan, including repeated scans of the visited list. -/
theorem scanWork_le (block : α → List α) (blockWork : α → ℕ) (b w : ℕ)
    (hsize : ∀ x, (block x).length ≤ b) (hwork : ∀ x, blockWork x ≤ w)
    (seen order : List α) :
    scanWork block blockWork seen order ≤
      order.length * (2 * seen.length + 2 * b * order.length + w + 2) := by
  induction order generalizing seen with
  | nil => simp [scanWork]
  | cons x xs ih =>
      by_cases hx : x ∈ seen
      · have hi := ih seen
        simp only [scanWork, hx, ite_true, List.length_cons]
        nlinarith
      · have hi := ih (seen ++ block x)
        have hs := hsize x
        have hw := hwork x
        simp only [List.length_append] at hi
        simp only [scanWork, hx, ite_false, List.length_cons]
        nlinarith [Nat.mul_le_mul_left (2 * xs.length) hs]

/-- Explicit work bound for the two-orientation permutation scan. The block
construction follows the orbit once, reflects it once, and appends it once. -/
theorem bothTrace_scanWork_le (σ τ : α → α) (n : ℕ) (order : List α) :
    scanWork (bothTrace σ τ n) (fun _ => 3 * n) [] order ≤
      order.length * (4 * n * order.length + 3 * n + 2) := by
  have h := scanWork_le (bothTrace σ τ n) (fun _ => 3 * n) (2 * n) (3 * n)
    (fun x => by simp) (fun _ => le_rfl) [] order
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at h
  nlinarith

end Scan
end WeightedMIS.FiniteCycleEnumeration
