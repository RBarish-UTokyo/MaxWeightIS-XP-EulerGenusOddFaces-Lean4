module

public import WeightedMIS.FiniteCycleEnumeration

/-! # First-unseen enumeration with a shared front extension of the seen list -/

@[expose] public section

namespace WeightedMIS.FiniteCycleEnumeration

variable {α : Type*} [DecidableEq α]

/-- The seen block is prepended so the finite heap program shares its old tail. -/
def frontRepresentatives (block : α → List α) (seen : List α) : List α → List α
  | [] => []
  | x :: rest => if x ∈ seen then frontRepresentatives block seen rest
      else x :: frontRepresentatives block (block x ++ seen) rest

/-- Changing the order of seen entries does not change the deterministic roots. -/
theorem frontRepresentatives_eq (block : α → List α) (seen seen' order : List α)
    (hs : ∀ x, x ∈ seen ↔ x ∈ seen') :
    frontRepresentatives block seen order = representatives block seen' order := by
  induction order generalizing seen seen' with
  | nil => rfl
  | cons x order ih =>
    by_cases hx : x ∈ seen
    · have hx' := (hs x).mp hx
      simpa only [frontRepresentatives, representatives, if_pos hx, if_pos hx'] using ih seen seen' hs
    · have hx' : x ∉ seen' := fun h => hx ((hs x).mpr h)
      simp only [frontRepresentatives, representatives, if_neg hx, if_neg hx']
      congr 1
      apply ih
      intro y
      simp only [List.mem_append]
      rw [hs y]
      exact or_comm

theorem frontRepresentatives_self (block : α → List α) (seen order : List α) :
    frontRepresentatives block seen order = representatives block seen order :=
  frontRepresentatives_eq block seen seen order (fun _ => Iff.rfl)

end WeightedMIS.FiniteCycleEnumeration
