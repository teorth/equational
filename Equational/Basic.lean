import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/

def Equation1 (G: Type*) [Magma G] := ∀ x y : G, x = y

def Equation2 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ w

def Equation3 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x

def Equation4 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = y ∘ x

def Equation5 (G: Type*) [Magma G] := ∀ x y z w u v: G, x ∘ (y ∘ z) = (w ∘ u) ∘ v

def Equation6 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ z

def Equation7 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ x

def Equation8 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u

def Equation9 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ y) ∘ w

def Equation10 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ z

def Equation11 (G: Type*) [Magma G] := ∀ x : G, x = x



/- Positive implications -/

theorem Equation1_implies_Equation2 (G: Type*) [Magma G] (h: Equation1 G) : Equation2 G :=
  fun _ _ _ _ => h _ _

theorem Equation1_implies_Equation3 (G: Type*) [Magma G] (h: Equation1 G) : Equation3 G :=
  fun _ _ => h _ _

theorem Equation2_implies_Equation4 (G: Type*) [Magma G] (h: Equation2 G) : Equation4 G :=
  fun _ _ => h _ _ _ _

theorem Equation2_implies_Equation5 (G: Type*) [Magma G] (h: Equation2 G) : Equation5 G :=
  fun _ _ _ _ _ _ => h _ _ _ _

theorem Equation2_implies_Equation6 (G: Type*) [Magma G] (h: Equation2 G) : Equation6 G :=
  fun _ _ _ => h _ _ _ _

theorem Equation3_implies_Equation6 (G: Type*) [Magma G] (h: Equation3 G) : Equation6 G := by
  intro _ _ _
  rw [h, h]

theorem Equation3_implies_Equation8 (G: Type*) [Magma G] (h: Equation3 G) : Equation8 G := by
  intro x y z w u
  rw [h y z, h x w, h x y, h x u]

/-- This proof is from https://mathoverflow.net/a/450905/766 -/
theorem Equation4_implies_Equation7 (G: Type*) [Magma G] (h: Equation4 G) : Equation7 G := by
  have idem (x : G) : (x ∘ x) ∘ (x ∘ x) = (x ∘ x) := by
    rw [h x (x ∘ x), h x x]
  have comm (x y : G) : (x ∘ x) ∘ y = y ∘ (x ∘ x) := by
    rw [<-idem x, h (x ∘ x) y, idem x]
  have op_idem (x y : G) : (x ∘ x) ∘ (y ∘ y) = x ∘ y := by
    rw [h x (y ∘ y), h y x]
  intro x y
  rw [<- op_idem x y, comm x (y ∘ y), op_idem y x]

theorem Equation5_implies_Equation8 (G: Type*) [Magma G] (h: Equation5 G) : Equation8 G :=
  fun _ _ _ _ _ => h _ _ _ _ _ _

theorem Equation8_implies_Equation9 (G: Type*) [Magma G] (h: Equation8 G) : Equation9 G :=
  fun _ _ _ _ => h _ _ _ _ _

theorem Equation9_implies_Equation10 (G: Type*) [Magma G] (h: Equation9 G) : Equation10 G :=
  fun _ _ _ => h _ _ _ _

theorem Equation11_true (G: Type*) [Magma G] : Equation11 G :=
  fun _ => rfl



/- Counterexamples -/

theorem Equation2_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation2 G ∧ ¬ Equation3 G := by
  let hG : Magma Nat := {
    op := fun _ _ => 0
  }
  use ℕ, hG
  constructor
  . intro _ _ _ _
    rfl
  by_contra h
  replace h := h 1 0
  dsimp [hG] at h
  linarith

theorem Equation3_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation5 G := by
  let hG : Magma Nat := {
    op := fun x _ => x
  }
  use ℕ, hG
  constructor
  . intro _ _
    rfl
  by_contra h
  replace h := h 0 0 0 1 0 0
  dsimp [hG] at h
  linarith

theorem Equation3_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation7 G := by
  let hG : Magma Nat := {
    op := fun x _ => x
  }
  use ℕ, hG
  constructor
  . intro _ _
    rfl
  by_contra h
  replace h := h 1 0
  dsimp [hG] at h
  linarith

theorem Equation5_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation6 G := by
  let hG : Magma Nat := {
    op := fun x y => if x = 0 ∧ y = 0 then 1 else 2
  }
  use ℕ, hG
  constructor
  . intro x y z w u v
    simp [hG]
    calc
      _ = 2 := by
        by_cases h' : y = 0 ∧ z = 0
        . simp [h']
        simp [h']
      _ = _ := by
        by_cases h' : w = 0 ∧ u = 0
        . simp [h']
        simp [h']
  by_contra h
  replace h := h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation5_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation7 G := by
  let hG : Magma Nat := {
    op := fun x y => if x = 1 ∧ y = 2 then 3 else 4
  }
  use ℕ, hG
  constructor
  . intro x y z w u v
    simp [hG]
    calc
      _ = 4 := by
        by_cases h' : y = 1 ∧ z = 2
        . simp [h']
        simp [h']
      _ = _ := by
        by_cases h' : w = 1 ∧ u = 2
        . simp [h']
        simp [h']
  by_contra h
  replace h := h 1 2
  dsimp [hG] at h
  linarith

theorem Equation6_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation6 G ∧ ¬ Equation7 G := by
  let hG : Magma Nat := {
    op := fun x _ => x
  }
  use ℕ, hG
  constructor
  . intro _ _ _
    simp [hG]
  by_contra h
  replace h := h 0 1
  dsimp [hG] at h
  linarith

theorem Equation6_not_implies_Equation10 : ∃ (G: Type) (_: Magma G), Equation6 G ∧ ¬ Equation10 G := by
  let hG : Magma Nat := {
    op := fun x _ => x + 1
  }
  use ℕ, hG
  constructor
  . intro _ _ _
    simp [hG]
  by_contra h
  replace h := h 0 0 0
  dsimp [hG] at h
  linarith

theorem Equation7_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation7 G ∧ ¬ Equation6 G := by
  let hG : Magma Nat := {
    op := fun x y => x+y
  }
  use ℕ, hG
  constructor
  . exact Nat.add_comm
  by_contra h
  replace h := h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation7_not_implies_Equation10 : ∃ (G: Type) (_: Magma G), Equation7 G ∧ ¬ Equation10 G := by
  let hG : Magma Nat := {
    op := fun x y => x * y + 1
  }
  use ℕ, hG
  constructor
  . intro x y
    dsimp [hG]
    ring
  by_contra h
  replace h := h 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation9_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation9 G ∧ ¬ Equation8 G := by
  let hG : Magma Nat := {
    op := fun x y => if x = 0 then (if y ≤ 2 then 1 else 2) else x
  }
  use ℕ, hG
  constructor
  . intro x y z w
    by_cases h : x = 0
    . simp [hG, h]
      have : ¬ (if y ≤ 2 then 1 else 2) = 0 := by
        by_cases h' : y ≤ 2
        . simp [h']
        simp [h']
      simp [this]
      congr 1
      by_cases h0 : y = 0
      . simp [h0]
        by_cases hz : z ≤ 2
        . simp [hz]
        simp [hz]
      by_cases h' : y ≤ 2
      . simp [h0, h']
      simp [h', h0]
    simp [hG, h]
  by_contra h
  replace h := h 0 0 0 3 3
  dsimp [hG] at h
  linarith

theorem Equation10_not_implies_Equation9 : ∃ (G: Type) (_: Magma G), Equation10 G ∧ ¬ Equation9 G := by
  let hG : Magma Nat := {
    op := fun x y => x + y
  }
  use ℕ, hG
  constructor
  . intro x y z
    simp [hG]
    abel
  by_contra h
  replace h := h 0 0 0 1
  dsimp [hG] at h
  linarith

theorem Equation10_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation10 G ∧ ¬ Equation6 G := by
  let hG : Magma Nat := {
    op := fun x y => x + y
  }
  use ℕ, hG
  constructor
  . intro x y z
    simp [hG]
    abel
  by_contra h
  replace h := h 0 0 1
  dsimp [hG] at h
  linarith
