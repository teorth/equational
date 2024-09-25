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

theorem Equation2_not_implies_Equation3 : ∃ (G: Type) (hG: Magma G), @Equation2 G hG ∧ ¬ @Equation3 G hG := by
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

theorem Equation3_not_implies_Equation7 : ∃ (G: Type) (hG: Magma G), @Equation3 G hG ∧ ¬ @Equation7 G hG := by
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

theorem Equation3_not_implies_Equation5 : ∃ (G: Type) (hG: Magma G), @Equation3 G hG ∧ ¬ @Equation5 G hG := by
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

theorem Equation7_not_implies_Equation6 : ∃ (G: Type) (hG: Magma G), @Equation7 G hG ∧ ¬ @Equation6 G hG := by
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

theorem Equation7_not_implies_Equation10 : ∃ (G: Type) (hG: Magma G), @Equation7 G hG ∧ ¬ @Equation10 G hG := by
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
