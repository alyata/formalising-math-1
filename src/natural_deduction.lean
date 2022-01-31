import formula

variable {vars : Type}

/-- Gentzen-style (Proof Tree) Natural Deduction -/
inductive Deriv : set (Form vars) → Form vars → Prop
| Bottom_E  : ∀ {Γ : set (Form vars)} {A : Form vars},
              Deriv Γ ⊥ → Deriv Γ A
| Ax        : ∀ {Γ : set (Form vars)} {A : Form vars},
              A ∈ Γ → Deriv Γ A
| Not_I     : ∀ {Γ : set (Form vars)} {A : Form vars}, 
              Deriv (insert A Γ) ⊥ → Deriv Γ (~ A)
| Not_E     : ∀ {Γ : set (Form vars)} {A : Form vars}, 
              Deriv Γ (~ A) → Deriv Γ A → Deriv Γ ⊥
| And_I     : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ A → Deriv Γ B → Deriv Γ (A ⋀ B)
| And_E_1   : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ (A ⋀ B) → Deriv Γ A
| And_E_2   : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ (A ⋀ B) → Deriv Γ B
| Or_I_1    : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ A → Deriv Γ (A ⋁ B)
| Or_I_2    : ∀ {Γ : set (Form vars)} {A B : Form vars}, 
              Deriv Γ B → Deriv Γ (A ⋁ B)
| Or_E      : ∀ {Γ : set (Form vars)} {A B C : Form vars}, 
              Deriv Γ (A ⋁ B) → Deriv (insert A Γ) C → Deriv (insert B Γ) C 
              → Deriv Γ C
| Contra    : ∀ {Γ : set (Form vars)} {A : Form vars}, 
              Deriv (insert (~ A) Γ) ⊥ → Deriv Γ A

open Deriv

notation Γ ` ⊩ ` A := Deriv Γ A
notation Γ ` ⊮ ` A := ¬ Deriv Γ A

def inconsistent (Γ : set (Form vars)) : Prop := Γ ⊩ ⊥ 
def consistent   (Γ : set (Form vars)) : Prop := Γ ⊮ ⊥

/-- An example derivation:
(Ax) ---------  --------- (Ax)
     A, B ⊩ A   A, B ⊩ B
    --------------------- (⋀I)
         A, B ⊩ A ⋀ B
-/
example {A B : Form vars} : {A, B} ⊩ (A ⋀ B) :=
begin
  apply Deriv.And_I,
  {
    apply Deriv.Ax,
    simp,
  },
  {
    apply Deriv.Ax,
    simp
  }
end

#lint