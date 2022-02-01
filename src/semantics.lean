import formula

variable {vars : Type}

/-- Evaluates formulas to truth values given a propositional variable 
    truth assignment
-/
def eval (v : vars → bool) : Form vars → bool
| ⊥       := ff
| ⦃x⦄     := v x
| (~ P)   := not (eval P)
| (P ⋀ Q) := and (eval P) (eval Q)
| (P ⋁ Q) := or (eval P) (eval Q)

notation `⟦` P `⟧_` v := eval v P
notation v ` ⊨ ` A := ⟦A⟧_v
notation v ` ⊨ ` Γ := ∀ γ, γ ∈ Γ → ⟦γ⟧_v

theorem no_bottom (v : vars → bool) : ¬ (↥(v ⊨ ⊥)) :=
by simp [eval]

def entail (Γ : set (Form vars)) (A : Form vars) : Prop :=
∀ (v : vars → bool), (v ⊨ Γ) → (v ⊨ A)

notation Γ ` ⊨ ` A := entail Γ A
notation Γ ` ⊭ ` A := ¬ entail Γ A

def satisfiable (Γ : set (Form vars)) : Prop :=
∃ (v : vars → bool), v ⊨ Γ
def unsatisfiable (Γ : set (Form vars)) : Prop :=
¬ satisfiable Γ

variable {Γ : set (Form vars)}

theorem satisfiable_iff : satisfiable Γ ↔ (Γ ⊭ ⊥) :=
by simp [satisfiable, entail, eval]

theorem unsatisfiable_iff : unsatisfiable Γ ↔ (Γ ⊨ ⊥) :=
begin
  simp [unsatisfiable, satisfiable_iff],
end

#lint