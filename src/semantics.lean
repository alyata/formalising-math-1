import formula

variable {vars : Type}

/-- Evaluates formulas to truth values given a propositional variable 
    truth assignment
-/
def eval (v : vars → bool) : Form vars → bool
| ⊥       := false
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

@[simp] def satisfiable (Γ : set (Form vars)) : Prop :=
∃ (v : vars → bool), v ⊨ Γ
@[simp] def unsatisfiable (Γ : set (Form vars)) : Prop :=
¬ satisfiable Γ

variable {Γ : set (Form vars)}

theorem satisfiable_iff : satisfiable Γ ↔ (Γ ⊭ ⊥) :=
by simp [satisfiable, entail, eval]

theorem unsatisfiable_iff : unsatisfiable Γ ↔ (Γ ⊨ ⊥) :=
begin
  simp [eval, entail],
  split,
  {
    intros h v hΓ,
    rcases h v with ⟨γ, hin, hγ⟩,
    specialize hΓ γ hin,
    simp [hγ] at hΓ,
    exact hΓ
  },
  {
    intros h v,
    specialize h v,
    by_contra h',
    simp at h',
    apply h,
    intros γ hin,
    specialize h' γ hin,
    simp [h'],
  }
end

#lint