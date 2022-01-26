import tactic

/-- Formulas of propositional logic, 
`Form` ::= `⦃x⦄` | `𝔽` | `¬ Form` | `Form ∧ Form` | `Form ∨ Form` -/
inductive Form (vars : Type) : Type
| Bottom : Form
| Var    : vars → Form
| Not    : Form → Form
| And    : Form → Form → Form
| Or     : Form → Form → Form

notation `𝔽`        := Form.Bottom
notation `⦃` a `⦄`  := Form.Var a
notation `~` a     := Form.Not a
notation a ` ⋀ ` b := Form.And a b
notation a ` ⋁ ` b := Form.Or a b

variables {vars : Type} {Γ : list (Form vars)} {A B C : Form vars}

/-- Gentzen-style (Proof Tree) Natural Deduction for `Form` -/
inductive Deriv : list (Form vars) → Form vars → Prop
| Bottom_E  : ∀ {Γ : list (Form vars)} {A : Form vars},
              Deriv Γ 𝔽 → Deriv Γ A
| Ax        : ∀ {Γ : list (Form vars)} {A : Form vars},
              A ∈ Γ → Deriv Γ A
| Not_I     : ∀ {Γ : list (Form vars)} {A : Form vars}, 
              Deriv (A :: Γ) 𝔽 → Deriv Γ (~ A)
| Not_E     : ∀ {Γ : list (Form vars)} {A : Form vars}, 
              Deriv Γ (~ A) → Deriv Γ A → Deriv Γ 𝔽
| And_I     : ∀ {Γ : list (Form vars)} {A B : Form vars}, 
              Deriv Γ A → Deriv Γ B → Deriv Γ (A ⋀ B)
| And_E_1   : ∀ {Γ : list (Form vars)} {A B : Form vars}, 
              Deriv Γ (A ⋀ B) → Deriv Γ A
| And_E_2   : ∀ {Γ : list (Form vars)} {A B : Form vars}, 
              Deriv Γ (A ⋀ B) → Deriv Γ B
| Or_I_1    : ∀ {Γ : list (Form vars)} {A B : Form vars}, 
              Deriv Γ A → Deriv Γ (A ⋁ B)
| Or_I_2    : ∀ {Γ : list (Form vars)} {A B : Form vars}, 
              Deriv Γ B → Deriv Γ (A ⋁ B)
| Or_E      : ∀ {Γ : list (Form vars)} {A B C : Form vars}, 
              Deriv Γ (A ⋁ B) → Deriv (A :: Γ) C → Deriv (B :: Γ) C 
              → Deriv Γ C
| Contra    : ∀ {Γ : list (Form vars)} {A : Form vars}, 
              Deriv ((~ A) :: Γ) 𝔽 → Deriv Γ A

notation Γ ` ⊩ ` A := Deriv Γ A
notation Γ ` ⊮ ` A := ¬ Deriv Γ A

def inconsistent {vars : Type} (Γ : list (Form vars)) : Prop := Γ ⊩ 𝔽 
def consistent {vars : Type} (Γ : list (Form vars)) : Prop :=  Γ ⊮ 𝔽 

/-- An example derivation:
(Ax) ---------  --------- (Ax)
     A, B ⊩ A   A, B ⊩ B
    --------------------- (⋀I)
         A, B ⊩ A ⋀ B
-/
example : [A, B] ⊩ (A ⋀ B) :=
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

def eval (v : vars → bool) : Form vars → bool
| 𝔽 := false
| ⦃x⦄ := v x
| (~ P) := not (eval P)
| (P ⋀ Q) := and (eval P) (eval Q)
| (P ⋁ Q) := or (eval P) (eval Q)

notation `⟦` P `⟧_` v := eval v P
notation v ` ⊨ ` A := ⟦A⟧_v
notation v ` ⊨ ` Γ := ∀ γ, γ ∈ Γ → ⟦γ⟧_v

theorem no_bottom (v : vars → bool) : ¬ (↥(v ⊨ 𝔽)) :=
by simp [eval]

def entail (Γ : list (Form vars)) (A : Form vars) : Prop :=
∀ (v : vars → bool), (v ⊨ Γ) → (v ⊨ A)

notation Γ ` ⊨ ` A := entail Γ A
notation Γ ` ⊭ ` A := ¬ entail Γ A

@[simp] def satisfiable (Γ : list (Form vars)) : Prop :=
∃ (v : vars → bool), v ⊨ Γ
@[simp] def unsatisfiable (Γ : list (Form vars)) : Prop :=
¬ satisfiable Γ

theorem satisfiable_iff (Γ : list (Form vars)) 
                      : satisfiable Γ ↔ (Γ ⊭ 𝔽) :=
by simp [satisfiable, entail, eval]

theorem unsatisfiable_iff (Γ : list (Form vars)) 
                        : unsatisfiable Γ ↔ (Γ ⊨ 𝔽) :=
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

------------------------------------------------------
-- Main Theorems: soundness & completeness theorems --
------------------------------------------------------

theorem soundness {vars : Type} {Γ : list (Form vars)} {A : Form vars} : 
                  (Γ ⊩ A) → (Γ ⊨ A) :=
begin
  -- induce on the structure of the derivation
  -- but before that we unwrap definitions and introduce hypotheses
  -- to avoid repeating the process in each case
  intro deriv,
  rw entail,
  intros v hΓ,
  induction deriv,
  case Deriv.Bottom_E : Γ A h ih {
   -- the ih can be used to derive falsehood, from which anything follows
   specialize ih hΓ,
   simp [eval] at ih,
   exfalso,
   exact ih,
  },
  case Deriv.Ax : Γ A h {
   exact hΓ A h,
  },
  case Deriv.Not_I : Γ A h ih {
   -- see what the goal really is (when simplified) first
   simp [eval],
   -- we need A to evaluate to truth in order to use the ih,
   -- so try to prove by contradiction as it assumes exactly this
   by_contra hA,
   simp at hA,
   -- use the ih: we first have to prove the precedent in the
   -- exactly required form
   have : ∀ (γ : Form vars), γ ∈ A :: Γ → (↥⟦γ⟧_ v),
   { -- either γ is A or its in Γ
     intros γ hγ,
     simp at hγ, cases hγ,
     {rw hγ, exact hA}, -- in the former case, we use hA
     {exact hΓ γ hγ}    -- in the latter case, we use hΓ
   },
   specialize ih this,
   -- now the evaluation of the ih is really just falsehood, exactly what we 
   -- need
   simp [eval] at ih,
   exact ih
  },
  case Deriv.Not_E : Γ A h₁ h₂ ih₁ ih₂ {
   -- ih₁ and ih₂ have contradicting antecedents, so we first obtain those
   specialize ih₁ hΓ,
   specialize ih₂ hΓ,
   simp [eval] at ih₁ ih₂ ⊢,
   -- form the contradiction to obtain falsehood
   rw ih₁ at ih₂,
   simp at ih₂,
   exact ih₂
  },
  case Deriv.And_I : Γ A B h₁ h₂ ih₁ ih₂ {
   -- similar to case above, but we make A ⋀ B instead of a contradiction 
   specialize ih₁ hΓ,
   specialize ih₂ hΓ,
   simp [eval] at ⊢,
   exact ⟨ih₁, ih₂⟩
  },
  case Deriv.And_E_1 : Γ A B h ih {
   -- take out the truth of A from the truth of A and B
   specialize ih hΓ,
   simp [eval] at ih,
   cases ih with ih₁ ih₂,
   exact ih₁
  },
  case Deriv.And_E_2 : Γ A B h ih {
   -- As in the previous case, but we want B
   specialize ih hΓ,
   simp [eval] at ih,
   cases ih with ih₁ ih₂,
   exact ih₂
  },
  case Deriv.Or_I_1 : Γ A B h ih {
   specialize ih hΓ,
   simp [eval],
   left,
   exact ih
  },
  case Deriv.Or_I_2 : Γ A B h ih {
   specialize ih hΓ,
   simp [eval],
   right,
   exact ih
  },
  case Deriv.Or_E : Γ A B C h h₁ h₂ ih ih₁ ih₂ {
   -- the antecedent of ih₁ and ih₂ both are the goal we want,
   -- but we cannot apply them directly as this would require proving that A 
   -- (respectively B) evaluates to true. This we cannot do. Instead use ih 
   -- to obtain the A ⋁ B, which allows an analysis by cases.
   specialize ih hΓ,
   simp [eval] at ih,
   cases ih,
   -- from here, we can use ih₁ in the first case and ih₂ in the second.
   {
     apply ih₁,
     intros γ hγ,
     cases hγ,
     {rw hγ, exact ih}, -- if γ = A
     {exact hΓ γ hγ}    -- if γ in Γ
   },
   {
     apply ih₂,
     intros γ hγ,
     cases hγ,
     {rw hγ, exact ih}, -- if γ = A
     {exact hΓ γ hγ}    -- if γ in Γ
   },
  },
  case Deriv.Contra : Γ A h ih {
   -- as with Not_I, we need a proof by contradiction.
   -- the structure of the proof is very similar.
   by_contra hA,
   simp [eval] at hA,
   have : ∀ (γ : Form vars), γ ∈ (~ A) :: Γ → (↥⟦γ⟧_ v),
   {
     intros γ hγ,
     simp at hγ, cases hγ,
     {rw hγ, simp [eval], exact hA},
     {exact hΓ γ hγ}
   },
   specialize ih this, simp [eval] at ih,
   exact ih
  },
end  

def soundness' {vars : Type} (Γ : list (Form vars)) : 
               satisfiable Γ → consistent Γ :=
begin
  rw [consistent, satisfiable_iff],
  intro hsat,
  -- suppose towards a contradiction that Γ is inconsistent, so Γ ⊩ 𝔽
  by_contra hcon,
  -- by the soundness theorem, Γ ⊨ 𝔽, which contradicts Γ being satisfiable
  have : (Γ ⊨ 𝔽) := soundness hcon,
  exact hsat this
end

def completeness' {vars : Type} {Γ : list (Form vars)} : 
                  consistent Γ → satisfiable Γ := 
begin
  rw [consistent, satisfiable_iff],
  sorry
end

def completeness {vars : Type} (Γ : list (Form vars)) (A : Form vars) : 
                 (Γ ⊨ A) → (Γ ⊩ A) :=
begin
  intro hA,
  have : ¬ satisfiable ((~ A) :: Γ), {
    rw [satisfiable_iff, entail], simp,
    intros v hnA hΓ,
    -- since hA : Γ ⊨ A, and hΓ : v ⊨ Γ, then also v ⊨ A
    specialize hA v hΓ,
    -- but this contradicts with the fact that hnA : v ⊨ ~ A
    -- which allows us to prove falsehood
    simp [eval] at hnA,
    simp [hnA] at hA,
    -- but falsehood is equivalent to entailing 𝔽, 
    -- which is exactly what we need
    simp [eval],
    exact hA
  },
  -- By the completeness' theorem, we can conclude that (~ A) :: Γ is 
  -- inconsistent, so (~ A) :: Γ ⊩ 𝔽.
  have : ¬ consistent ((~ A) :: Γ) := mt completeness' this,
  simp [consistent] at this,
  -- Applying the Contra derivation step, we find exactly what we need.
  exact Deriv.Contra this
end