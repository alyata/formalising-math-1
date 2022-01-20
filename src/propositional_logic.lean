import tactic

inductive Form (vars : Type) : Type
| Bottom : Form
| Var    : vars → Form
| Not    : Form → Form
| And    : Form → Form → Form
| Or     : Form → Form → Form

notation `⊥`       := Form.Bottom
notation `|` a `|` := Form.Var a
notation `~` a     := Form.Not a
notation a ` ⋀ ` b   := Form.And a b
notation a ` ⋁ ` b   := Form.Or a b

inductive Deriv {vars : Type} : list (Form vars) → Form vars → Prop
| Bottom_E  : ∀ {Γ : list (Form vars)} {A : Form vars},
              Deriv Γ ⊥ → Deriv Γ A
| Ax        : ∀ {Γ : list (Form vars)} {A : Form vars},
              A ∈ Γ → Deriv Γ A
| Not_I     : ∀ {Γ : list (Form vars)} {A : Form vars}, 
              Deriv (A :: Γ) ⊥ → Deriv Γ (~ A)
| Not_E     : ∀ {Γ : list (Form vars)} {A : Form vars}, 
              Deriv Γ (~ A) → Deriv Γ A → Deriv Γ ⊥
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
              Deriv ((~ A) :: Γ) ⊥ → Deriv Γ A

notation Γ ` ⊩ ` A := Deriv Γ A

/-
   A   B
  ------- (⋀I)
   A ⋀ B
-/
example {vars : Type} (A B : Form vars) : [A, B] ⊩ (A ⋀ B) :=
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

def eval {vars : Type} (v : vars → bool) : Form vars → bool
| ⊥ := false
| |x| := v x
| (~ P) := not (eval P)
| (P ⋀ Q) := and (eval P) (eval Q)
| (P ⋁ Q) := or (eval P) (eval Q)

notation `⟦` P `⟧_` v := eval v P

def entail {vars : Type} (Γ : list (Form vars)) (A : Form vars) : Prop :=
∀ (v : vars → bool), (∀ γ, γ ∈ Γ → ⟦γ⟧_v) → ⟦A⟧_v

notation Γ ` ⊨ ` A := entail Γ A

theorem soundness {vars : Type} (Γ : list (Form vars)) (A : Form vars) : 
                  (Γ ⊩ A) → (Γ ⊨ A) :=
begin
  -- induce on the structure of the derivation
  -- but before that we unwrap definitions and introduce hypotheses
  -- to avoid repeating in each case
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
   -- now the evaluation of the ih is really just falsehood, exactly what we need
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

def completeness {vars : Type} (Γ : list (Form vars)) (A : Form vars) : 
                 (Γ ⊨ A) → (Γ ⊩ A) :=
begin
  sorry
end