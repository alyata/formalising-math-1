import form
import natural_deduction
import semantics

------------------------------------------------------
-- Main Theorems: soundness & completeness theorems --
------------------------------------------------------

variables {vars : Type} [denumerable vars] {Γ : set (Form vars)} {A B C : Form vars}

theorem soundness : (Γ ⊩ A) → (Γ ⊨ A) :=
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
   have : ∀ (γ : Form vars), γ ∈ (insert A Γ) → (↥⟦γ⟧_ v),
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
   have : ∀ (γ : Form vars), γ ∈ (insert (~ A) Γ) → (↥⟦γ⟧_ v),
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

theorem soundness' : satisfiable Γ → consistent Γ :=
begin
  rw [consistent, satisfiable_iff],
  intro hsat,
  -- suppose towards a contradiction that Γ is inconsistent, so Γ ⊩ ⊥
  by_contra hcon,
  -- by the soundness theorem, Γ ⊨ ⊥, which contradicts Γ being satisfiable
  have : (Γ ⊨ ⊥) := soundness hcon,
  exact hsat this
end

def complete (Γ : set (Form vars)) : Prop := 
  ∀ (A : Form vars), A ∈ Γ ∨ (~ A) ∈ Γ

lemma contradiction_of_deriv_of_neg_nin 
  (hcomp : complete Γ) (hcon : consistent Γ) 
  : (Γ ⊩ A) →  A ∉ Γ → false :=
begin
  intros hdA hAnin,
  have : (~ A) ∈ Γ := (or_iff_right hAnin).mp (hcomp A),
  have hdnA : (Γ ⊩ ~ A) := Deriv.Ax this,
  have hincon : inconsistent Γ := Deriv.Not_E hdnA hdA,
  exact hcon hincon
end

theorem deriv_closure 
  (hcomp : complete Γ) (hcon : consistent Γ) : (Γ ⊩ A) ↔ A ∈ Γ :=
begin
  split,
  {
    intro hdA,
    by_contra hAnin,
    exact contradiction_of_deriv_of_neg_nin hcomp hcon hdA hAnin
  },
  { exact Deriv.Ax }
end

theorem neg_in_iff_not_in
(hcomp : complete Γ) (hcon : consistent Γ) : (~ A) ∈ Γ ↔ A ∉ Γ :=
begin
  split,
  {
    intro hnA, 
    by_contra hA,
    have hincon : inconsistent Γ := Deriv.Not_E (Deriv.Ax hnA) (Deriv.Ax hA),
    exact hcon hincon
  },
  { intro h, exact (or_iff_right h).mp (hcomp A) },
end 

theorem and_in_iff_both_in
  (hcomp : complete Γ) (hcon : consistent Γ) : (A ⋀ B) ∈ Γ ↔ A ∈ Γ ∧ B ∈ Γ :=
begin
  split,
  {
    intro hAB,
    have hdA : (Γ ⊩ A) := Deriv.And_E_1 (Deriv.Ax hAB),
    have hdB : (Γ ⊩ B) := Deriv.And_E_2 (Deriv.Ax hAB),
    split,
    {by_contra hAnin, exact contradiction_of_deriv_of_neg_nin hcomp hcon hdA hAnin},
    {by_contra hBnin, exact contradiction_of_deriv_of_neg_nin hcomp hcon hdB hBnin}
  },
  {
    rintro ⟨hA, hB⟩,
    have hdAB : (Γ ⊩ (A ⋀ B)) := Deriv.And_I (Deriv.Ax hA) (Deriv.Ax hB),
    by_contra hABnin,
    exact contradiction_of_deriv_of_neg_nin hcomp hcon hdAB hABnin
  }
end

theorem or_in_iff_either_in
  (hcomp : complete Γ) (hcon : consistent Γ) : (A ⋁ B) ∈ Γ ↔ A ∈ Γ ∨ B ∈ Γ :=
begin
  split,
  {
    intro hAB,
    by_contra h,
    rw [not_or_distrib] at h,
    cases h with hAnin hBnin,
    have hnAin : (~ A) ∈ Γ := (or_iff_right hAnin).mp (hcomp A),
    have hnBin : (~ B) ∈ Γ := (or_iff_right hBnin).mp (hcomp B),

    /- The derivation:
                  (Ax)----------- (Ax)----------   (Ax)----------- (Ax)----------
                      Γ, A ⊩ ~ A      Γ, A ⊩ A        Γ, B ⊩ ~ B      Γ, B ⊩ B
  (Ax)---------- (~E)---------------------------   (~E)--------------------------
      Γ ⊩ A ⋁ B             Γ, A ⊩ ⊥                        Γ, B ⊩ ⊥ 
      ---------------------------------------------------------------------------
                                    Γ ⊩ ⊥
    -/
    have hincon : (inconsistent Γ), {
      apply Deriv.Or_E,
      { exact Deriv.Ax hAB },
      { apply Deriv.Not_E, 
        exact Deriv.Ax (or.intro_right _ hnAin),
        exact Deriv.Ax (or.intro_left _ rfl)},
      {
        apply Deriv.Not_E, 
        exact Deriv.Ax (or.intro_right _ hnBin),
        exact Deriv.Ax (or.intro_left _ rfl)
      }
    },
    exact hcon hincon
  },
  {
    intro h,
    rw ←deriv_closure hcomp hcon,
    cases h with hA hB,
    { exact Deriv.Or_I_1 (Deriv.Ax hA) },
    { exact Deriv.Or_I_2 (Deriv.Ax hB) }
  }
end

/-- Let Γ be a consistent set of formulas. 

Using the denumeration A₀, A₁, ... of all formulas, define the following sets 
inductively:

 Γ₀ = Γ

 Γₙ₊₁ = if consistent (insert Aₙ Γₙ) then insert Aₙ Γₙ else insert (~ Aₙ) Γₙ
  -/
def lindenbaum_fn (Γ : set (Form vars)) (hcon : consistent Γ) 
  [∀ (Γ : set (Form vars)), decidable (consistent Γ)] : ℕ → set (Form vars)
| 0 := Γ
| (n + 1) := 
let Aₙ := denumerable.of_nat (Form vars) n in
if consistent (insert Aₙ (lindenbaum_fn n)) 
then insert Aₙ (lindenbaum_fn n) 
else insert (~ Aₙ) (lindenbaum_fn n)

lemma lindenbaum_fn_consistent {Γ : set (Form vars)} {hcon : consistent Γ}
  [∀ (Γ : set (Form vars)), decidable (consistent Γ)]
  : ∀ n, consistent (lindenbaum_fn Γ hcon n) :=
begin
  intro n,
  induction n,
  case nat.zero { exact hcon },
  case nat.succ : k ih {
    simp [lindenbaum_fn],
    simp [apply_ite consistent 
          (consistent (insert (denumerable.of_nat (Form vars) k) (lindenbaum_fn Γ hcon k)))
          (insert (denumerable.of_nat (Form vars) k) (lindenbaum_fn Γ hcon k))
          (insert (~ (denumerable.of_nat (Form vars) k)) (lindenbaum_fn Γ hcon k))],
    by_cases hc : consistent (insert (denumerable.of_nat (Form vars) k) (lindenbaum_fn Γ hcon k)),
    -- if inserting A is consistent, then goal immediately follows.
    { rw if_pos hc, exact hc },
    -- if inserting A is inconsistent, then we prove by contradiction since if
    -- inserting A or ~ A are both inconsistent, then we can show it is 
    -- already inconsistent before insertion, thus contradicting the ih.
    { rw if_neg hc, by_contra hnc, simp [consistent] at hc hnc, 
      exact ih (Deriv.Not_E (Deriv.Not_I hnc) (Deriv.Not_I hc)),
    }
  }
end

lemma lindenbaum_lemma (Γ : set (Form vars)) (hcon : consistent Γ) 
  [∀ (Γ : set (Form vars)), decidable (consistent Γ)] 
  : ∃ CΓ, Γ ⊆ CΓ ∧ complete CΓ ∧ consistent CΓ :=
begin -- Check out Zorn's Lemma
  refine ⟨⋃ (i : ℕ), (lindenbaum_fn Γ hcon i), _, _, _⟩,
  -- Γ ⊆ CΓ
  { exact set.subset_Union (lindenbaum_fn Γ hcon) 0 },
  -- complete CΓ
  { rw complete, intro A,
    have : A ∈ lindenbaum_fn Γ hcon (encodable.encode A + 1) ∨
       (~ A) ∈ lindenbaum_fn Γ hcon (encodable.encode A + 1), {
      simp [lindenbaum_fn],
      -- we can simplify using apply_ite, but the apply_ite itself needs to be
      -- simplified before it is applicable
      have apply_mem_A, from
      apply_ite (λΓ, A ∈ Γ) 
                (consistent (insert A (lindenbaum_fn Γ hcon (encodable.encode A))))
                (insert A (lindenbaum_fn Γ hcon (encodable.encode A)))
                (insert (~ A) (lindenbaum_fn Γ hcon (encodable.encode A))),
      have apply_mem_nA, from
      apply_ite (λΓ, (~ A) ∈ Γ) 
                (consistent (insert A (lindenbaum_fn Γ hcon (encodable.encode A))))
                (insert A (lindenbaum_fn Γ hcon (encodable.encode A)))
                (insert (~ A) (lindenbaum_fn Γ hcon (encodable.encode A))),
      simp at apply_mem_A apply_mem_nA,
      rw [apply_mem_A, apply_mem_nA],
      -- part of the goal is to show either the set is consistent or 
      -- inconsistent, which can be shown by the law of excluded middle
      by_cases hc : consistent (insert A (lindenbaum_fn Γ hcon (encodable.encode A))),
      {left, left, exact hc}, {right, left, exact hc}
    },
    cases this,
    { left, 
      apply set.mem_of_mem_of_subset this, 
      exact set.subset_Union (lindenbaum_fn Γ hcon) (encodable.encode A + 1) },
    { right,
      apply set.mem_of_mem_of_subset this,
      exact set.subset_Union (lindenbaum_fn Γ hcon) (encodable.encode A + 1) }
  },
  -- consistent CΓ
    { sorry }
end

def lindenbaum_model (CΓ : set (Form vars)) [∀p, decidable (⦃p⦄ ∈ CΓ)]
  (hcomp : complete CΓ) (hcon : consistent CΓ)
  : vars → bool :=
λ p, if ⦃p⦄ ∈ CΓ then true else false

lemma truth_lemma
  (CΓ : set (Form vars)) [∀p, decidable (⦃p⦄ ∈ CΓ)]
  (hcomp : complete CΓ) (hcon : consistent CΓ)
  : ↥(lindenbaum_model CΓ hcomp hcon ⊨ A) ↔ A ∈ CΓ :=
begin
  induction A,
  case Form.Bottom {
    simp [eval],
    rw ←deriv_closure hcomp hcon,
    exact hcon
  },
  case Form.Var {
    simp [eval, lindenbaum_model],
    -- Learning Point: using `set_option pp.notation false` to find out what 
    -- ↥ desugars to, so that the apply_ite theorem can be used
    rw apply_ite coe_sort (⦃A⦄ ∈ CΓ) tt ff,
    simp
  },
  case Form.Not : A ih {
    simp [eval, ih],
    exact (neg_in_iff_not_in hcomp hcon).symm
  },
  case Form.And : A B ihA ihB {
    simp [eval, ihA, ihB],
    exact (and_in_iff_both_in hcomp hcon).symm
  },
  case Form.Or : A B ihA ihB {
    simp [eval, ihA, ihB],
    exact (or_in_iff_either_in hcomp hcon).symm
  },
end

theorem completeness' {Γ : set (Form vars)} : 
                  consistent Γ → satisfiable Γ := 
begin
  -- specifically, we need membership in CΓ to be decidable
  -- and consistency to be decicable
  classical,
  intro hcon,
  -- construct the lindenbaum completion CΓ of Γ
  rcases lindenbaum_lemma Γ hcon with ⟨CΓ, hsuper, hcomp, hcon⟩,
  simp [satisfiable],
  -- build a model out of CΓ
  use lindenbaum_model CΓ hcomp hcon,
  -- for every sentence γ ∈ Γ,
  intros γ hγ,
  -- it is entailed by the model iff γ ∈ CΓ (by the truth lemma)
  rw truth_lemma,
  -- but this is easy to show since Γ ⊆ CΓ
  apply hsuper,
  exact hγ
end

theorem completeness {Γ : set (Form vars)} {A : Form vars} : 
                 (Γ ⊨ A) → (Γ ⊩ A) :=
begin
  intro hA,
  have : ¬ satisfiable (insert (~ A) Γ), {
    rw [satisfiable_iff, entail], simp,
    intros v hnA hΓ,
    -- since hA : Γ ⊨ A, and hΓ : v ⊨ Γ, then also v ⊨ A
    specialize hA v hΓ,
    -- but this contradicts with the fact that hnA : v ⊨ ~ A
    -- which allows us to prove falsehood
    simp [eval] at hnA,
    simp [hnA] at hA,
    -- but falsehood is equivalent to entailing ⊥, 
    -- which is exactly what we need
    simp [eval],
    exact hA
  },
  -- By the completeness' theorem, we can conclude that (~ A) :: Γ is 
  -- inconsistent, so (~ A) :: Γ ⊩ ⊥.
  have : ¬ consistent (insert (~ A) Γ) := mt completeness' this,
  simp [consistent] at this,
  -- Applying the Contra derivation step, we find exactly what we need.
  exact Deriv.Contra this
end