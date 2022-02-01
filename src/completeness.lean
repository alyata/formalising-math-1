
import natural_deduction
import semantics

variables {vars : Type} {Γ : set (Form vars)} {A B C : Form vars}

/-- A complete set of formulas contains, for every formula A, either A 
or its negation.

Note: this is a different use of the word from the "completeness theorem",
which pertains to the derivation and semantic system, not to sets.
-/
def complete (Γ : set (Form vars)) : Prop := 
  ∀ (A : Form vars), A ∈ Γ ∨ (~ A) ∈ Γ

/-- Let Γ be a set of formulas (we will also require Γ be consistent but this 
is asserted in the corresponding theorem lindenbaum_fn_consistent and 
lindenbaum_lemma).

Using the denumeration A₀, A₁, ... of all formulas, define the following sequence
of sets inductively:

 Γ₀ = Γ

 Γₙ₊₁ = if consistent (insert Aₙ Γₙ) then insert Aₙ Γₙ else insert (~ Aₙ) Γₙ
-/
def lindenbaum_fn (Γ : set (Form vars)) [denumerable vars]
  [∀ (Γ : set (Form vars)), decidable (consistent Γ)] : ℕ → set (Form vars)
| 0 := Γ
| (n + 1) := 
let Aₙ := denumerable.of_nat (Form vars) n in
if consistent (insert Aₙ (lindenbaum_fn n)) 
then insert Aₙ (lindenbaum_fn n) 
else insert (~ Aₙ) (lindenbaum_fn n)

/-- Each of the Γₙ defined above are consistent if the source set Γ is consistent -/
lemma lindenbaum_fn_consistent {Γ : set (Form vars)} {hcon : consistent Γ}
  [denumerable vars] [∀ (Γ : set (Form vars)), decidable (consistent Γ)]
  : ∀ n, consistent (lindenbaum_fn Γ n) :=
begin
  intro n,
  induction n,
  -- Γ₀ = Γ is consistent by assumption
  case nat.zero { exact hcon },
  case nat.succ : k ih {
    simp [lindenbaum_fn, apply_ite consistent],
    set A  := denumerable.of_nat (Form vars) k,
    set Γₖ := lindenbaum_fn Γ k,
    by_cases hc : consistent (insert A Γₖ),
    -- if inserting A is consistent, then the goal immediately follows.
    { rw if_pos hc, exact hc },
    -- if inserting A is inconsistent, then we prove by contradiction since if
    -- inserting A or ~ A are both inconsistent, then we can show it is 
    -- already inconsistent before insertion, thus contradicting the ih.
    { rw if_neg hc, by_contra hnc, simp [consistent] at hc hnc, 
      exact ih (Deriv.Not_E (Deriv.Not_I hnc) (Deriv.Not_I hc)),
    }
  }
end

/-- Using the sequence of sets defined above -/
lemma lindenbaum_lemma (Γ : set (Form vars)) (hcon : consistent Γ) 
  [denumerable vars] [∀ (Γ : set (Form vars)), decidable (consistent Γ)] 
  : ∃ CΓ, Γ ⊆ CΓ ∧ complete CΓ ∧ consistent CΓ :=
begin
  refine ⟨⋃ (i : ℕ), (lindenbaum_fn Γ i), _, _, _⟩,
  -- Γ ⊆ CΓ
  { exact set.subset_Union (lindenbaum_fn Γ) 0 },
  -- complete CΓ
  { rw complete, intro A,
    have : A ∈ lindenbaum_fn Γ (encodable.encode A + 1) ∨
       (~ A) ∈ lindenbaum_fn Γ (encodable.encode A + 1), {
      simp [lindenbaum_fn],
      -- we can simplify using apply_ite, but the apply_ite itself needs to be
      -- simplified before it is applicable
      have apply_mem_A, from
      apply_ite (λΓ, A ∈ Γ) 
                (consistent (insert A (lindenbaum_fn Γ (encodable.encode A))))
                (insert A (lindenbaum_fn Γ (encodable.encode A)))
                (insert (~ A) (lindenbaum_fn Γ (encodable.encode A))),
      have apply_mem_nA, from
      apply_ite (λΓ, (~ A) ∈ Γ) 
                (consistent (insert A (lindenbaum_fn Γ (encodable.encode A))))
                (insert A (lindenbaum_fn Γ (encodable.encode A)))
                (insert (~ A) (lindenbaum_fn Γ (encodable.encode A))),
      simp at apply_mem_A apply_mem_nA,
      rw [apply_mem_A, apply_mem_nA],
      -- part of the goal is to show either the set is consistent or 
      -- inconsistent, which can be shown by the law of excluded middle
      by_cases hc : consistent (insert A (lindenbaum_fn Γ (encodable.encode A))),
      {left, left, exact hc}, {right, left, exact hc}
    },
    cases this,
    { left, 
      apply set.mem_of_mem_of_subset this, 
      exact set.subset_Union (lindenbaum_fn Γ) (encodable.encode A + 1) },
    { right,
      apply set.mem_of_mem_of_subset this,
      exact set.subset_Union (lindenbaum_fn Γ) (encodable.encode A + 1) }
  },
  -- consistent CΓ
    { sorry }
end

def lindenbaum_model (CΓ : set (Form vars)) [∀p, decidable (⦃p⦄ ∈ CΓ)]
  : vars → bool :=
λ p, if ⦃p⦄ ∈ CΓ then true else false

lemma contradiction_of_deriv_of_nin 
  (hcomp : complete Γ) (hcon : consistent Γ) 
  : (Γ ⊩ A) →  A ∉ Γ → false :=
begin
  intros hdA hAnin,
  have : (~ A) ∈ Γ := (or_iff_right hAnin).mp (hcomp A),
  have hdnA : (Γ ⊩ ~ A) := Deriv.Ax this,
  have hincon : inconsistent Γ := Deriv.Not_E hdnA hdA,
  exact hcon hincon
end

theorem deriv_iff_in
  (hcomp : complete Γ) (hcon : consistent Γ) : (Γ ⊩ A) ↔ A ∈ Γ :=
begin
  split,
  {
    intro hdA,
    by_contra hAnin,
    exact contradiction_of_deriv_of_nin hcomp hcon hdA hAnin
  },
  { exact Deriv.Ax }
end

lemma truth_lemma
  (CΓ : set (Form vars)) [∀p, decidable (⦃p⦄ ∈ CΓ)]
  (hcomp : complete CΓ) (hcon : consistent CΓ)
  : ↥(lindenbaum_model CΓ ⊨ A) ↔ A ∈ CΓ :=
begin
  induction A,
  case Form.Bottom {
    simp [eval],
    rw ←deriv_iff_in hcomp hcon,
    exact hcon
  },
  case Form.Var {
    simp [eval, lindenbaum_model],
    -- Learning Point: using `set_option pp.notation false` to find out what 
    -- ↥ desugars to (`coe_sort`), so that the apply_ite theorem can be used
    rw apply_ite coe_sort (⦃A⦄ ∈ CΓ) tt ff,
    simp
  },
  case Form.Not : A ih {
    simp [eval, ih],
    split,
    { intro h, exact (or_iff_right h).mp (hcomp A) },
    {
      intro hnA, 
      by_contra hA,
      have hincon : inconsistent CΓ := Deriv.Not_E (Deriv.Ax hnA) (Deriv.Ax hA),
      exact hcon hincon
    },
  },
  case Form.And : A B ihA ihB {
    simp [eval, ihA, ihB],
    split, 
    {
      rintro ⟨hA, hB⟩,
      have hdAB : (CΓ ⊩ (A ⋀ B)) := Deriv.And_I (Deriv.Ax hA) (Deriv.Ax hB),
      by_contra hABnin,
      exact contradiction_of_deriv_of_nin hcomp hcon hdAB hABnin
    },
    {
      intro hAB,
      have hdA : (CΓ ⊩ A) := Deriv.And_E_1 (Deriv.Ax hAB),
      have hdB : (CΓ ⊩ B) := Deriv.And_E_2 (Deriv.Ax hAB),
      split,
      {by_contra hAnin, exact contradiction_of_deriv_of_nin hcomp hcon hdA hAnin},
      {by_contra hBnin, exact contradiction_of_deriv_of_nin hcomp hcon hdB hBnin}
    },
  },
  case Form.Or : A B ihA ihB {
    simp[eval, ihA, ihB],
    split,
    {
      intro h,
      rw ←deriv_iff_in hcomp hcon,
      cases h with hA hB,
      { exact Deriv.Or_I_1 (Deriv.Ax hA) },
      { exact Deriv.Or_I_2 (Deriv.Ax hB) }
    },
    {
      intro hAB,
      by_contra h,
      rw [not_or_distrib] at h,
      cases h with hAnin hBnin,
      have hnAin : (~ A) ∈ CΓ := (or_iff_right hAnin).mp (hcomp A),
      have hnBin : (~ B) ∈ CΓ := (or_iff_right hBnin).mp (hcomp B),

      /- The derivation:
                    (Ax)------------ (Ax)----------   (Ax)----------- (Ax)----------
                        CΓ, A ⊩ ~ A      CΓ, A ⊩ A       CΓ, B ⊩ ~ B     CΓ, B ⊩ B
    (Ax)----------- (~E)---------------------------   (~E)--------------------------
        CΓ ⊩ A ⋁ B             CΓ, A ⊩ ⊥                        CΓ, B ⊩ ⊥ 
        ---------------------------------------------------------------------------
                                      CΓ ⊩ ⊥
      -/
      have hincon : (inconsistent CΓ), {
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
    }
  },
end

theorem completeness' {Γ : set (Form vars)} [denumerable vars]
  : consistent Γ → satisfiable Γ := 
begin
  -- specifically, we need membership in CΓ to be decidable
  -- and consistency of sets of formulas to be decicable
  -- hence we use classical reasoning
  classical,
  intro hcon,
  -- construct the lindenbaum completion CΓ of Γ
  rcases lindenbaum_lemma Γ hcon with ⟨CΓ, hsuper, hcomp, hcon⟩,
  simp [satisfiable],
  -- build a model out of CΓ
  use lindenbaum_model CΓ,
  -- for every sentence γ ∈ Γ,
  intros γ hγ,
  -- it is entailed by the model iff γ ∈ CΓ (by the truth lemma)
  rw truth_lemma CΓ hcomp hcon,
  -- but this is easy to show since Γ ⊆ CΓ
  apply hsuper,
  exact hγ
end

theorem completeness [denumerable vars] {Γ : set (Form vars)} {A : Form vars} 
  : (Γ ⊨ A) → (Γ ⊩ A) :=
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