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
| Weakening : ∀ {Γ Γ' : set (Form vars)} {A : Form vars},
              (Γ ⊆ Γ') → (Deriv Γ A) → (Deriv Γ' A)

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

-- def compact_set [∀ (Γ : set (Form vars)) A, decidable (A ∈ Γ)] 
--   : ∀ {Γ : set (Form vars)} {A}, (Γ ⊩ A) → set (Form vars)
-- | Γ A (Deriv.Bottom_E h) := compact_set h
-- | Γ A (Deriv.Ax _) := {A}
-- | Γ (~ A) (Deriv.Not_I h) := if A ∈ Γ then compact_set h else compact_set h \ {A}
-- | Γ ⊥ (Deriv.Not_E hnA hA) := compact_set hnA ∪ compact_set hA 
-- | Γ (A ⋀ B) (Deriv.And_I hA hB) := compact_set hA ∪ compact_set hB 
-- | Γ A (Deriv.And_E_1 hAB) := compact_set hAB 
-- | Γ B (Deriv.And_E_2 hAB) := compact_set hAB
-- | Γ (A ⋁ B) (Deriv.Or_I_1 hA) := compact_set hA
-- | Γ (A ⋁ B) (Deriv.Or_I_2 hB) := compact_set hB
-- | Γ C (Deriv.Or_E hAB hAC hBC) := sorry
-- | Γ A (Deriv.Contra h) := if (~ A) ∈ Γ then compact_set h else compact_set h \ {~ A}
-- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd.snd⟩]}

def deriv_compactness [∀ (Γ : set (Form vars)) A, decidable (A ∈ Γ)] 
{Γ : set (Form vars)} {A} (h : Γ ⊩ A) 
  : ∃ Γ', Γ' ⊆ Γ ∧ Γ'.finite ∧ (Γ' ⊩ A) :=
begin
  --use compact_set h,
  induction h,
  case Deriv.Bottom_E : Γ A _ ih {
    rcases ih with ⟨Γ', hsub, hfin, hbot⟩,
    use Γ', use hsub, use hfin,
    use Deriv.Bottom_E hbot,
  },
  case Deriv.Ax : Γ A h {
    use {A},
    split, { simp, use h },
    split, { simp },
    { apply Deriv.Ax, simp }
  },
  case Deriv.Not_I : Γ A _ ih {
    rcases ih with ⟨Γ', hsub, hfin, hbot⟩,
    use Γ' \ {A}, -- we need to remove the assumption added by the Not_I rule
    refine ⟨_, _, _⟩,
    { simp, exact hsub },
    { exact set.finite.subset hfin (set.diff_subset Γ' {A}) },
    { apply Deriv.Not_I, simp, exact Deriv.Weakening (by simp : Γ' ⊆ insert A Γ') hbot }
  },
  case Deriv.Not_E : Γ A _ _ ihnA ihA {
    rcases ihnA with ⟨ΓnA, hnAsub, hnAfin, hnA⟩,
    rcases ihA with ⟨ΓA, hAsub, hAfin, hA⟩,
    use ΓnA ∪ ΓA,
    refine ⟨_, _, _⟩,
    { simp [hnAsub, hAsub] },
    { simp [hnAfin, hAfin] },
    { apply Deriv.Not_E,
      exact Deriv.Weakening (by simp) hnA,
      exact Deriv.Weakening (by simp) hA },
  },
  case Deriv.And_I : Γ A B _ _ ihA ihB {
    rcases ihA with ⟨ΓA, hAsub, hAfin, hA⟩,
    rcases ihB with ⟨ΓB, hBsub, hBfin, hB⟩,
    use ΓA ∪ ΓB,
    refine ⟨_, _, _⟩,
    { simp [hAsub, hBsub] },
    { simp [hAfin, hBfin] },
    { apply Deriv.And_I,
      exact Deriv.Weakening (by simp) hA,
      exact Deriv.Weakening (by simp) hB },
  },
  case Deriv.And_E_1 : Γ A B _ ih {
    rcases ih with ⟨Γ', hsub, hfin, hA⟩,
    use Γ', use hsub, use hfin,
    use Deriv.And_E_1 hA
  },
  case Deriv.And_E_2 : Γ A B _ ih {
    rcases ih with ⟨Γ', hsub, hfin, hB⟩,
    use Γ', use hsub, use hfin,
    use Deriv.And_E_2 hB
  },
  case Deriv.Or_I_1 : Γ A B _ ih {
    rcases ih with ⟨Γ', hsub, hfin, hA⟩,
    use Γ', use hsub, use hfin,
    use Deriv.Or_I_1 hA
  },
  case Deriv.Or_I_2 : Γ A B _ ih {
    rcases ih with ⟨Γ', hsub, hfin, hB⟩,
    use Γ', use hsub, use hfin,
    use Deriv.Or_I_2 hB
  },
  case Deriv.Or_E : Γ A B C _ _ _ ihAB ihAC ihBC {
    rcases ihAB with ⟨ΓAB, hABsub, hABfin, hAB⟩,
    rcases ihAC with ⟨ΓAC, hACsub, hACfin, hAC⟩,
    rcases ihBC with ⟨ΓBC, hBCsub, hBCfin, hBC⟩,
    -- all the assumptions used except for the ones added by the Or_E rule.
    use ΓAB ∪ ((ΓAC \ {A}) ∪ (ΓBC \ {B})),
    refine ⟨_, _, _⟩,
    { simp, exact ⟨hABsub, hACsub, hBCsub⟩ },
    { simp, 
      exact ⟨hABfin, 
             set.finite.subset hACfin (set.diff_subset ΓAC {A}), 
             set.finite.subset hBCfin (set.diff_subset ΓBC {B})⟩ },
    { apply Deriv.Or_E,
      { exact Deriv.Weakening (set.subset_union_left _ _) hAB },
      { rw [←set.union_insert, ←set.insert_union, set.insert_diff_singleton],
        refine Deriv.Weakening _ hAC,
        apply set.subset_union_of_subset_right,
        apply set.subset_union_of_subset_left,
        exact set.subset_insert A ΓAC },
      { rw [←set.union_insert, ←set.union_insert, set.insert_diff_singleton],
        refine Deriv.Weakening _ hBC,
        apply set.subset_union_of_subset_right,
        apply set.subset_union_of_subset_right,
        exact set.subset_insert B ΓBC }
    }
  },
  case Deriv.Contra : Γ A _ ih {
    -- similar to Not_I
    rcases ih with ⟨Γ', hsub, hfin, hbot⟩,
    use Γ' \ {~ A},
    refine ⟨_, _, _⟩,
    { simp, exact hsub },
    { exact set.finite.subset hfin (set.diff_subset Γ' {~ A}) },
    { apply Deriv.Contra, 
      simp, 
      exact Deriv.Weakening (by simp : Γ' ⊆ insert (~ A) Γ') hbot }
  },
  case Deriv.Weakening : Γ SΓ A hsub _ ih {
    rcases ih with ⟨Γ', hsub', hfin, hA⟩,
    use Γ', use trans hsub' hsub, use hfin,
    use hA
  }
end

theorem deriv_compactness' [∀ (Γ : set (Form vars)) A, decidable (A ∈ Γ)] 
{Γ : set (Form vars)} (hfincon : ∀ (Δ : set (Form vars)), Δ ⊆ Γ → Δ.finite → consistent Δ) 
  : consistent Γ :=
begin
  have := mt deriv_compactness,
  simp at this,
  exact this hfincon,
  exact _inst_1 -- not sure why it cannot resolve this typeclass
end

#lint