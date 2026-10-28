/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.FiniteProb

/-!
# Independence in finite product spaces

Two facts about the product spaces of `PseudorandomLib.FiniteProb`:

* `pProb_forall_of_disjoint`: events determined by pairwise disjoint sets of coordinates are
  independent;
* `pProb_comp_injective`: reading the coordinates along an injective map gives the pulled-back
  product law.

Both come from splitting the coordinates along a predicate (`pE_split`).
-/

@[expose] public section

namespace MoserTardos

open Finset Pseudorandom

variable {κ α : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] {Q : κ → α → ℝ}

/-- Expectation in a product space, with the coordinates split along a predicate. -/
theorem pE_split (p : κ → Prop) [DecidablePred p] (F : (κ → α) → ℝ) :
    pE Q F = ∑ a : ({k // p k} → α), ∑ b : ({k // ¬ p k} → α),
      ((∏ k : {k // p k}, Q k (a k)) * ∏ k : {k // ¬ p k}, Q k (b k)) *
        F ((Equiv.piEquivPiSubtypeProd p (fun _ => α)).symm (a, b)) := by
  unfold pE pw
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => α)) _ _ fun T => ?_
  simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  congr 1
  exact (Fintype.prod_subtype_mul_prod_subtype p (fun k => Q k (T k))).symm

theorem sum_prod_subtype (hQ : IsPMF Q) (p : κ → Prop) [DecidablePred p] :
    ∑ a : ({k // p k} → α), ∏ k : {k // p k}, Q k (a k) = 1 := by
  rw [← Fintype.prod_sum (fun (k : {k // p k}) (x : α) => Q k x)]
  exact prod_eq_one fun k _ => hQ.2 k

/-- Functions of disjoint sets of coordinates are uncorrelated. -/
theorem pE_mul_of_split (hQ : IsPMF Q) (p : κ → Prop) [DecidablePred p] (f g : (κ → α) → ℝ)
    (hf : ∀ T T', (∀ k, p k → T k = T' k) → f T = f T')
    (hg : ∀ T T', (∀ k, ¬ p k → T k = T' k) → g T = g T') :
    pE Q (fun T => f T * g T) = pE Q f * pE Q g := by
  rcases isEmpty_or_nonempty (κ → α) with h | h
  · simp [pE]
  obtain ⟨T₀⟩ := h
  obtain ⟨fA, hfA⟩ : ∃ fA : ({k // p k} → α) → ℝ, ∀ a b, f ((Equiv.piEquivPiSubtypeProd p (fun _ => α)).symm (a, b)) = fA a :=
    ⟨fun a => f ((Equiv.piEquivPiSubtypeProd p (fun _ => α)).symm (a, ((Equiv.piEquivPiSubtypeProd p (fun _ => α)) T₀).2)), fun a b => hf _ _ fun k hk => by simp [hk]⟩
  obtain ⟨gB, hgB⟩ : ∃ gB : ({k // ¬ p k} → α) → ℝ, ∀ a b, g ((Equiv.piEquivPiSubtypeProd p (fun _ => α)).symm (a, b)) = gB b :=
    ⟨fun b => g ((Equiv.piEquivPiSubtypeProd p (fun _ => α)).symm (((Equiv.piEquivPiSubtypeProd p (fun _ => α)) T₀).1, b)), fun a b => hg _ _ fun k hk => by simp [hk]⟩
  rw [pE_split p, pE_split (Q := Q) p f, pE_split (Q := Q) p g]
  simp only [hfA, hgB]
  have hA := sum_prod_subtype hQ p
  have hB := sum_prod_subtype hQ (fun k => ¬ p k)
  have e1 : ∑ a : ({k // p k} → α), ∑ b : ({k // ¬ p k} → α),
      ((∏ k : {k // p k}, Q k (a k)) * ∏ k : {k // ¬ p k}, Q k (b k)) * (fA a * gB b) =
      (∑ a : ({k // p k} → α), (∏ k : {k // p k}, Q k (a k)) * fA a) *
        ∑ b : ({k // ¬ p k} → α), (∏ k : {k // ¬ p k}, Q k (b k)) * gB b := by
    rw [Finset.sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have e2 : ∑ a : ({k // p k} → α), ∑ b : ({k // ¬ p k} → α),
      ((∏ k : {k // p k}, Q k (a k)) * ∏ k : {k // ¬ p k}, Q k (b k)) * fA a =
      (∑ a : ({k // p k} → α), (∏ k : {k // p k}, Q k (a k)) * fA a) *
        ∑ b : ({k // ¬ p k} → α), ∏ k : {k // ¬ p k}, Q k (b k) := by
    rw [Finset.sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have e3 : ∑ a : ({k // p k} → α), ∑ b : ({k // ¬ p k} → α),
      ((∏ k : {k // p k}, Q k (a k)) * ∏ k : {k // ¬ p k}, Q k (b k)) * gB b =
      (∑ a : ({k // p k} → α), ∏ k : {k // p k}, Q k (a k)) *
        ∑ b : ({k // ¬ p k} → α), (∏ k : {k // ¬ p k}, Q k (b k)) * gB b := by
    rw [Finset.sum_mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [e1, e2, e3, hA, hB]
  ring

open Classical in
/-- **Independence.** Events determined by pairwise disjoint sets of coordinates are
independent. -/
theorem pProb_forall_of_disjoint (hQ : IsPMF Q) {V : Type*} (S : Finset V) (C : V → Finset κ)
    (hC : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → Disjoint (C v) (C w)) (A : V → (κ → α) → Prop)
    (hA : ∀ v T T', (∀ k ∈ C v, T k = T' k) → (A v T ↔ A v T')) :
    pProb Q (fun T => ∀ v ∈ S, A v T) = ∏ v ∈ S, pProb Q (A v) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [prod_empty, pProb_eq_pE _ (fun _ => 1) (fun _ _ => rfl) (fun _ h => absurd (by simp) h),
      pE_const hQ]
  | insert a S ha ih =>
    rw [prod_insert ha, ← ih fun v hv w hw => hC v (mem_insert_of_mem hv) w (mem_insert_of_mem hw)]
    have hsplit := pE_mul_of_split hQ (· ∈ C a) (fun T => if A a T then (1 : ℝ) else 0)
      (fun T => if ∀ v ∈ S, A v T then (1 : ℝ) else 0)
      (fun T T' h => by simp only [hA a T T' h])
      (fun T T' h => by
        have : (∀ v ∈ S, A v T) ↔ (∀ v ∈ S, A v T') := forall₂_congr fun v hv =>
          hA v T T' fun k hk => h k fun hka =>
            disjoint_left.1 (hC a (mem_insert_self a S) v (mem_insert_of_mem hv)
              (fun hav => ha (hav ▸ hv))) hka hk
        simp only [this])
    rw [pProb_eq_pE _ (fun T => (if A a T then (1 : ℝ) else 0) *
        (if ∀ v ∈ S, A v T then (1 : ℝ) else 0)), hsplit,
      ← pProb_eq_pE (A a) _ (fun T h => if_pos h) (fun T h => if_neg h),
      ← pProb_eq_pE (fun T => ∀ v ∈ S, A v T) _ (fun T h => if_pos h) (fun T h => if_neg h)]
    · intro T h
      rw [if_pos (h a (mem_insert_self a S)), if_pos fun v hv => h v (mem_insert_of_mem hv),
        mul_one]
    · intro T h
      by_cases h1 : A a T
      · rw [if_pos h1, one_mul, if_neg]
        intro h2
        exact h fun v hv => (mem_insert.1 hv).elim (fun e => e ▸ h1) (h2 v)
      · rw [if_neg h1, zero_mul]

/-- Reading the coordinates along an injective map gives the pulled-back product law. -/
theorem pProb_comp_injective {ι : Type*} [Fintype ι] [DecidableEq ι] (hQ : IsPMF Q)
    (g : ι → κ) (hg : Function.Injective g) (S : (ι → α) → Prop) :
    pProb Q (fun T => S (T ∘ g)) = pProb (fun i => Q (g i)) S := by
  classical
  let p : κ → Prop := fun k => ∃ i, g i = k
  let e' : ι ≃ {k // p k} :=
    { toFun := fun i => ⟨g i, i, rfl⟩
      invFun := fun r => Classical.choose r.2
      left_inv := fun i => hg (Classical.choose_spec (⟨i, rfl⟩ : ∃ i', g i' = g i))
      right_inv := fun r => Subtype.ext (Classical.choose_spec r.2) }
  rw [pProb_equiv e' (fun i => Q (g i)) S]
  have hQe : (fun r : {k // p k} => Q (g (e'.symm r))) = fun r => Q r.1 := by
    funext r
    have := congrArg Subtype.val (e'.apply_symm_apply r)
    exact congrArg Q this
  rw [hQe]
  unfold pProb
  rw [pE_split p]
  have hF : ∀ (a : {k // p k} → α) (b : {k // ¬ p k} → α),
      (if S ((Equiv.piEquivPiSubtypeProd p (fun _ => α)).symm (a, b) ∘ g)
        then (1 : ℝ) else 0) = if S (a ∘ e') then 1 else 0 := by
    intro a b
    have : (Equiv.piEquivPiSubtypeProd p (fun _ => α)).symm (a, b) ∘ g = a ∘ e' := by
      funext i
      show (if h : p (g i) then a ⟨g i, h⟩ else b ⟨g i, h⟩) = a ⟨g i, i, rfl⟩
      rw [dif_pos ⟨i, rfl⟩]
    rw [this]
  simp only [hF]
  have hB := sum_prod_subtype hQ (fun k => ¬ p k)
  unfold pE pw
  refine sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum, hB, mul_one]

end MoserTardos
