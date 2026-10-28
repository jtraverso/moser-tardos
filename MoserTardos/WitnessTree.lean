/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MoserTardos.GaltonWatson
public import MoserTardos.Indep

/-!
# The `τ`-check

The vertices of a tree `τ : Tr d j` are listed as (label, depth) pairs (`verts`), and the weight of
a tree is the product of `p` over its vertex labels (`weight_eq_prod`). A tree is *good* when its
vertices are distinct and two vertices at the same depth carry labels that are neither equal nor
neighbours; the witness trees built from a run of the algorithm are good.

The `τ`-check (`Check`) reads a table of depth `L`: at each vertex `v`, the variable `i` takes the
table entry `idx v i`, the number of vertices strictly deeper than `v` whose label involves `i`,
and the event labelling `v` must hold. For a good tree the entries read at distinct vertices are
distinct, so the probability that the check passes is at most the weight of the tree
(`pProb_check_le`).
-/

@[expose] public section

namespace MoserTardos

open Finset Pseudorandom

namespace Inst

variable {ι α : Type*} [DecidableEq ι] {n : ℕ} (I : Inst ι α n)

theorem mem_nbrIncl_of_mem_vbl {x y : Fin n} {i : ι} (hx : i ∈ I.vbl x) (hy : i ∈ I.vbl y) :
    x ∈ I.nbrIncl y := by
  unfold nbrIncl
  by_cases h : x = y
  · exact h ▸ mem_insert_self _ _
  · exact mem_insert_of_mem (I.mem_nbr.2 ⟨h, Finset.not_disjoint_iff.2 ⟨i, hy, hx⟩⟩)

theorem mem_nbrIncl_comm {x y : Fin n} : x ∈ I.nbrIncl y → y ∈ I.nbrIncl x := by
  unfold nbrIncl
  intro h
  rcases mem_insert.1 h with h | h
  · exact h ▸ mem_insert_self _ _
  · obtain ⟨hne, hd⟩ := I.mem_nbr.1 h
    exact mem_insert_of_mem (I.mem_nbr.2 ⟨Ne.symm hne, fun h' => hd h'.symm⟩)

/-- The vertices of a tree as (label, depth) pairs, the root at depth `δ`. -/
noncomputable def verts : (d : ℕ) → (j : Fin n) → I.Tr d j → ℕ → Multiset (Fin n × ℕ)
  | 0, _, τ, _ => PEmpty.elim τ
  | d + 1, j, τ, δ => (j, δ) ::ₘ (univ : Finset (I.nbrIncl j)).val.bind fun k =>
      match τ k with
      | none => 0
      | some σ => verts d k σ (δ + 1)

theorem weight_eq_prod (p : Fin n → ℝ) :
    ∀ (d : ℕ) (j : Fin n) (τ : I.Tr d j) (δ : ℕ),
      I.weight p d j τ = ((I.verts d j τ δ).map fun v => p v.1).prod
  | 0, _, τ, _ => PEmpty.elim τ
  | d + 1, j, τ, δ => by
    rw [weight, verts, Multiset.map_cons, Multiset.prod_cons, Multiset.map_bind,
      Multiset.prod_bind]
    congr 1
    rw [Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun k _ => ?_
    rcases h : τ k with _ | σ
    · simp
    · exact weight_eq_prod p d k σ (δ + 1)

/-- A tree is *good* when its vertices are distinct and two vertices at the same depth have
labels that are neither equal nor neighbours. -/
def Good {d : ℕ} {j : Fin n} (τ : I.Tr d j) : Prop :=
  (I.verts d j τ 0).Nodup ∧ ∀ v ∈ I.verts d j τ 0, ∀ w ∈ I.verts d j τ 0, v ≠ w → v.2 = w.2 →
    v.1 ∉ I.nbrIncl w.1

/-- The table index read for the variable `i` at the vertex `v`: the number of vertices strictly
deeper than `v` whose label involves `i`. -/
def idx (V : Finset (Fin n × ℕ)) (v : Fin n × ℕ) (i : ι) : ℕ :=
  (V.filter fun w => v.2 < w.2 ∧ i ∈ I.vbl w.1).card

/-- The `τ`-check on a table of depth `L`: the tree is good, has at most `L` vertices, and at each
vertex `v` the event labelling `v` holds when each variable `i` takes the table entry
`idx v i`. -/
def Check (a₀ : α) {L d : ℕ} {j : Fin n} (τ : I.Tr d j) (T : ι × Fin L → α) : Prop :=
  I.Good τ ∧ Multiset.card (I.verts d j τ 0) ≤ L ∧
    ∀ v ∈ I.verts d j τ 0, I.ev v.1 fun i => extend a₀ T i (I.idx (I.verts d j τ 0).toFinset v i)

theorem idx_lt_idx {V : Finset (Fin n × ℕ)} {v w : Fin n × ℕ} (hw : w ∈ V) (hvw : v.2 < w.2)
    {i : ι} (hi : i ∈ I.vbl w.1) : I.idx V w i < I.idx V v i := by
  unfold idx
  refine card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨w, ?_, ?_⟩)
  · intro x hx
    obtain ⟨hx, h1, h2⟩ := mem_filter.1 hx
    exact mem_filter.2 ⟨hx, hvw.trans h1, h2⟩
  · exact mem_filter.2 ⟨hw, hvw, hi⟩
  · simp

theorem idx_lt_card {V : Finset (Fin n × ℕ)} {v : Fin n × ℕ} (hv : v ∈ V) (i : ι) :
    I.idx V v i < V.card := by
  unfold idx
  refine card_lt_card ((Finset.ssubset_iff_of_subset (filter_subset _ _)).2 ⟨v, hv, ?_⟩)
  simp

end Inst

theorem tableLaw_isPMF {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}
    (hP : IsPMF P) (L : ℕ) : IsPMF (tableLaw P L) :=
  ⟨fun e a => hP.1 e.1 a, fun e => hP.2 e.1⟩

namespace Inst

variable {ι α : Type*} [DecidableEq ι] {n : ℕ} (I : Inst ι α n)

/-- **The `τ`-check is unlikely.** The probability that a tree passes the check on a random
table is at most its weight. -/
theorem pProb_check_le [Fintype ι] [Fintype α] {P : ι → α → ℝ} (hP : IsPMF P) (a₀ : α) (L : ℕ)
    {d : ℕ} {j : Fin n} (τ : I.Tr d j) :
    pProb (tableLaw P L) (I.Check a₀ τ) ≤ I.weight (fun k => pProb P (I.ev k)) d j τ := by
  classical
  have hPL := tableLaw_isPMF hP L
  have hw0 : 0 ≤ I.weight (fun k => pProb P (I.ev k)) d j τ :=
    I.weight_nonneg (fun k => pProb_nonneg hP _) d j τ
  by_cases hG : I.Good τ ∧ Multiset.card (I.verts d j τ 0) ≤ L
  swap
  · rw [pProb_eq_pE _ (fun _ => 0) (fun T h => absurd ⟨h.1, h.2.1⟩ hG) (fun _ _ => rfl)]
    simpa [pE] using hw0
  obtain ⟨⟨hnd, hsame⟩, hL⟩ := hG
  set V := I.verts d j τ 0 with hV
  set F := V.toFinset with hF
  have hFL : F.card ≤ L := (Multiset.toFinset_card_le V).trans hL
  have hlt : ∀ v ∈ F, ∀ i, I.idx F v i < L := fun v hv i => (I.idx_lt_card hv i).trans_le hFL
  -- the event at a vertex, and the table entries it reads
  let A : Fin n × ℕ → (ι × Fin L → α) → Prop := fun v T =>
    I.ev v.1 fun i => extend a₀ T i (I.idx F v i)
  let C : Fin n × ℕ → Finset (ι × Fin L) := fun v =>
    univ.filter fun e => e.1 ∈ I.vbl v.1 ∧ (e.2 : ℕ) = I.idx F v e.1
  have hA : ∀ v T T', (∀ e ∈ C v, T e = T' e) → (A v T ↔ A v T') := by
    intro v T T' h
    refine I.dep v.1 _ _ fun i hi => ?_
    unfold extend
    split_ifs with hk
    · exact h _ (mem_filter.2 ⟨mem_univ _, hi, rfl⟩)
    · rfl
  have hC : ∀ v ∈ F, ∀ w ∈ F, v ≠ w → Disjoint (C v) (C w) := by
    intro v hv w hw hne
    refine disjoint_left.2 fun e hev hew => ?_
    obtain ⟨-, hiv, hev⟩ := mem_filter.1 hev
    obtain ⟨-, hiw, hew⟩ := mem_filter.1 hew
    rcases lt_trichotomy v.2 w.2 with h | h | h
    · have := I.idx_lt_idx hw h hiw
      omega
    · exact hsame v (Multiset.mem_toFinset.1 hv) w (Multiset.mem_toFinset.1 hw) hne h
        (I.mem_nbrIncl_of_mem_vbl hiv hiw)
    · have := I.idx_lt_idx hv h hiv
      omega
  have hcheck : ∀ T, I.Check a₀ τ T ↔ ∀ v ∈ F, A v T := by
    intro T
    refine ⟨fun h v hv => h.2.2 v (Multiset.mem_toFinset.1 hv), fun h =>
      ⟨⟨hnd, hsame⟩, hL, fun v hv => h v (Multiset.mem_toFinset.2 hv)⟩⟩
  rw [pProb_congr hcheck, pProb_forall_of_disjoint hPL F C hC A hA,
    I.weight_eq_prod _ d j τ 0, ← hV, Finset.prod_eq_multiset_prod, hF, Multiset.toFinset_val,
    hnd.dedup]
  refine le_of_eq (congrArg Multiset.prod (Multiset.map_congr rfl fun v hv => ?_))
  have hvF : v ∈ F := Multiset.mem_toFinset.2 hv
  let g : ι → ι × Fin L := fun i => (i, ⟨I.idx F v i, hlt v hvF i⟩)
  have hg : Function.Injective g := fun i i' h => congrArg Prod.fst h
  have hAg : ∀ T, A v T ↔ I.ev v.1 (T ∘ g) := by
    intro T
    refine I.dep v.1 _ _ fun i _ => ?_
    simp only [extend, Function.comp_apply, g, dif_pos (hlt v hvF i)]
  rw [pProb_congr hAg, pProb_comp_injective hPL g hg]
  rfl

end Inst

end MoserTardos
