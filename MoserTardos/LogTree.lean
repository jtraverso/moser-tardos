/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MoserTardos.WitnessTree

/-!
# Witness trees from the log

Fix a table `T` and a step `s` at which the event `j₀` is resampled. Going back from `s`, a step
`r < s` joins the witness tree of `s` when its event is a neighbour of (or equal to) the event of a
later step already in the tree, and it is attached as deep as possible. We encode this by the
depth `wd T s r : WithBot ℕ` (`⊥` for steps outside the tree), defined by recursion on `s - r` as
the supremum of `wd T s u + 1` over the later steps `u` whose event can sit above the event of
`r`. The parent of a step is the first later step realising its depth (`par`).

* `dp_lt`: a step below a later step of the tree with a neighbouring event is in the tree, and is
  strictly deeper. Hence two vertices of the same depth carry neither equal nor neighbouring
  events, and the tree is good;
* `verts_build`: the typed tree `build` has as vertices exactly the steps of the tree, with their
  events and depths;
* `nres_eq_idx`: when step `u` is checked, the variable `i` of its event has been resampled once
  for each vertex of the tree deeper than `u` whose event involves `i` (the coupling with the
  `τ`-check);
* `check_build`, `build_injective`: the witness tree of a step passes the `τ`-check on the table,
  and different steps resampling `j₀` have different witness trees.
-/

@[expose] public section

namespace MoserTardos

open Finset Pseudorandom

namespace Inst

variable {ι α : Type*} [DecidableEq ι] {n : ℕ} (I : Inst ι α n)

/-! ### The run -/

theorem ev_of_firstViolated {ω : ι → α} {j : Fin n} (h : I.firstViolated ω = some j) :
    I.ev j ω := by
  classical
  unfold firstViolated at h
  by_cases hne : (univ.filter fun j => I.ev j ω).Nonempty
  · rw [dif_pos hne] at h
    obtain rfl := Option.some.inj h
    exact (mem_filter.1 (min'_mem _ hne)).2
  · rw [dif_neg hne] at h
    cases h

theorem ev_of_logAt {T : ι → ℕ → α} {r : ℕ} {j : Fin n} (h : I.logAt T r = some j) :
    I.ev j (I.run T r).val :=
  I.ev_of_firstViolated h

open Classical in
/-- The number of resamplings of the variable `i` among the first `r` steps. -/
noncomputable def nres (T : ι → ℕ → α) (i : ι) (r : ℕ) : ℕ :=
  ((range r).filter fun r' => ∃ e, I.logAt T r' = some e ∧ i ∈ I.vbl e).card

/-- After `r` steps, the variable `i` holds the table entry of index the number of its
resamplings. -/
theorem run_spec (T : ι → ℕ → α) (i : ι) : ∀ r,
    (I.run T r).cnt i = I.nres T i r + 1 ∧ (I.run T r).val i = T i (I.nres T i r)
  | 0 => by simp [run, init, nres]
  | r + 1 => by
    classical
    obtain ⟨hc, hv⟩ := run_spec T i r
    have hn : I.nres T i (r + 1) = I.nres T i r +
        if ∃ e, I.logAt T r = some e ∧ i ∈ I.vbl e then 1 else 0 := by
      unfold nres
      rw [range_add_one, filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp)]
      · rfl
    show (I.step T (I.run T r)).cnt i = _ ∧ (I.step T (I.run T r)).val i = _
    unfold step
    rcases h : I.firstViolated (I.run T r).val with _ | e
    · have : ¬ ∃ e, I.logAt T r = some e ∧ i ∈ I.vbl e := by
        rintro ⟨e, he, -⟩
        rw [logAt, h] at he
        cases he
      simp only [hn, if_neg this, add_zero]
      exact ⟨hc, hv⟩
    · have hl : I.logAt T r = some e := h
      by_cases hi : i ∈ I.vbl e
      · have : ∃ e', I.logAt T r = some e' ∧ i ∈ I.vbl e' := ⟨e, hl, hi⟩
        simp only [resample, if_pos hi, hn, if_pos this, hc]
        constructor <;> trivial
      · have : ¬ ∃ e', I.logAt T r = some e' ∧ i ∈ I.vbl e' := by
          rintro ⟨e', he', hi'⟩
          rw [hl] at he'
          cases he'
          exact hi hi'
        simp only [resample, if_neg hi, hn, if_neg this, add_zero]
        exact ⟨hc, hv⟩

/-! ### Depth in the witness tree -/

/-- The event resampled at a step (`a`) can sit below the event resampled at a later step
(`b`). -/
def Adj (a b : Option (Fin n)) : Prop := ∃ x y, a = some x ∧ b = some y ∧ x ∈ I.nbrIncl y

open Classical in
/-- The depth of step `r` in the witness tree of step `s` (`⊥` if `r` is not in the tree). -/
noncomputable def wd (T : ι → ℕ → α) (s r : ℕ) : WithBot ℕ :=
  if r = s then 0 else
    (Ioc r s).attach.sup fun u =>
      if I.Adj (I.logAt T r) (I.logAt T u.1) then wd T s u.1 + 1 else ⊥
termination_by s - r
decreasing_by
  have := mem_Ioc.1 u.2
  omega

variable (T : ι → ℕ → α) (s : ℕ)

open Classical in
theorem wd_of_ne {r : ℕ} (h : r ≠ s) : I.wd T s r = (Ioc r s).sup fun u =>
    (if I.Adj (I.logAt T r) (I.logAt T u) then I.wd T s u + 1 else ⊥ : WithBot ℕ) := by
  rw [wd, if_neg h]
  exact Finset.sup_attach (Ioc r s) fun u =>
    (if I.Adj (I.logAt T r) (I.logAt T u) then I.wd T s u + 1 else ⊥ : WithBot ℕ)

theorem wd_self : I.wd T s s = 0 := by
  rw [wd, if_pos rfl]

/-- Step `r` belongs to the witness tree of step `s`. -/
def Mem (r : ℕ) : Prop := I.wd T s r ≠ ⊥

/-- The depth of a step of the witness tree. -/
noncomputable def dp (r : ℕ) : ℕ := WithBot.unbotD 0 (I.wd T s r)

variable {T s}

theorem coe_dp {r : ℕ} (h : I.Mem T s r) : (I.dp T s r : WithBot ℕ) = I.wd T s r := by
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 h
  unfold dp
  rw [← hm]
  rfl

theorem mem_self : I.Mem T s s := by
  unfold Mem
  rw [wd_self]
  exact WithBot.coe_ne_bot

theorem dp_self : I.dp T s s = 0 := by
  unfold dp
  rw [wd_self]
  rfl

theorem le_of_mem {r : ℕ} (h : I.Mem T s r) : r ≤ s := by
  classical
  by_contra hrs
  apply h
  rw [I.wd_of_ne T s (by omega), Ioc_eq_empty (by omega), sup_empty]

/-- A step below a later step of the tree with a neighbouring event is in the tree, and strictly
deeper. -/
theorem dp_lt {r u : ℕ} (hru : r < u) (hus : u ≤ s) (hadj : I.Adj (I.logAt T r) (I.logAt T u))
    (hu : I.Mem T s u) : I.Mem T s r ∧ I.dp T s u < I.dp T s r := by
  classical
  have hle : I.wd T s u + 1 ≤ I.wd T s r := by
    rw [I.wd_of_ne T s (show r ≠ s by omega)]
    refine le_trans ?_ (Finset.le_sup (f := fun u =>
      if I.Adj (I.logAt T r) (I.logAt T u) then I.wd T s u + 1 else ⊥) (mem_Ioc.2 ⟨hru, hus⟩))
    rw [if_pos hadj]
  rw [← I.coe_dp hu] at hle
  have h1 : ((I.dp T s u + 1 : ℕ) : WithBot ℕ) ≤ I.wd T s r := by exact_mod_cast hle
  obtain ⟨b, hb, hle'⟩ := WithBot.coe_le_iff.1 h1
  have hm : I.Mem T s r := by
    unfold Mem
    rw [hb]
    exact WithBot.coe_ne_bot
  refine ⟨hm, ?_⟩
  have h2 := I.coe_dp hm
  rw [hb] at h2
  have : I.dp T s r = b := WithBot.coe_injective h2
  have hle'' : I.dp T s u + 1 ≤ b := by exact_mod_cast hle'
  omega

/-- Every step of the tree other than `s` sits below a later step of the tree, one level up. -/
theorem exists_up {r : ℕ} (hr : I.Mem T s r) (hrs : r ≠ s) :
    ∃ u, r < u ∧ u ≤ s ∧ I.Adj (I.logAt T r) (I.logAt T u) ∧ I.Mem T s u ∧
      I.dp T s r = I.dp T s u + 1 := by
  classical
  have h := I.wd_of_ne T s hrs
  have hne : (Ioc r s).Nonempty := by
    by_contra h'
    rw [not_nonempty_iff_eq_empty] at h'
    rw [h', sup_empty] at h
    exact hr h
  obtain ⟨u, hu, hsup⟩ := exists_mem_eq_sup (Ioc r s) hne fun u =>
    if I.Adj (I.logAt T r) (I.logAt T u) then I.wd T s u + 1 else ⊥
  rw [hsup] at h
  by_cases hadj : I.Adj (I.logAt T r) (I.logAt T u)
  · rw [if_pos hadj] at h
    have hum : I.Mem T s u := by
      intro hb
      rw [hb, WithBot.bot_add] at h
      exact hr h
    refine ⟨u, (mem_Ioc.1 hu).1, (mem_Ioc.1 hu).2, hadj, hum, ?_⟩
    rw [← I.coe_dp hum, ← I.coe_dp hr] at h
    exact_mod_cast h
  · rw [if_neg hadj] at h
    exact absurd h hr

/-- The event of a step of the tree. -/
noncomputable def lab (T : ι → ℕ → α) (j₀ : Fin n) (u : ℕ) : Fin n := (I.logAt T u).getD j₀

variable {j₀ : Fin n}

theorem logAt_of_mem (hs : I.logAt T s = some j₀) {r : ℕ} (hr : I.Mem T s r) :
    I.logAt T r = some (I.lab T j₀ r) := by
  by_cases hrs : r = s
  · subst hrs
    simp [lab, hs]
  · obtain ⟨u, -, -, ⟨x, y, hx, -, -⟩, -⟩ := I.exists_up hr hrs
    simp [lab, hx]

theorem adj_of_mem_nbrIncl (hs : I.logAt T s = some j₀) {r u : ℕ} (hr : I.Mem T s r)
    (hu : I.Mem T s u) (h : I.lab T j₀ r ∈ I.nbrIncl (I.lab T j₀ u)) :
    I.Adj (I.logAt T r) (I.logAt T u) :=
  ⟨_, _, I.logAt_of_mem hs hr, I.logAt_of_mem hs hu, h⟩

/-- Two distinct steps of the tree at the same depth carry neither equal nor neighbouring
events. -/
theorem not_mem_nbrIncl_of_dp_eq (hs : I.logAt T s = some j₀) {r u : ℕ} (hr : I.Mem T s r)
    (hu : I.Mem T s u) (hne : r ≠ u) (hd : I.dp T s r = I.dp T s u) :
    I.lab T j₀ r ∉ I.nbrIncl (I.lab T j₀ u) := by
  intro h
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := (I.dp_lt hlt (I.le_of_mem hu) (I.adj_of_mem_nbrIncl hs hr hu h) hu).2
    omega
  · have := (I.dp_lt hlt (I.le_of_mem hr)
      (I.adj_of_mem_nbrIncl hs hu hr (I.mem_nbrIncl_comm h)) hr).2
    omega

/-- The (event, depth) pair determines a step of the tree. -/
theorem eq_of_lab_dp (hs : I.logAt T s = some j₀) {r u : ℕ} (hr : I.Mem T s r)
    (hu : I.Mem T s u) (hl : I.lab T j₀ r = I.lab T j₀ u) (hd : I.dp T s r = I.dp T s u) :
    r = u := by
  by_contra hne
  exact I.not_mem_nbrIncl_of_dp_eq hs hr hu hne hd (hl ▸ mem_insert_self _ _)

/-! ### Parents and descendants -/

variable (T s) in
open Classical in
/-- The parent of a step of the tree: the first later step one level up. -/
noncomputable def par (r : ℕ) : Option ℕ :=
  if h : ∃ u, r < u ∧ u ≤ s ∧ I.Adj (I.logAt T r) (I.logAt T u) ∧ I.Mem T s u ∧
      I.Mem T s r ∧ I.dp T s r = I.dp T s u + 1 then some (Nat.find h) else none

theorem par_spec {r u : ℕ} (h : I.par T s r = some u) :
    r < u ∧ u ≤ s ∧ I.Adj (I.logAt T r) (I.logAt T u) ∧ I.Mem T s u ∧ I.Mem T s r ∧
      I.dp T s r = I.dp T s u + 1 := by
  classical
  unfold par at h
  split_ifs at h with h'
  · obtain rfl := Option.some.inj h
    exact Nat.find_spec h'

theorem exists_par {r : ℕ} (hr : I.Mem T s r) (hrs : r ≠ s) : ∃ u, I.par T s r = some u := by
  classical
  obtain ⟨u, h1, h2, h3, h4, h5⟩ := I.exists_up hr hrs
  unfold par
  rw [dif_pos ⟨u, h1, h2, h3, h4, hr, h5⟩]
  exact ⟨_, rfl⟩

variable (T s) in
/-- `u` is a descendant of `r` in the witness tree of `s`. -/
def IsDesc (u r : ℕ) : Prop := Relation.ReflTransGen (fun x y => I.par T s x = some y) u r

theorem le_of_isDesc {u r : ℕ} (h : I.IsDesc T s u r) : u ≤ r := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact ih.trans (I.par_spec hbc).1.le

theorem mem_of_isDesc {u r : ℕ} (h : I.IsDesc T s u r) (hr : I.Mem T s r) : I.Mem T s u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hr
  | head hab _ _ => exact (I.par_spec hab).2.2.2.2.1

theorem isDesc_of_mem {u : ℕ} (hu : I.Mem T s u) : I.IsDesc T s u s := by
  induction h : s - u using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    by_cases hus : u = s
    · subst hus
      exact Relation.ReflTransGen.refl
    · obtain ⟨v, hv⟩ := I.exists_par hu hus
      obtain ⟨h1, h2, -, h4, -⟩ := I.par_spec hv
      exact Relation.ReflTransGen.head hv (ih (s - v) (by omega) h4 rfl)

theorem par_rightUnique : Relator.RightUnique fun x y => I.par T s x = some y :=
  fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)

variable (T s) in
open Classical in
/-- The descendants of `r` (including `r`). -/
noncomputable def descF (r : ℕ) : Finset ℕ := (range (r + 1)).filter fun u => I.IsDesc T s u r

theorem mem_descF {u r : ℕ} : u ∈ I.descF T s r ↔ I.IsDesc T s u r := by
  classical
  unfold descF
  rw [mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (I.le_of_isDesc h), h⟩⟩

theorem mem_descF_self_iff {u : ℕ} : u ∈ I.descF T s s ↔ I.Mem T s u :=
  I.mem_descF.trans ⟨fun h => I.mem_of_isDesc h I.mem_self, I.isDesc_of_mem⟩

/-- Two children of `r` with the same event coincide. -/
theorem child_unique (hs : I.logAt T s = some j₀) {r u₁ u₂ : ℕ} {k : Fin n}
    (h₁ : I.par T s u₁ = some r ∧ I.logAt T u₁ = some k)
    (h₂ : I.par T s u₂ = some r ∧ I.logAt T u₂ = some k) : u₁ = u₂ := by
  obtain ⟨-, -, -, -, hm₁, hd₁⟩ := I.par_spec h₁.1
  obtain ⟨-, -, -, -, hm₂, hd₂⟩ := I.par_spec h₂.1
  refine I.eq_of_lab_dp hs hm₁ hm₂ ?_ (by omega)
  rw [I.logAt_of_mem hs hm₁] at h₁
  rw [I.logAt_of_mem hs hm₂] at h₂
  exact Option.some.inj (h₁.2.trans h₂.2.symm)

open Classical in
/-- The descendants of `r`: `r` and the descendants of its children, one for each neighbouring
event. -/
theorem descF_eq (hs : I.logAt T s = some j₀) {r : ℕ} {a : Fin n} (hr : I.Mem T s r)
    (ha : I.logAt T r = some a) :
    (I.descF T s r).val = r ::ₘ (univ : Finset (I.nbrIncl a)).val.bind fun k =>
      if h : ∃ u, I.par T s u = some r ∧ I.logAt T u = some k.1 then
        (I.descF T s (Nat.find h)).val else 0 := by
  have hchild : ∀ {c}, I.par T s c = some r → ∃ k : I.nbrIncl a,
      ∃ h : ∃ u, I.par T s u = some r ∧ I.logAt T u = some k.1, Nat.find h = c := by
    intro c hc
    obtain ⟨-, -, ⟨x, y, hx, hy, hxy⟩, -⟩ := I.par_spec hc
    rw [ha] at hy
    obtain rfl := Option.some.inj hy
    have h : ∃ u, I.par T s u = some r ∧ I.logAt T u = some x := ⟨c, hc, hx⟩
    exact ⟨⟨x, hxy⟩, h, I.child_unique hs (Nat.find_spec h) ⟨hc, hx⟩⟩
  refine (Multiset.Nodup.ext (I.descF T s r).nodup ?_).2 fun x => ?_
  · refine Multiset.nodup_cons.2 ⟨?_, Multiset.nodup_bind.2 ⟨?_, ?_⟩⟩
    · rw [Multiset.mem_bind]
      rintro ⟨k, -, hk⟩
      split_ifs at hk with h
      · have h1 := (I.par_spec (Nat.find_spec h).1).1
        have h2 := I.le_of_isDesc (I.mem_descF.1 hk)
        omega
      · simp at hk
    · intro k _
      split_ifs
      · exact (I.descF T s _).nodup
      · exact Multiset.nodup_zero
    · refine Multiset.Nodup.pairwise (fun k _ k' _ hkk' => ?_) (univ : Finset (I.nbrIncl a)).nodup
      simp only [Function.onFun]
      split_ifs with h h'
      · refine Multiset.disjoint_left.2 fun {x} hx hx' => ?_
        have hc := Nat.find_spec h
        have hc' := Nat.find_spec h'
        have hne : Nat.find h ≠ Nat.find h' := by
          intro he
          rw [he, hc'.2] at hc
          exact hkk' (Subtype.ext (Option.some.inj hc.2).symm)
        rcases Relation.ReflTransGen.total_of_right_unique I.par_rightUnique
          (I.mem_descF.1 hx) (I.mem_descF.1 hx') with hd | hd
        · rcases (Relation.ReflTransGen.cases_head_iff).1 hd with he | ⟨y, hy, hyd⟩
          · exact hne he
          · rw [hc.1] at hy
            obtain rfl := Option.some.inj hy
            have := I.le_of_isDesc hyd
            have := (I.par_spec hc'.1).1
            omega
        · rcases (Relation.ReflTransGen.cases_head_iff).1 hd with he | ⟨y, hy, hyd⟩
          · exact hne he.symm
          · rw [hc'.1] at hy
            obtain rfl := Option.some.inj hy
            have := I.le_of_isDesc hyd
            have := (I.par_spec hc.1).1
            omega
      all_goals exact Multiset.disjoint_left.2 fun {x} hx hx' => by simp at hx hx'
  · rw [Multiset.mem_cons, Multiset.mem_bind, Finset.mem_val, I.mem_descF]
    constructor
    · intro hx
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hx with rfl | ⟨c, hxc, hc⟩
      · exact Or.inl rfl
      · obtain ⟨k, h, hk⟩ := hchild hc
        refine Or.inr ⟨k, Finset.mem_univ_val k, ?_⟩
        rw [dif_pos h, hk]
        exact I.mem_descF.2 hxc
    · rintro (rfl | ⟨k, -, hk⟩)
      · exact Relation.ReflTransGen.refl
      · split_ifs at hk with h
        · exact Relation.ReflTransGen.tail (I.mem_descF.1 hk) (Nat.find_spec h).1
        · simp at hk

/-! ### The typed witness tree -/

variable (T s) in
open Classical in
/-- The witness tree of `s` below the step `r` (with event `a`), as a tree of depth at most
`d + 1`. -/
noncomputable def build : (d : ℕ) → ℕ → (a : Fin n) → I.Tr (d + 1) a
  | 0, _, _ => (fun _ => none : (k : I.nbrIncl _) → Option (I.Tr 0 k))
  | d + 1, r, a => (fun k =>
      if h : ∃ u, I.par T s u = some r ∧ I.logAt T u = some k.1 then
        some (build d (Nat.find h) k) else none : (k : I.nbrIncl a) → Option (I.Tr (d + 1) k))

/-- The vertices of the typed witness tree are the steps of the tree below `r`, with their events
and depths. -/
theorem verts_build (hs : I.logAt T s = some j₀) :
    ∀ (d r : ℕ) (a : Fin n), I.Mem T s r → I.logAt T r = some a → r ≤ d →
      I.verts (d + 1) a (I.build T s d r a) (I.dp T s r) =
        (I.descF T s r).val.map fun u => (I.lab T j₀ u, I.dp T s u)
  | 0, r, a, hr, ha, hrd => by
    classical
    obtain rfl : r = 0 := by omega
    rw [I.descF_eq hs hr ha, Multiset.map_cons]
    have hlab : I.lab T j₀ 0 = a := by simp [lab, ha]
    rw [hlab]
    unfold verts
    congr 1
    rw [Multiset.map_bind]
    refine Multiset.bind_congr fun k _ => ?_
    rw [dif_neg]
    · rfl
    · rintro ⟨u, hu, -⟩
      have := (I.par_spec hu).1
      omega
  | d + 1, r, a, hr, ha, hrd => by
    classical
    rw [I.descF_eq hs hr ha, Multiset.map_cons]
    have hlab : I.lab T j₀ r = a := by simp [lab, ha]
    rw [hlab]
    unfold verts
    congr 1
    rw [Multiset.map_bind]
    refine Multiset.bind_congr fun k _ => ?_
    by_cases h : ∃ u, I.par T s u = some r ∧ I.logAt T u = some k.1
    · rw [dif_pos h]
      have hc := Nat.find_spec h
      obtain ⟨hlt, -, -, hcm, -, hd⟩ := I.par_spec hc.1
      have hb : I.build T s (d + 1) r a k = some (I.build T s d (Nat.find h) k) := by
        simp only [build, dif_pos h]
      simp only [hb]
      rw [← verts_build hs d (Nat.find h) k (I.mem_of_isDesc
        (Relation.ReflTransGen.single hc.1) hr) hc.2 (by omega), hd]
    · rw [dif_neg h]
      have hb : I.build T s (d + 1) r a k = none := by
        simp only [build, dif_neg h]
      simp only [hb]
      rfl

/-- The vertex list of the witness tree of `s`. -/
theorem verts_build_root (hs : I.logAt T s = some j₀) {d : ℕ} (hsd : s ≤ d) :
    I.verts (d + 1) j₀ (I.build T s d s j₀) 0 =
      (I.descF T s s).val.map fun u => (I.lab T j₀ u, I.dp T s u) := by
  rw [← I.verts_build hs d s j₀ I.mem_self hs hsd, dp_self]

/-! ### The coupling -/

/-- When step `u` of the tree is checked, a variable `i` of its event has been resampled once for
each step of the tree deeper than `u` whose event involves `i`. -/
theorem nres_eq_idx (hs : I.logAt T s = some j₀) {u : ℕ} (hu : I.Mem T s u) {i : ι}
    (hi : i ∈ I.vbl (I.lab T j₀ u)) {d : ℕ} (hsd : s ≤ d) :
    I.nres T i u = I.idx (I.verts (d + 1) j₀ (I.build T s d s j₀) 0).toFinset
      (I.lab T j₀ u, I.dp T s u) i := by
  classical
  rw [I.verts_build_root hs hsd]
  have hinj : Set.InjOn (fun u => (I.lab T j₀ u, I.dp T s u)) (I.descF T s s : Set ℕ) := by
    intro x hx y hy hxy
    exact I.eq_of_lab_dp hs (I.mem_descF_self_iff.1 hx) (I.mem_descF_self_iff.1 hy)
      (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have himg : ((I.descF T s s).val.map fun u => (I.lab T j₀ u, I.dp T s u)).toFinset =
      (I.descF T s s).image fun u => (I.lab T j₀ u, I.dp T s u) := rfl
  unfold idx
  rw [himg, filter_image, card_image_of_injOn (hinj.mono (filter_subset _ _))]
  unfold nres
  congr 1
  ext r'
  simp only [mem_filter, mem_range, I.mem_descF_self_iff]
  have hus := I.le_of_mem hu
  constructor
  · rintro ⟨hr', e, he, hie⟩
    have hadj : I.Adj (I.logAt T r') (I.logAt T u) :=
      ⟨e, _, he, I.logAt_of_mem hs hu, I.mem_nbrIncl_of_mem_vbl hie hi⟩
    obtain ⟨hm, hlt⟩ := I.dp_lt hr' hus hadj hu
    rw [I.logAt_of_mem hs hm] at he
    obtain rfl := Option.some.inj he
    exact ⟨hm, hlt, hie⟩
  · rintro ⟨hm, hlt, hie⟩
    refine ⟨?_, _, I.logAt_of_mem hs hm, hie⟩
    by_contra hge
    rcases (not_lt.1 hge).lt_or_eq with hgt | heq
    · have := (I.dp_lt hgt (I.le_of_mem hm)
        (I.adj_of_mem_nbrIncl hs hu hm (I.mem_nbrIncl_of_mem_vbl hi hie)) hm).2
      omega
    · subst heq
      omega

/-- **The coupling.** The witness tree of a step resampling `j₀` passes the `τ`-check on the
table that drives the run. -/
theorem check_build (a₀ : α) {L d : ℕ} (T' : ι × Fin L → α)
    (hs : I.logAt (extend a₀ T') s = some j₀) (hsL : s < L) (hsd : s ≤ d) :
    I.Check a₀ (I.build (extend a₀ T') s d s j₀) T' := by
  classical
  set T := extend a₀ T' with hT
  have hV := I.verts_build_root hs hsd
  have hinj : ∀ x ∈ (I.descF T s s).val, ∀ y ∈ (I.descF T s s).val,
      (I.lab T j₀ x, I.dp T s x) = (I.lab T j₀ y, I.dp T s y) → x = y := by
    intro x hx y hy hxy
    exact I.eq_of_lab_dp hs (I.mem_descF_self_iff.1 hx) (I.mem_descF_self_iff.1 hy)
      (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hV]
    exact Multiset.Nodup.map_on hinj (I.descF T s s).nodup
  · rw [hV]
    intro v hv w hw hne hd
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hv
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hw
    exact I.not_mem_nbrIncl_of_dp_eq hs (I.mem_descF_self_iff.1 hx) (I.mem_descF_self_iff.1 hy)
      (fun h => hne (h ▸ rfl)) hd
  · rw [hV, Multiset.card_map]
    have : (I.descF T s s).card ≤ (range (s + 1)).card := card_le_card (filter_subset _ _)
    rw [card_range] at this
    exact (show (I.descF T s s).val.card = (I.descF T s s).card from rfl) ▸ (by omega)
  · intro v hv
    have hv' := hv
    rw [hV] at hv'
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hv'
    have hum := I.mem_descF_self_iff.1 hu
    have hev := I.ev_of_logAt (I.logAt_of_mem hs hum)
    refine (I.dep _ _ _ fun i hi => ?_).1 hev
    rw [(I.run_spec T i u).2, I.nres_eq_idx hs hum hi hsd]

/-- Different steps resampling `j₀` have different witness trees. -/
theorem build_injective {a₀ : α} {L d : ℕ} {T' : ι × Fin L → α} {s₁ s₂ : ℕ}
    (h₁ : I.logAt (extend a₀ T') s₁ = some j₀) (h₂ : I.logAt (extend a₀ T') s₂ = some j₀)
    (hd₁ : s₁ ≤ d) (hd₂ : s₂ ≤ d)
    (h : I.build (extend a₀ T') s₁ d s₁ j₀ = I.build (extend a₀ T') s₂ d s₂ j₀) : s₁ = s₂ := by
  classical
  set T := extend a₀ T'
  -- the number of vertices labelled `j₀` in the witness tree of `s`
  have hcount : ∀ {s}, I.logAt T s = some j₀ → s ≤ d →
      Multiset.card ((I.verts (d + 1) j₀ (I.build T s d s j₀) 0).filter fun v => v.1 = j₀) =
        ((range (s + 1)).filter fun u => I.logAt T u = some j₀).card := by
    intro s hs hsd
    rw [I.verts_build_root hs hsd, Multiset.filter_map, Multiset.card_map]
    show ((I.descF T s s).filter _).card = _
    congr 1
    ext u
    simp only [mem_filter, mem_range, I.mem_descF_self_iff, Function.comp_apply]
    constructor
    · rintro ⟨hm, hl⟩
      exact ⟨Nat.lt_succ_of_le (I.le_of_mem hm), (I.logAt_of_mem hs hm).trans (congrArg _ hl)⟩
    · rintro ⟨hus, hl⟩
      have hm : I.Mem T s u := by
        rcases (Nat.lt_succ_iff.1 hus).lt_or_eq with hlt | rfl
        · exact (I.dp_lt hlt le_rfl ⟨j₀, j₀, hl, hs, mem_insert_self _ _⟩ I.mem_self).1
        · exact I.mem_self
      refine ⟨hm, ?_⟩
      have := I.logAt_of_mem hs hm
      rw [hl] at this
      exact (Option.some.inj this).symm
  have hc := hcount h₁ hd₁
  rw [h, hcount h₂ hd₂] at hc
  by_contra hne
  have hmono : ∀ {a b : ℕ}, a < b → I.logAt T b = some j₀ →
      ((range (a + 1)).filter fun u => I.logAt T u = some j₀).card <
        ((range (b + 1)).filter fun u => I.logAt T u = some j₀).card := by
    intro a b hab hb
    refine card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨b, ?_, ?_⟩)
    · intro x hx
      simp only [mem_filter, mem_range] at hx ⊢
      exact ⟨by omega, hx.2⟩
    · simp [hb]
    · simp only [mem_filter, mem_range, not_and]
      intro hb'
      omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd hc (hmono hlt h₂).ne'
  · exact absurd hc (hmono hlt h₁).ne

end Inst

end MoserTardos
