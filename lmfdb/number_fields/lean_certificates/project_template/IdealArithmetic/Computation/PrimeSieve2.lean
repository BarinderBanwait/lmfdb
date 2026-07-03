import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Ordmap.Ordset
import Batteries.Data.RBMap.WF
import Lean.Data.RBTree
import Mathlib.Tactic

/-! # The Segmented Prime Sieve

Implements the segmented prime sieve of Eratosthenes.

# Main definition:
- `PrimeSieve`: computes all the prime numbers in a given interval.

# Main result:
- `PrimeSieve_mem` : proves correctness of the program.  -/


def PrimeSieve_loop (P : List ℕ) (cont : ℕ) (accum : List ℕ) : List ℕ :=
  match cont , accum with
  | 0, accum => accum
  | cont + 1 , accum => if h : cont + 1 < P.length then
    PrimeSieve_loop P cont (List.filter
      (fun x => x ≠ P[cont + 1] → x.mod P[cont + 1] ≠ 0 ) accum) else []

/-- The Segmented Prime Sieve:
  Computes a list of all the primes `p` such that `A < p ≤ B`. For correctness, `L` must be
  a list with `¬ 1 ∈ L` and containing all the primes up to the square root of `B`.
  Tail recursive implementation. -/
def PrimeSieve (A : ℕ) (B : ℕ) (L : List ℕ) : List ℕ :=
  let P := (0 :: L)
  let m := List.length L
  let r := B - A
  (PrimeSieve_loop P m ((List.range r).map (fun k => A + 1 + k) ))


/- Proof of correctness of `PrimeSieve`.   -/

lemma PrimeSieve_loop_sublist_aux {P : List ℕ} {c : ℕ} (hcl : c < P.length) {L₁ L₂ : List ℕ}
    (hL : L₁.Sublist L₂)  : (PrimeSieve_loop P c L₁).Sublist (PrimeSieve_loop P c L₂) := by
  revert L₁ L₂
  induction c with
  | zero =>
    intro L₁ L₂ hL
    simp only [PrimeSieve_loop, hL]
  | succ c hc =>
    intro L₁ L₂ hL
    simp only [PrimeSieve_loop, hcl, ↓reduceDIte, ne_eq]
    exact hc (show c < P.length by omega) (List.Sublist.filter _ hL)

lemma PrimeSieve_loop_sublist {P : List ℕ} {c d : ℕ} (h : c ≤ d)
    (hdd : d < P.length) (L : List ℕ) :
    (PrimeSieve_loop P d L).Sublist (PrimeSieve_loop P c L) := by
  induction d with
  | zero => rw [nonpos_iff_eq_zero.1 h]
  | succ d hd =>
    have hdaux : d < P.length := by omega
    have haux: (PrimeSieve_loop P (d + 1) L).Sublist (PrimeSieve_loop P d L) := by
      simp only [PrimeSieve_loop, hdd, ↓reduceDIte]
      refine PrimeSieve_loop_sublist_aux hdaux ?_
      simp only [ ne_eq, List.filter_sublist]
    by_cases hi : c ≤ d
    · refine List.Sublist.trans haux (hd hi hdaux)
    · rw [(show (c = d + 1) by omega )]

lemma PrimeSieve_loop_multiples_aux (P : List ℕ)  (i : ℕ)
    (hdd : i < P.length) (L : List ℕ)
    (n : ℕ) (hz : P[0] = 0) (hn : P[i] ∣ n) (hneq : n ≠ P[i]) :
    ¬ n ∈ PrimeSieve_loop P i L := by
  match i with
  | 0 =>
    simp only [hz, zero_dvd_iff] at hn
    simp only [hn, hz, ne_eq, not_true_eq_false] at hneq
  | i + 1 =>
    simp only [PrimeSieve_loop, hdd, ↓reduceDIte, ne_eq]
    intro hnn
    have hnaux : n ∈ PrimeSieve_loop P 0
      ((List.filter (fun x => x ≠ P[i+ 1] → x.mod P[i + 1] ≠ 0 ) L)):= by
      refine List.Sublist.mem hnn (PrimeSieve_loop_sublist (by omega) (by omega) _)
    simp only [PrimeSieve_loop, ne_eq, decide_implies, decide_not, dite_eq_ite, ite_not,
      Bool.if_true_left, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hnaux
    rw [Nat.dvd_iff_mod_eq_zero] at hn
    rcases hnaux.2 with h1 | h2
    · contradiction
    · contradiction


lemma PrimeSieve_loop_prime_mem {P : List ℕ} {i : ℕ} (hdd : i < P.length)
    {L : List ℕ} {n : ℕ} (hnl : n ∈ L)
    (hn : ∀ k, ∀ h : k ≤ i , P[k] ≠ n → ¬ P[k] ∣ n) :
    n ∈ PrimeSieve_loop P i L := by
  revert L
  induction i with
  | zero => simp only [PrimeSieve_loop, imp_self, implies_true]
  | succ i hi =>
    intro L hnndup
    simp only [PrimeSieve_loop, hdd, ↓reduceDIte, ne_eq, decide_implies, decide_not, dite_eq_ite,
      ite_not, Bool.if_true_left]
    refine hi (by omega) ?_ ?_
    · intro k hk
      exact hn k (by omega)
    · simp only [List.mem_filter, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
      refine ⟨hnndup, ?_ ⟩
      by_cases h : n = P[i + 1]
      · left ; exact h
      · right
        erw [← Nat.dvd_iff_mod_eq_zero]
        exact (hn (i + 1) (by omega)) fun a ↦ h (id (Eq.symm a))


/-- If every prime below `Nat.sqrt B + 1` is included in `L`, and `¬ 1 ∈ L`, then `PrimeSieve A B L` consists precisely
on those primes in the interval `A < p ∧ p ≤ B`.  -/
lemma PrimeSieve_mem (A : ℕ) (B : ℕ) (hA : 1 ≤ A) (L : List ℕ)
    (h : ∀ q, Nat.Prime q → q < Nat.sqrt B + 1 → q ∈ L) (hpL : ¬ 1 ∈ L) (p : ℕ)  :
    p ∈ PrimeSieve A B L ↔ Nat.Prime p ∧ A < p ∧ p ≤ B := by
  constructor
  · intro hp
    have hleaux : A < p ∧ p ≤ B := by
      have : p ∈ ((List.range (B - A)).map (fun k => A + 1 + k) ) := by
        refine List.Sublist.mem hp ?_
        refine PrimeSieve_loop_sublist (P := (0 :: L)) (c := 0) (d := List.length L) (by omega)
          (by simp) ((List.map (fun k ↦ A + 1 + k) (List.range (B - A))))
      simp only [List.mem_map, List.mem_range] at this
      omega
    refine ⟨?_, hleaux⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨by omega, ?_ ⟩
    intro m hmm hmsq
    let q := Nat.minFac m
    have hqp : Nat.Prime q := Nat.minFac_prime (by omega)
    have hqm : q ≤ m := Nat.minFac_le (by omega)
    suffices ¬ q ∣ p by exact fun hc => this (dvd_trans (Nat.minFac_dvd m) hc)
    have hqmem : q ∈ L := by
      refine h q hqp ?_
      refine lt_of_le_of_lt (le_trans hqm hmsq ) ?_
      refine Order.lt_add_one_iff.mpr (Nat.sqrt_le_sqrt hleaux.2)
    intro hc
    obtain ⟨j, hjl, hj⟩ := List.getElem_of_mem hqmem
    have := (PrimeSieve_loop_multiples_aux (0 :: L) (j + 1) (by simp [hjl])
      ((List.range (B - A)).map (fun k => A + 1 + k) ) p rfl ?_ ?_)
    apply this
    refine List.Sublist.mem hp ?_
    refine PrimeSieve_loop_sublist (P := (0 :: L)) (c := j + 1)
      (d := List.length L) (by omega) (by simp) _
    · simp only [List.getElem_cons_succ, hj, hc]
    · simp only [List.getElem_cons_succ, hj, ne_eq]
      have := lt_of_le_of_lt hmsq (Nat.sqrt_lt_self (n := p) (by omega))
      linarith
  · rintro ⟨hp, hla, hlb⟩
    refine PrimeSieve_loop_prime_mem (i := L.length)
      (L := ((List.range (B - A)).map (fun k => A + 1 + k) )) (n := p) ?_ ?_ ?_
    · simp
    · simp only [List.mem_map, List.mem_range]
      use (p - (A + 1))
      omega
    · intro k hk hneq
      match k with
      | 0 =>
        simp only [List.getElem_cons_zero, zero_dvd_iff, ne_eq]
        exact id (Ne.symm hneq)
      | k + 1 =>
        simp at hneq ⊢
        intro hc
        rw [Nat.dvd_prime hp] at hc
        simp only [hneq, or_false] at hc
        simp only [← hc, List.getElem_mem, not_true_eq_false] at hpL


/-- Specialized version of `PrimeSieve_mem ` where `L` is taken to contain exactly those primes
below `Nat.sqrt B + 1`.  -/
lemma PrimeSieve_mem_of_primesBelow (A : ℕ) (B C : ℕ) (hC : C ≤ B)
    (hA : 1 ≤ A) (L : List ℕ)
    (hL : L.toFinset = Nat.primesBelow (B.sqrt + 1))  (p : ℕ) :
    p ∈ PrimeSieve A C L ↔ Nat.Prime p ∧ A < p ∧ p ≤ C := by
  refine PrimeSieve_mem A C hA L ?_ ?_ p
  · intro q hqp hqlt
    suffices q ∈ L.toFinset by exact List.mem_dedup.mp this
    rw [hL]
    refine Nat.mem_primesBelow.mpr ⟨?_, hqp⟩
    refine lt_of_lt_of_le hqlt ?_
    simp only [add_le_add_iff_right]
    exact Nat.sqrt_le_sqrt hC
  · intro hc
    have : 1 ∈ L.toFinset := by exact List.mem_toFinset.mpr hc
    rw [hL, Nat.mem_primesBelow] at this
    exact Nat.prime_one_false this.2


lemma list_eq_primesBelow {B : ℕ} {L : List ℕ}
    (h : ∀ p, p ∈ L ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ B) :
    L.toFinset = Nat.primesBelow (B + 1) := by
  ext p
  rw [List.mem_toFinset]
  convert h p
  rw [Nat.mem_primesBelow]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ⟨ Nat.Prime.one_lt h2 , by omega⟩ ⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h1 ⟩


lemma primes_below_append  (e P : List ℕ) (hneq : e ≠ []) (L : List (List ℕ))
  (he : List.Pairwise (fun x1 x2 => x1 < x2) e)
  (hlength : e.length = L.length + 1) (hM : P.toFinset = Nat.primesBelow (Nat.sqrt (e.getLast hneq) + 1) )
  (hez : e[0]'(List.length_pos_iff.mpr hneq) ≠ 0)
  (hl : ∀ i, ∀ h : i + 1 < e.length , PrimeSieve (e[i]) (e[i + 1]) P = L[i]) (p : ℕ) :
  p ∈ List.foldr (fun x y => x ++ y) [] L ↔
    Nat.Prime p ∧ e[0]'(List.length_pos_iff.mpr hneq) < p ∧ p ≤ e.getLast hneq := by
  revert L
  induction e with
  | nil => exact fun L hlength hl ↦ False.elim (hneq rfl)
  | cons e es hes =>
    intro L hlength
    simp only [List.length_cons, add_lt_add_iff_right, List.getElem_cons_succ,
      List.getElem_cons_zero]
    intro hl
    match L with
    | [] =>
      simp only [List.length_cons, List.length_nil, zero_add, Nat.add_eq_right,
        List.length_eq_zero_iff] at hlength
      simp_rw [hlength]
      simp only [List.foldr_nil, List.not_mem_nil, List.getLast_singleton, false_iff, not_and,
        not_le, imp_self, implies_true]
    | (b :: bs) =>
      by_cases hess : es = []
      · simp[hess] at hlength
      · simp
        rw [List.getLast_cons hess]
        haveI : NeZero (e :: es).length := Nat.instNeZeroSucc
        have hlees : e <  es[0]'(List.length_pos_iff.mpr hess) := by
          convert List.Pairwise.rel_get_of_lt he (a := 0) (b := ⟨1, by simp[List.length_pos_iff.mpr hess]⟩ ) ?_
          · refine Fin.val_pos_iff.mp ?_
            simp only [Nat.lt_one_iff, pos_of_gt]
        have hleql : es[0]'(List.length_pos_iff.mpr hess) ≤ es.getLast hess := by
          simp at he
          have : es.length ≠ 0 := by
            intro hc
            apply hess
            exact List.eq_nil_iff_length_eq_zero.mpr hc
          haveI : NeZero (es.length) := by exact { out := this }
          by_cases hesl : 1 < es.length
          · refine le_of_lt ?_
            convert List.Pairwise.rel_get_of_lt he.2 (a := 0) (b := ⟨es.length - 1, by omega⟩ ) ?_
            · simp
              exact List.getLast_eq_getElem hess
            · refine Fin.val_pos_iff.mp ?_
              rw [tsub_pos_iff_lt]
              omega
          · refine le_of_eq ?_
            obtain ⟨b, hb⟩ := (List.length_eq_one_iff  (l := es) ).1 (by omega)
            simp_rw [hb]
            rfl
        have : e < p ∧ p ≤ es.getLast hess ↔ (e < p ∧ p ≤ es[0]'(List.length_pos_iff.mpr hess)) ∨ (es[0]'(List.length_pos_iff.mpr hess) < p ∧  p ≤ es.getLast hess) := by
          constructor
          · rintro ⟨he1, he2⟩
            omega
          · rintro (⟨he1, he2⟩ | ⟨he3, he4⟩)
            · refine ⟨he1, le_trans he2 hleql ⟩
            · refine ⟨lt_trans hlees he3, he4⟩
        rw [this, and_or_left]
        simp at he
        rw [List.getLast_cons hess] at hM
        simp at hlength
        have haux : (p ∈ List.foldr (fun x y ↦ x ++ y) [] bs ↔ Nat.Prime p ∧ es[0] < p ∧ p ≤ es.getLast hess) := by
          apply hes hess he.2 hM ?_ bs hlength
          intro i hi
          refine hl (i + 1) hi
          exact Nat.ne_zero_of_lt hlees
        have := hl 0 (by omega)
        simp only [List.getElem_cons_zero] at this
        refine or_congr ?_ haux
        rw [← this]
        refine PrimeSieve_mem_of_primesBelow e _ _ hleql ?_ P hM p
        simp at hez
        omega


lemma sqrt20000 : Nat.sqrt 20000  = 141 := by
  symm
  rw [Nat.eq_sqrt']
  decide

def primes_below_142 := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]

lemma primes_below_142_proof : primes_below_142.toFinset = Nat.primesBelow (Nat.sqrt 20000 + 1) := by
  refine list_eq_primesBelow ?_
  have heq : PrimeSieve 1 141 [2, 3, 5,7,11] = primes_below_142 := by rfl
  intro p
  rw [← PrimeSieve_mem_of_primesBelow 1 (Nat.sqrt 20000) (Nat.sqrt 20000) (by omega)
    (by omega) [2, 3, 5,7,11] ?_ p, sqrt20000, heq]
  rw [sqrt20000]
  decide +kernel

-----------

open Ordnode

/-- We extract element in a Ordnode contained in the interval [l₁, l₂].  -/
def Ordnode.extractRangeTree {α : Type*} [LinearOrder α] [DecidableLT α]
  (t : Ordnode α) (l₁ l₂ : α) : Ordnode α :=
  match t with
  | nil => nil
  | node _ l v r =>
    if l₂ < v then -- if the upper limit is too small, we go to the left tree.
      extractRangeTree l l₁ l₂
    else if v < l₁ then --If the lower limit is too big, we look at the right tree.
      extractRangeTree r l₁ l₂
    else -- If the value is in the range, we look at both subtrees.
      let left := extractRangeTree l l₁ l₂
      let right := extractRangeTree r l₁ l₂
      node 0 left v right -- We link them. Balance is violated. This is no longer a Valid tree, but
      -- this makes the proof much easier.


lemma Ordnode.extractRangeTree_emem {α : Type*} [LinearOrder α] [DecidableLT α]
  {t : Ordnode α} (ht : t.Bounded ⊥ ⊤) (l₁ l₂ : α) (x : α) :
    Ordnode.Emem x (Ordnode.extractRangeTree t l₁ l₂)
      ↔ Ordnode.Emem x t ∧ l₁ ≤ x ∧ x ≤ l₂ := by
  induction t with
  | nil => simp [extractRangeTree, Emem, Any]
  | node m t1 v t2 hi1 hi2 =>
    have : (node m t1 v t2).Bounded ⊥ ⊤ = (t1.Bounded ⊥ ↑v ∧ t2.Bounded ↑v ⊤) := by rfl
    rw [this] at ht
    by_cases hl : l₂ < v
    · simp only [extractRangeTree, hl, ↓reduceIte, hi1 (Ordnode.Bounded.weak_right ht.1),
      and_congr_left_iff, and_imp]
      intro ha1 ha2
      constructor
      · intro hmem1
        simp only [Emem, Any]
        left
        exact hmem1
      · intro hmem2
        simp only [Emem, Any] at hmem2
        rcases hmem2 with hc1 | hc2 | hc3
        · exact hc1
        · exfalso
          exact (lt_self_iff_false _ ).1 (lt_of_le_of_lt (hc2 ▸ ha2) hl)
        · have := Ordnode.Bounded.mem_gt ht.2
          rw [Ordnode.all_iff_forall] at this
          specialize this x hc3
          exfalso
          exact (lt_self_iff_false _ ).1 (lt_trans (lt_of_lt_of_le this ha2) hl)
    · by_cases hl2 : v < l₁
      · simp [extractRangeTree, hl, hl2, hi2 (Ordnode.Bounded.weak_left ht.2)]
        intro ha1 ha2
        constructor
        · intro hmem1
          simp only [Emem, Any]
          right ; right
          exact hmem1
        · intro hmem2
          simp only [Emem, Any] at hmem2
          rcases hmem2 with hc1 | hc2 | hc3
          · have := Ordnode.Bounded.mem_lt ht.1
            rw [Ordnode.all_iff_forall] at this
            specialize this x hc1
            exfalso
            exact (lt_self_iff_false _ ).1 (lt_trans hl2 (lt_of_le_of_lt ha1 this))
          · exfalso
            exact (lt_self_iff_false _ ).1 (lt_of_le_of_lt (hc2 ▸ ha1) hl2)
          · exact hc3
      · simp [extractRangeTree, hl, hl2, Emem, Any]
        specialize hi1 (Ordnode.Bounded.weak_right ht.1)
        specialize hi2 (Ordnode.Bounded.weak_left ht.2)
        simp [Emem] at hi1 hi2
        rw [hi1, hi2]
        aesop


lemma Ordnode.extractRangeTree_toList_mem {α : Type*} [LinearOrder α] [DecidableLT α]
  {t : Ordnode α} (ht : t.Bounded ⊥ ⊤) (l₁ l₂ : α) (x : α) :
    x ∈ (Ordnode.extractRangeTree t l₁ l₂).toList  ↔ x ∈ t.toList ∧ l₁ ≤ x ∧ x ≤ l₂ := by
  rw [← Ordnode.emem_iff_mem_toList, ← Ordnode.emem_iff_mem_toList]
  exact Ordnode.extractRangeTree_emem ht l₁ l₂ x


lemma Ordnode.ofList_valid {α : Type*} [Preorder α] [Std.Total fun (x1 x2 : α) => x1 ≤ x2]
  [DecidableLE α] (t : List α) :
  Ordnode.Valid (ofList t) := by
  induction t with
  | nil =>
    simp only [ofList, List.foldr_nil]
    exact valid_nil
  | cons m t1 v =>
    simp only [ofList, List.foldr_cons]
    apply Ordnode.insert.valid
    exact v

lemma Ordnode.ofList_bounded {α : Type*} [Preorder α] [Std.Total fun (x1 x2 : α) => x1 ≤ x2]
  [DecidableLE α] (t : List α) :
  Ordnode.Bounded (ofList t) ⊥ ⊤  := (Ordnode.ofList_valid t).ord

/- Primes below 10,000

Compute all the prime numbers up to 10,000. We use a precomputed list of the primes below 100.
We split things up in intervals of length 300 for smaller proofs and to avoid `maxRecDepth`
(recursion bound on the elaborator) errors, however longer intervals may be considered
with `decide+kernel`, which directly invokes kernel reduction.  -/

set_option maxRecDepth 10000
def primesBelow20000 :=
  [[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293],
  [307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599],
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887],
  [907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193],
  [1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499],
  [1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789],
  [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099],
  [2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399],
  [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699],
  [2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999],
  [3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299],
  [3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593],
  [3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889],
  [3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177],
  [4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493],
  [4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799],
  [4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099],
  [5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399],
  [5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693],
  [5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987],
  [6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299],
  [6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599],
  [6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899],
  [6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193],
  [7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499],
  [7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793],
  [7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093],
  [8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389],
  [8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699],
  [8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999],
  [9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293],
  [9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587],
  [9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887],
  [9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133, 10139, 10141, 10151, 10159, 10163, 10169, 10177, 10181, 10193],
  [10211, 10223, 10243, 10247, 10253, 10259, 10267, 10271, 10273, 10289, 10301, 10303, 10313, 10321, 10331, 10333, 10337, 10343, 10357, 10369, 10391, 10399, 10427, 10429, 10433, 10453, 10457, 10459, 10463, 10477, 10487, 10499],
  [10501, 10513, 10529, 10531, 10559, 10567, 10589, 10597, 10601, 10607, 10613, 10627, 10631, 10639, 10651, 10657, 10663, 10667, 10687, 10691, 10709, 10711, 10723, 10729, 10733, 10739, 10753, 10771, 10781, 10789, 10799],
  [10831, 10837, 10847, 10853, 10859, 10861, 10867, 10883, 10889, 10891, 10903, 10909, 10937, 10939, 10949, 10957, 10973, 10979, 10987, 10993, 11003, 11027, 11047, 11057, 11059, 11069, 11071, 11083, 11087, 11093],
  [11113, 11117, 11119, 11131, 11149, 11159, 11161, 11171, 11173, 11177, 11197, 11213, 11239, 11243, 11251, 11257, 11261, 11273, 11279, 11287, 11299, 11311, 11317, 11321, 11329, 11351, 11353, 11369, 11383, 11393, 11399],
  [11411, 11423, 11437, 11443, 11447, 11467, 11471, 11483, 11489, 11491, 11497, 11503, 11519, 11527, 11549, 11551, 11579, 11587, 11593, 11597, 11617, 11621, 11633, 11657, 11677, 11681, 11689, 11699],
  [11701, 11717, 11719, 11731, 11743, 11777, 11779, 11783, 11789, 11801, 11807, 11813, 11821, 11827, 11831, 11833, 11839, 11863, 11867, 11887, 11897, 11903, 11909, 11923, 11927, 11933, 11939, 11941, 11953, 11959, 11969, 11971, 11981, 11987],
  [12007, 12011, 12037, 12041, 12043, 12049, 12071, 12073, 12097, 12101, 12107, 12109, 12113, 12119, 12143, 12149, 12157, 12161, 12163, 12197, 12203, 12211, 12227, 12239, 12241, 12251, 12253, 12263, 12269, 12277, 12281, 12289],
  [12301, 12323, 12329, 12343, 12347, 12373, 12377, 12379, 12391, 12401, 12409, 12413, 12421, 12433, 12437, 12451, 12457, 12473, 12479, 12487, 12491, 12497, 12503, 12511, 12517, 12527, 12539, 12541, 12547, 12553, 12569, 12577, 12583, 12589],
  [12601, 12611, 12613, 12619, 12637, 12641, 12647, 12653, 12659, 12671, 12689, 12697, 12703, 12713, 12721, 12739, 12743, 12757, 12763, 12781, 12791, 12799, 12809, 12821, 12823, 12829, 12841, 12853, 12889, 12893, 12899],
  [12907, 12911, 12917, 12919, 12923, 12941, 12953, 12959, 12967, 12973, 12979, 12983, 13001, 13003, 13007, 13009, 13033, 13037, 13043, 13049, 13063, 13093, 13099, 13103, 13109, 13121, 13127, 13147, 13151, 13159, 13163, 13171, 13177, 13183, 13187],
  [13217, 13219, 13229, 13241, 13249, 13259, 13267, 13291, 13297, 13309, 13313, 13327, 13331, 13337, 13339, 13367, 13381, 13397, 13399, 13411, 13417, 13421, 13441, 13451, 13457, 13463, 13469, 13477, 13487, 13499],
  [13513, 13523, 13537, 13553, 13567, 13577, 13591, 13597, 13613, 13619, 13627, 13633, 13649, 13669, 13679, 13681, 13687, 13691, 13693, 13697, 13709, 13711, 13721, 13723, 13729, 13751, 13757, 13759, 13763, 13781, 13789, 13799],
  [13807, 13829, 13831, 13841, 13859, 13873, 13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921, 13931, 13933, 13963, 13967, 13997, 13999, 14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087],
  [14107, 14143, 14149, 14153, 14159, 14173, 14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323, 14327, 14341, 14347, 14369, 14387, 14389],
  [14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447, 14449, 14461, 14479, 14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563, 14591, 14593, 14621, 14627, 14629, 14633, 14639, 14653, 14657, 14669, 14683, 14699],
  [14713, 14717, 14723, 14731, 14737, 14741, 14747, 14753, 14759, 14767, 14771, 14779, 14783, 14797, 14813, 14821, 14827, 14831, 14843, 14851, 14867, 14869, 14879, 14887, 14891, 14897, 14923, 14929, 14939, 14947, 14951, 14957, 14969, 14983],
  [15013, 15017, 15031, 15053, 15061, 15073, 15077, 15083, 15091, 15101, 15107, 15121, 15131, 15137, 15139, 15149, 15161, 15173, 15187, 15193, 15199, 15217, 15227, 15233, 15241, 15259, 15263, 15269, 15271, 15277, 15287, 15289, 15299],
  [15307, 15313, 15319, 15329, 15331, 15349, 15359, 15361, 15373, 15377, 15383, 15391, 15401, 15413, 15427, 15439, 15443, 15451, 15461, 15467, 15473, 15493, 15497, 15511, 15527, 15541, 15551, 15559, 15569, 15581, 15583],
  [15601, 15607, 15619, 15629, 15641, 15643, 15647, 15649, 15661, 15667, 15671, 15679, 15683, 15727, 15731, 15733, 15737, 15739, 15749, 15761, 15767, 15773, 15787, 15791, 15797, 15803, 15809, 15817, 15823, 15859, 15877, 15881, 15887, 15889],
  [15901, 15907, 15913, 15919, 15923, 15937, 15959, 15971, 15973, 15991, 16001, 16007, 16033, 16057, 16061, 16063, 16067, 16069, 16073, 16087, 16091, 16097, 16103, 16111, 16127, 16139, 16141, 16183, 16187, 16189, 16193],
  [16217, 16223, 16229, 16231, 16249, 16253, 16267, 16273, 16301, 16319, 16333, 16339, 16349, 16361, 16363, 16369, 16381, 16411, 16417, 16421, 16427, 16433, 16447, 16451, 16453, 16477, 16481, 16487, 16493],
  [16519, 16529, 16547, 16553, 16561, 16567, 16573, 16603, 16607, 16619, 16631, 16633, 16649, 16651, 16657, 16661, 16673, 16691, 16693, 16699, 16703, 16729, 16741, 16747, 16759, 16763, 16787],
  [16811, 16823, 16829, 16831, 16843, 16871, 16879, 16883, 16889, 16901, 16903, 16921, 16927, 16931, 16937, 16943, 16963, 16979, 16981, 16987, 16993, 17011, 17021, 17027, 17029, 17033, 17041, 17047, 17053, 17077, 17093, 17099],
  [17107, 17117, 17123, 17137, 17159, 17167, 17183, 17189, 17191, 17203, 17207, 17209, 17231, 17239, 17257, 17291, 17293, 17299, 17317, 17321, 17327, 17333, 17341, 17351, 17359, 17377, 17383, 17387, 17389, 17393],
  [17401, 17417, 17419, 17431, 17443, 17449, 17467, 17471, 17477, 17483, 17489, 17491, 17497, 17509, 17519, 17539, 17551, 17569, 17573, 17579, 17581, 17597, 17599, 17609, 17623, 17627, 17657, 17659, 17669, 17681, 17683],
  [17707, 17713, 17729, 17737, 17747, 17749, 17761, 17783, 17789, 17791, 17807, 17827, 17837, 17839, 17851, 17863, 17881, 17891, 17903, 17909, 17911, 17921, 17923, 17929, 17939, 17957, 17959, 17971, 17977, 17981, 17987, 17989],
  [18013, 18041, 18043, 18047, 18049, 18059, 18061, 18077, 18089, 18097, 18119, 18121, 18127, 18131, 18133, 18143, 18149, 18169, 18181, 18191, 18199, 18211, 18217, 18223, 18229, 18233, 18251, 18253, 18257, 18269, 18287, 18289],
  [18301, 18307, 18311, 18313, 18329, 18341, 18353, 18367, 18371, 18379, 18397, 18401, 18413, 18427, 18433, 18439, 18443, 18451, 18457, 18461, 18481, 18493, 18503, 18517, 18521, 18523, 18539, 18541, 18553, 18583, 18587, 18593],
  [18617, 18637, 18661, 18671, 18679, 18691, 18701, 18713, 18719, 18731, 18743, 18749, 18757, 18773, 18787, 18793, 18797, 18803, 18839, 18859, 18869, 18899],
  [18911, 18913, 18917, 18919, 18947, 18959, 18973, 18979, 19001, 19009, 19013, 19031, 19037, 19051, 19069, 19073, 19079, 19081, 19087, 19121, 19139, 19141, 19157, 19163, 19181, 19183],
  [19207, 19211, 19213, 19219, 19231, 19237, 19249, 19259, 19267, 19273, 19289, 19301, 19309, 19319, 19333, 19373, 19379, 19381, 19387, 19391, 19403, 19417, 19421, 19423, 19427, 19429, 19433, 19441, 19447, 19457, 19463, 19469, 19471, 19477, 19483, 19489],
  [19501, 19507, 19531, 19541, 19543, 19553, 19559, 19571, 19577, 19583, 19597, 19603, 19609, 19661, 19681, 19687, 19697, 19699, 19709, 19717, 19727, 19739, 19751, 19753, 19759, 19763, 19777, 19793],
  [19801, 19813, 19819, 19841, 19843, 19853, 19861, 19867, 19889, 19891, 19913, 19919, 19927, 19937, 19949, 19961, 19963, 19973, 19979, 19991, 19993, 19997]]



def e_interval_aux := [1, 300, 600, 900, 1200, 1500, 1800, 2100, 2400, 2700, 3000, 3300, 3600, 3900, 4200, 4500,
  4800, 5100, 5400, 5700, 6000, 6300, 6600, 6900, 7200, 7500, 7800, 8100, 8400, 8700, 9000, 9300, 9600, 9900, 10200,
  10500, 10800, 11100, 11400, 11700, 12000, 12300, 12600, 12900, 13200, 13500, 13800, 14100, 14400, 14700, 15000,
   15300, 15600, 15900, 16200, 16500, 16800, 17100, 17400, 17700, 18000, 18300, 18600, 18900, 19200, 19500, 19800,20000]

lemma e_sorted : List.Pairwise (fun x1 x2 => x1 < x2) e_interval_aux := by decide

-- Reach max recursiond depth
/- lemma primesBelow10000_eq_primesBelow_aux_fldr :
  List.foldr (fun x y => x ++ y) [] primesBelow_aux = primesBelow10000 := rfl -/


lemma PB0 : PrimeSieve 1 300 primes_below_142 = primesBelow20000[0] := by decide+kernel
lemma PB300 : PrimeSieve 300 600 primes_below_142 = primesBelow20000[1] := by decide+kernel
lemma PB600 : PrimeSieve 600 900 primes_below_142 = primesBelow20000[2] := by decide+kernel
lemma PB900 : PrimeSieve 900 1200 primes_below_142 = primesBelow20000[3] := by decide+kernel
lemma PB1200 : PrimeSieve 1200 1500 primes_below_142 = primesBelow20000[4] := by decide+kernel
lemma PB1500 : PrimeSieve 1500 1800 primes_below_142 = primesBelow20000[5] := by decide+kernel
lemma PB1800 : PrimeSieve 1800 2100 primes_below_142 = primesBelow20000[6] := by decide+kernel
lemma PB2100 : PrimeSieve 2100 2400 primes_below_142 = primesBelow20000[7] := by decide+kernel
lemma PB2400 : PrimeSieve 2400 2700 primes_below_142 = primesBelow20000[8] := by decide+kernel
lemma PB2700 : PrimeSieve 2700 3000 primes_below_142 = primesBelow20000[9] := by decide+kernel
lemma PB3000 : PrimeSieve 3000 3300 primes_below_142 = primesBelow20000[10] := by decide+kernel
lemma PB3300 : PrimeSieve 3300 3600 primes_below_142 = primesBelow20000[11] := by decide+kernel
lemma PB3600 : PrimeSieve 3600 3900 primes_below_142 = primesBelow20000[12] := by decide+kernel
lemma PB3900 : PrimeSieve 3900 4200 primes_below_142 = primesBelow20000[13] := by decide+kernel
lemma PB4200 : PrimeSieve 4200 4500 primes_below_142 = primesBelow20000[14] := by decide+kernel
lemma PB4500 : PrimeSieve 4500 4800 primes_below_142 = primesBelow20000[15] := by decide+kernel
lemma PB4800 : PrimeSieve 4800 5100 primes_below_142 = primesBelow20000[16] := by decide+kernel
lemma PB5100 : PrimeSieve 5100 5400 primes_below_142 = primesBelow20000[17] := by decide+kernel
lemma PB5400 : PrimeSieve 5400 5700 primes_below_142 = primesBelow20000[18] := by decide+kernel
lemma PB5700 : PrimeSieve 5700 6000 primes_below_142 = primesBelow20000[19] := by decide+kernel
lemma PB6000 : PrimeSieve 6000 6300 primes_below_142 = primesBelow20000[20] := by decide+kernel
lemma PB6300 : PrimeSieve 6300 6600 primes_below_142 = primesBelow20000[21] := by decide+kernel
lemma PB6600 : PrimeSieve 6600 6900 primes_below_142 = primesBelow20000[22] := by decide+kernel
lemma PB6900 : PrimeSieve 6900 7200 primes_below_142 = primesBelow20000[23] := by decide+kernel
lemma PB7200 : PrimeSieve 7200 7500 primes_below_142 = primesBelow20000[24] := by decide+kernel
lemma PB7500 : PrimeSieve 7500 7800 primes_below_142 = primesBelow20000[25] := by decide+kernel
lemma PB7800 : PrimeSieve 7800 8100 primes_below_142 = primesBelow20000[26] := by decide+kernel
lemma PB8100 : PrimeSieve 8100 8400 primes_below_142 = primesBelow20000[27] := by decide+kernel
lemma PB8400 : PrimeSieve 8400 8700 primes_below_142 = primesBelow20000[28] := by decide+kernel
lemma PB8700 : PrimeSieve 8700 9000 primes_below_142 = primesBelow20000[29] := by decide+kernel
lemma PB9000 : PrimeSieve 9000 9300 primes_below_142 = primesBelow20000[30] := by decide+kernel
lemma PB9300 : PrimeSieve 9300 9600 primes_below_142 = primesBelow20000[31] := by decide+kernel
lemma PB9600 : PrimeSieve 9600 9900 primes_below_142 = primesBelow20000[32] := by decide+kernel
lemma PB9900 : PrimeSieve 9900 10200 primes_below_142 = primesBelow20000[33] := by decide+kernel
lemma PB10200 : PrimeSieve 10200 10500 primes_below_142 = primesBelow20000[34] := by decide+kernel
lemma PB10500 : PrimeSieve 10500 10800 primes_below_142 = primesBelow20000[35] := by decide+kernel
lemma PB10800 : PrimeSieve 10800 11100 primes_below_142 = primesBelow20000[36] := by decide+kernel
lemma PB11100 : PrimeSieve 11100 11400 primes_below_142 = primesBelow20000[37] := by decide+kernel
lemma PB11400 : PrimeSieve 11400 11700 primes_below_142 = primesBelow20000[38] := by decide+kernel
lemma PB11700 : PrimeSieve 11700 12000 primes_below_142 = primesBelow20000[39] := by decide+kernel
lemma PB12000 : PrimeSieve 12000 12300 primes_below_142 = primesBelow20000[40] := by decide+kernel
lemma PB12300 : PrimeSieve 12300 12600 primes_below_142 = primesBelow20000[41] := by decide+kernel
lemma PB12600 : PrimeSieve 12600 12900 primes_below_142 = primesBelow20000[42] := by decide+kernel
lemma PB12900 : PrimeSieve 12900 13200 primes_below_142 = primesBelow20000[43] := by decide+kernel
lemma PB13200 : PrimeSieve 13200 13500 primes_below_142 = primesBelow20000[44] := by decide+kernel
lemma PB13500 : PrimeSieve 13500 13800 primes_below_142 = primesBelow20000[45] := by decide+kernel
lemma PB13800 : PrimeSieve 13800 14100 primes_below_142 = primesBelow20000[46] := by decide+kernel
lemma PB14100 : PrimeSieve 14100 14400 primes_below_142 = primesBelow20000[47] := by decide+kernel
lemma PB14400 : PrimeSieve 14400 14700 primes_below_142 = primesBelow20000[48] := by decide+kernel
lemma PB14700 : PrimeSieve 14700 15000 primes_below_142 = primesBelow20000[49] := by decide+kernel
lemma PB15000 : PrimeSieve 15000 15300 primes_below_142 = primesBelow20000[50] := by decide+kernel
lemma PB15300 : PrimeSieve 15300 15600 primes_below_142 = primesBelow20000[51] := by decide+kernel
lemma PB15600 : PrimeSieve 15600 15900 primes_below_142 = primesBelow20000[52] := by decide+kernel
lemma PB15900 : PrimeSieve 15900 16200 primes_below_142 = primesBelow20000[53] := by decide+kernel
lemma PB16200 : PrimeSieve 16200 16500 primes_below_142 = primesBelow20000[54] := by decide+kernel
lemma PB16500 : PrimeSieve 16500 16800 primes_below_142 = primesBelow20000[55] := by decide+kernel
lemma PB16800 : PrimeSieve 16800 17100 primes_below_142 = primesBelow20000[56] := by decide+kernel
lemma PB17100 : PrimeSieve 17100 17400 primes_below_142 = primesBelow20000[57] := by decide+kernel
lemma PB17400 : PrimeSieve 17400 17700 primes_below_142 = primesBelow20000[58] := by decide+kernel
lemma PB17700 : PrimeSieve 17700 18000 primes_below_142 = primesBelow20000[59] := by decide+kernel
lemma PB18000 : PrimeSieve 18000 18300 primes_below_142 = primesBelow20000[60] := by decide+kernel
lemma PB18300 : PrimeSieve 18300 18600 primes_below_142 = primesBelow20000[61] := by decide+kernel
lemma PB18600 : PrimeSieve 18600 18900 primes_below_142 = primesBelow20000[62] := by decide+kernel
lemma PB18900 : PrimeSieve 18900 19200 primes_below_142 = primesBelow20000[63] := by decide+kernel
lemma PB19200 : PrimeSieve 19200 19500 primes_below_142 = primesBelow20000[64] := by decide+kernel
lemma PB19500 : PrimeSieve 19500 19800 primes_below_142 = primesBelow20000[65] := by decide+kernel
lemma PB19800 : PrimeSieve 19800 20000 primes_below_142 = primesBelow20000[66] := by decide+kernel



lemma primes_below_20000 (p : ℕ):
  p ∈ primesBelow20000.foldr (fun x y => x ++ y) [] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 20000 := by
  convert primes_below_append e_interval_aux primes_below_142 (by decide) primesBelow20000 e_sorted ?_ ?_ (by decide) ?_ p
  · rfl
  · exact primes_below_142_proof
  · intro i hi
    have : e_interval_aux.length = 68 := by decide
    have hif : i < 67 := by omega
    interval_cases i
    exact PB0 ; exact PB300 ; exact PB600 ; exact PB900 ; exact PB1200 ; exact PB1500 ; exact PB1800
    exact PB2100 ; exact PB2400 ; exact PB2700 ; exact PB3000 ; exact PB3300 ; exact PB3600 ; exact PB3900
    exact PB4200 ; exact PB4500 ; exact PB4800 ; exact PB5100 ; exact PB5400 ; exact PB5700 ; exact PB6000
    exact PB6300 ; exact PB6600 ; exact PB6900 ; exact PB7200 ; exact PB7500 ; exact PB7800 ; exact PB8100
    exact PB8400 ; exact PB8700 ; exact PB9000 ; exact PB9300 ; exact PB9600 ; exact PB9900 ; exact PB10200
    exact PB10500 ; exact PB10800 ; exact PB11100 ; exact PB11400 ; exact PB11700 ; exact PB12000 ; exact PB12300
    exact PB12600 ; exact PB12900 ; exact PB13200 ; exact PB13500 ; exact PB13800 ; exact PB14100 ; exact PB14400
    exact PB14700 ; exact PB15000 ; exact PB15300 ; exact PB15600 ; exact PB15900 ; exact PB16200 ; exact PB16500
    exact PB16800 ; exact PB17100 ; exact PB17400 ; exact PB17700 ; exact PB18000 ; exact PB18300 ; exact PB18600
    exact PB18900 ; exact PB19200 ; exact PB19500 ; exact PB19800


/-- The tree with the primes-/
def PTreeE := node 2262 (node 1238 (node 726 (node 470 (node 342 (node 214 (node 150 (node 86 (node 54 (node 38 (node 22 (node 14 (node 6 (node 2 (node 1 (nil) 2 (nil)) 3 (nil)) 5 (node 3 (node 1 (nil) 7 (nil)) 11 (node 1 (nil) 13 (nil)))) 17 (node 7 (node 3 (node 1 (nil) 19 (nil)) 23 (node 1 (nil) 29 (nil))) 31 (node 3 (node 1 (nil) 37 (nil)) 41 (node 1 (nil) 43 (nil))))) 47 (node 7 (node 3 (node 1 (nil) 53 (nil)) 59 (node 1 (nil) 61 (nil))) 67 (node 3 (node 1 (nil) 71 (nil)) 73 (node 1 (nil) 79 (nil))))) 83 (node 15 (node 7 (node 3 (node 1 (nil) 89 (nil)) 97 (node 1 (nil) 101 (nil))) 103 (node 3 (node 1 (nil) 107 (nil)) 109 (node 1 (nil) 113 (nil)))) 127 (node 7 (node 3 (node 1 (nil) 131 (nil)) 137 (node 1 (nil) 139 (nil))) 149 (node 3 (node 1 (nil) 151 (nil)) 157 (node 1 (nil) 163 (nil)))))) 167 (node 15 (node 7 (node 3 (node 1 (nil) 173 (nil)) 179 (node 1 (nil) 181 (nil))) 191 (node 3 (node 1 (nil) 193 (nil)) 197 (node 1 (nil) 199 (nil)))) 211 (node 7 (node 3 (node 1 (nil) 223 (nil)) 227 (node 1 (nil) 229 (nil))) 233 (node 3 (node 1 (nil) 239 (nil)) 241 (node 1 (nil) 251 (nil)))))) 257 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 263 (nil)) 269 (node 1 (nil) 271 (nil))) 277 (node 3 (node 1 (nil) 281 (nil)) 283 (node 1 (nil) 293 (nil)))) 307 (node 7 (node 3 (node 1 (nil) 311 (nil)) 313 (node 1 (nil) 317 (nil))) 331 (node 3 (node 1 (nil) 337 (nil)) 347 (node 1 (nil) 349 (nil))))) 353 (node 15 (node 7 (node 3 (node 1 (nil) 359 (nil)) 367 (node 1 (nil) 373 (nil))) 379 (node 3 (node 1 (nil) 383 (nil)) 389 (node 1 (nil) 397 (nil)))) 401 (node 7 (node 3 (node 1 (nil) 409 (nil)) 419 (node 1 (nil) 421 (nil))) 431 (node 3 (node 1 (nil) 433 (nil)) 439 (node 1 (nil) 443 (nil))))))) 449 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 457 (nil)) 461 (node 1 (nil) 463 (nil))) 467 (node 3 (node 1 (nil) 479 (nil)) 487 (node 1 (nil) 491 (nil)))) 499 (node 7 (node 3 (node 1 (nil) 503 (nil)) 509 (node 1 (nil) 521 (nil))) 523 (node 3 (node 1 (nil) 541 (nil)) 547 (node 1 (nil) 557 (nil))))) 563 (node 15 (node 7 (node 3 (node 1 (nil) 569 (nil)) 571 (node 1 (nil) 577 (nil))) 587 (node 3 (node 1 (nil) 593 (nil)) 599 (node 1 (nil) 601 (nil)))) 607 (node 7 (node 3 (node 1 (nil) 613 (nil)) 617 (node 1 (nil) 619 (nil))) 631 (node 3 (node 1 (nil) 641 (nil)) 643 (node 1 (nil) 647 (nil)))))) 653 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 659 (nil)) 661 (node 1 (nil) 673 (nil))) 677 (node 3 (node 1 (nil) 683 (nil)) 691 (node 1 (nil) 701 (nil)))) 709 (node 7 (node 3 (node 1 (nil) 719 (nil)) 727 (node 1 (nil) 733 (nil))) 739 (node 3 (node 1 (nil) 743 (nil)) 751 (node 1 (nil) 757 (nil))))) 761 (node 15 (node 7 (node 3 (node 1 (nil) 769 (nil)) 773 (node 1 (nil) 787 (nil))) 797 (node 3 (node 1 (nil) 809 (nil)) 811 (node 1 (nil) 821 (nil)))) 823 (node 7 (node 3 (node 1 (nil) 827 (nil)) 829 (node 1 (nil) 839 (nil))) 853 (node 3 (node 1 (nil) 857 (nil)) 859 (node 1 (nil) 863 (nil)))))))) 877 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 881 (nil)) 883 (node 1 (nil) 887 (nil))) 907 (node 3 (node 1 (nil) 911 (nil)) 919 (node 1 (nil) 929 (nil)))) 937 (node 7 (node 3 (node 1 (nil) 941 (nil)) 947 (node 1 (nil) 953 (nil))) 967 (node 3 (node 1 (nil) 971 (nil)) 977 (node 1 (nil) 983 (nil))))) 991 (node 15 (node 7 (node 3 (node 1 (nil) 997 (nil)) 1009 (node 1 (nil) 1013 (nil))) 1019 (node 3 (node 1 (nil) 1021 (nil)) 1031 (node 1 (nil) 1033 (nil)))) 1039 (node 7 (node 3 (node 1 (nil) 1049 (nil)) 1051 (node 1 (nil) 1061 (nil))) 1063 (node 3 (node 1 (nil) 1069 (nil)) 1087 (node 1 (nil) 1091 (nil)))))) 1093 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1097 (nil)) 1103 (node 1 (nil) 1109 (nil))) 1117 (node 3 (node 1 (nil) 1123 (nil)) 1129 (node 1 (nil) 1151 (nil)))) 1153 (node 7 (node 3 (node 1 (nil) 1163 (nil)) 1171 (node 1 (nil) 1181 (nil))) 1187 (node 3 (node 1 (nil) 1193 (nil)) 1201 (node 1 (nil) 1213 (nil))))) 1217 (node 15 (node 7 (node 3 (node 1 (nil) 1223 (nil)) 1229 (node 1 (nil) 1231 (nil))) 1237 (node 3 (node 1 (nil) 1249 (nil)) 1259 (node 1 (nil) 1277 (nil)))) 1279 (node 7 (node 3 (node 1 (nil) 1283 (nil)) 1289 (node 1 (nil) 1291 (nil))) 1297 (node 3 (node 1 (nil) 1301 (nil)) 1303 (node 1 (nil) 1307 (nil)))))))) 1319 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1321 (nil)) 1327 (node 1 (nil) 1361 (nil))) 1367 (node 3 (node 1 (nil) 1373 (nil)) 1381 (node 1 (nil) 1399 (nil)))) 1409 (node 7 (node 3 (node 1 (nil) 1423 (nil)) 1427 (node 1 (nil) 1429 (nil))) 1433 (node 3 (node 1 (nil) 1439 (nil)) 1447 (node 1 (nil) 1451 (nil))))) 1453 (node 15 (node 7 (node 3 (node 1 (nil) 1459 (nil)) 1471 (node 1 (nil) 1481 (nil))) 1483 (node 3 (node 1 (nil) 1487 (nil)) 1489 (node 1 (nil) 1493 (nil)))) 1499 (node 7 (node 3 (node 1 (nil) 1511 (nil)) 1523 (node 1 (nil) 1531 (nil))) 1543 (node 3 (node 1 (nil) 1549 (nil)) 1553 (node 1 (nil) 1559 (nil)))))) 1567 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1571 (nil)) 1579 (node 1 (nil) 1583 (nil))) 1597 (node 3 (node 1 (nil) 1601 (nil)) 1607 (node 1 (nil) 1609 (nil)))) 1613 (node 7 (node 3 (node 1 (nil) 1619 (nil)) 1621 (node 1 (nil) 1627 (nil))) 1637 (node 3 (node 1 (nil) 1657 (nil)) 1663 (node 1 (nil) 1667 (nil))))) 1669 (node 15 (node 7 (node 3 (node 1 (nil) 1693 (nil)) 1697 (node 1 (nil) 1699 (nil))) 1709 (node 3 (node 1 (nil) 1721 (nil)) 1723 (node 1 (nil) 1733 (nil)))) 1741 (node 7 (node 3 (node 1 (nil) 1747 (nil)) 1753 (node 1 (nil) 1759 (nil))) 1777 (node 3 (node 1 (nil) 1783 (nil)) 1787 (node 1 (nil) 1789 (nil))))))) 1801 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 1811 (nil)) 1823 (node 1 (nil) 1831 (nil))) 1847 (node 3 (node 1 (nil) 1861 (nil)) 1867 (node 1 (nil) 1871 (nil)))) 1873 (node 7 (node 3 (node 1 (nil) 1877 (nil)) 1879 (node 1 (nil) 1889 (nil))) 1901 (node 3 (node 1 (nil) 1907 (nil)) 1913 (node 1 (nil) 1931 (nil))))) 1933 (node 15 (node 7 (node 3 (node 1 (nil) 1949 (nil)) 1951 (node 1 (nil) 1973 (nil))) 1979 (node 3 (node 1 (nil) 1987 (nil)) 1993 (node 1 (nil) 1997 (nil)))) 1999 (node 7 (node 3 (node 1 (nil) 2003 (nil)) 2011 (node 1 (nil) 2017 (nil))) 2027 (node 3 (node 1 (nil) 2029 (nil)) 2039 (node 1 (nil) 2053 (nil)))))) 2063 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 2069 (nil)) 2081 (node 1 (nil) 2083 (nil))) 2087 (node 3 (node 1 (nil) 2089 (nil)) 2099 (node 1 (nil) 2111 (nil)))) 2113 (node 7 (node 3 (node 1 (nil) 2129 (nil)) 2131 (node 1 (nil) 2137 (nil))) 2141 (node 3 (node 1 (nil) 2143 (nil)) 2153 (node 1 (nil) 2161 (nil))))) 2179 (node 15 (node 7 (node 3 (node 1 (nil) 2203 (nil)) 2207 (node 1 (nil) 2213 (nil))) 2221 (node 3 (node 1 (nil) 2237 (nil)) 2239 (node 1 (nil) 2243 (nil)))) 2251 (node 7 (node 3 (node 1 (nil) 2267 (nil)) 2269 (node 1 (nil) 2273 (nil))) 2281 (node 3 (node 1 (nil) 2287 (nil)) 2293 (node 1 (nil) 2297 (nil))))))))) 2309 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 2311 (nil)) 2333 (node 1 (nil) 2339 (nil))) 2341 (node 3 (node 1 (nil) 2347 (nil)) 2351 (node 1 (nil) 2357 (nil)))) 2371 (node 7 (node 3 (node 1 (nil) 2377 (nil)) 2381 (node 1 (nil) 2383 (nil))) 2389 (node 3 (node 1 (nil) 2393 (nil)) 2399 (node 1 (nil) 2411 (nil))))) 2417 (node 15 (node 7 (node 3 (node 1 (nil) 2423 (nil)) 2437 (node 1 (nil) 2441 (nil))) 2447 (node 3 (node 1 (nil) 2459 (nil)) 2467 (node 1 (nil) 2473 (nil)))) 2477 (node 7 (node 3 (node 1 (nil) 2503 (nil)) 2521 (node 1 (nil) 2531 (nil))) 2539 (node 3 (node 1 (nil) 2543 (nil)) 2549 (node 1 (nil) 2551 (nil)))))) 2557 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 2579 (nil)) 2591 (node 1 (nil) 2593 (nil))) 2609 (node 3 (node 1 (nil) 2617 (nil)) 2621 (node 1 (nil) 2633 (nil)))) 2647 (node 7 (node 3 (node 1 (nil) 2657 (nil)) 2659 (node 1 (nil) 2663 (nil))) 2671 (node 3 (node 1 (nil) 2677 (nil)) 2683 (node 1 (nil) 2687 (nil))))) 2689 (node 15 (node 7 (node 3 (node 1 (nil) 2693 (nil)) 2699 (node 1 (nil) 2707 (nil))) 2711 (node 3 (node 1 (nil) 2713 (nil)) 2719 (node 1 (nil) 2729 (nil)))) 2731 (node 7 (node 3 (node 1 (nil) 2741 (nil)) 2749 (node 1 (nil) 2753 (nil))) 2767 (node 3 (node 1 (nil) 2777 (nil)) 2789 (node 1 (nil) 2791 (nil))))))) 2797 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 2801 (nil)) 2803 (node 1 (nil) 2819 (nil))) 2833 (node 3 (node 1 (nil) 2837 (nil)) 2843 (node 1 (nil) 2851 (nil)))) 2857 (node 7 (node 3 (node 1 (nil) 2861 (nil)) 2879 (node 1 (nil) 2887 (nil))) 2897 (node 3 (node 1 (nil) 2903 (nil)) 2909 (node 1 (nil) 2917 (nil))))) 2927 (node 15 (node 7 (node 3 (node 1 (nil) 2939 (nil)) 2953 (node 1 (nil) 2957 (nil))) 2963 (node 3 (node 1 (nil) 2969 (nil)) 2971 (node 1 (nil) 2999 (nil)))) 3001 (node 7 (node 3 (node 1 (nil) 3011 (nil)) 3019 (node 1 (nil) 3023 (nil))) 3037 (node 3 (node 1 (nil) 3041 (nil)) 3049 (node 1 (nil) 3061 (nil)))))) 3067 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3079 (nil)) 3083 (node 1 (nil) 3089 (nil))) 3109 (node 3 (node 1 (nil) 3119 (nil)) 3121 (node 1 (nil) 3137 (nil)))) 3163 (node 7 (node 3 (node 1 (nil) 3167 (nil)) 3169 (node 1 (nil) 3181 (nil))) 3187 (node 3 (node 1 (nil) 3191 (nil)) 3203 (node 1 (nil) 3209 (nil))))) 3217 (node 15 (node 7 (node 3 (node 1 (nil) 3221 (nil)) 3229 (node 1 (nil) 3251 (nil))) 3253 (node 3 (node 1 (nil) 3257 (nil)) 3259 (node 1 (nil) 3271 (nil)))) 3299 (node 7 (node 3 (node 1 (nil) 3301 (nil)) 3307 (node 1 (nil) 3313 (nil))) 3319 (node 3 (node 1 (nil) 3323 (nil)) 3329 (node 1 (nil) 3331 (nil))))))))) 3343 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3347 (nil)) 3359 (node 1 (nil) 3361 (nil))) 3371 (node 3 (node 1 (nil) 3373 (nil)) 3389 (node 1 (nil) 3391 (nil)))) 3407 (node 7 (node 3 (node 1 (nil) 3413 (nil)) 3433 (node 1 (nil) 3449 (nil))) 3457 (node 3 (node 1 (nil) 3461 (nil)) 3463 (node 1 (nil) 3467 (nil))))) 3469 (node 15 (node 7 (node 3 (node 1 (nil) 3491 (nil)) 3499 (node 1 (nil) 3511 (nil))) 3517 (node 3 (node 1 (nil) 3527 (nil)) 3529 (node 1 (nil) 3533 (nil)))) 3539 (node 7 (node 3 (node 1 (nil) 3541 (nil)) 3547 (node 1 (nil) 3557 (nil))) 3559 (node 3 (node 1 (nil) 3571 (nil)) 3581 (node 1 (nil) 3583 (nil)))))) 3593 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3607 (nil)) 3613 (node 1 (nil) 3617 (nil))) 3623 (node 3 (node 1 (nil) 3631 (nil)) 3637 (node 1 (nil) 3643 (nil)))) 3659 (node 7 (node 3 (node 1 (nil) 3671 (nil)) 3673 (node 1 (nil) 3677 (nil))) 3691 (node 3 (node 1 (nil) 3697 (nil)) 3701 (node 1 (nil) 3709 (nil))))) 3719 (node 15 (node 7 (node 3 (node 1 (nil) 3727 (nil)) 3733 (node 1 (nil) 3739 (nil))) 3761 (node 3 (node 1 (nil) 3767 (nil)) 3769 (node 1 (nil) 3779 (nil)))) 3793 (node 7 (node 3 (node 1 (nil) 3797 (nil)) 3803 (node 1 (nil) 3821 (nil))) 3823 (node 3 (node 1 (nil) 3833 (nil)) 3847 (node 1 (nil) 3851 (nil))))))) 3853 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 3863 (nil)) 3877 (node 1 (nil) 3881 (nil))) 3889 (node 3 (node 1 (nil) 3907 (nil)) 3911 (node 1 (nil) 3917 (nil)))) 3919 (node 7 (node 3 (node 1 (nil) 3923 (nil)) 3929 (node 1 (nil) 3931 (nil))) 3943 (node 3 (node 1 (nil) 3947 (nil)) 3967 (node 1 (nil) 3989 (nil))))) 4001 (node 15 (node 7 (node 3 (node 1 (nil) 4003 (nil)) 4007 (node 1 (nil) 4013 (nil))) 4019 (node 3 (node 1 (nil) 4021 (nil)) 4027 (node 1 (nil) 4049 (nil)))) 4051 (node 7 (node 3 (node 1 (nil) 4057 (nil)) 4073 (node 1 (nil) 4079 (nil))) 4091 (node 3 (node 1 (nil) 4093 (nil)) 4099 (node 1 (nil) 4111 (nil)))))) 4127 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4129 (nil)) 4133 (node 1 (nil) 4139 (nil))) 4153 (node 3 (node 1 (nil) 4157 (nil)) 4159 (node 1 (nil) 4177 (nil)))) 4201 (node 7 (node 3 (node 1 (nil) 4211 (nil)) 4217 (node 1 (nil) 4219 (nil))) 4229 (node 3 (node 1 (nil) 4231 (nil)) 4241 (node 1 (nil) 4243 (nil))))) 4253 (node 15 (node 7 (node 3 (node 1 (nil) 4259 (nil)) 4261 (node 1 (nil) 4271 (nil))) 4273 (node 3 (node 1 (nil) 4283 (nil)) 4289 (node 1 (nil) 4297 (nil)))) 4327 (node 7 (node 3 (node 1 (nil) 4337 (nil)) 4339 (node 1 (nil) 4349 (nil))) 4357 (node 3 (node 1 (nil) 4363 (nil)) 4373 (node 1 (nil) 4391 (nil)))))))) 4397 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4409 (nil)) 4421 (node 1 (nil) 4423 (nil))) 4441 (node 3 (node 1 (nil) 4447 (nil)) 4451 (node 1 (nil) 4457 (nil)))) 4463 (node 7 (node 3 (node 1 (nil) 4481 (nil)) 4483 (node 1 (nil) 4493 (nil))) 4507 (node 3 (node 1 (nil) 4513 (nil)) 4517 (node 1 (nil) 4519 (nil))))) 4523 (node 15 (node 7 (node 3 (node 1 (nil) 4547 (nil)) 4549 (node 1 (nil) 4561 (nil))) 4567 (node 3 (node 1 (nil) 4583 (nil)) 4591 (node 1 (nil) 4597 (nil)))) 4603 (node 7 (node 3 (node 1 (nil) 4621 (nil)) 4637 (node 1 (nil) 4639 (nil))) 4643 (node 3 (node 1 (nil) 4649 (nil)) 4651 (node 1 (nil) 4657 (nil)))))) 4663 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4673 (nil)) 4679 (node 1 (nil) 4691 (nil))) 4703 (node 3 (node 1 (nil) 4721 (nil)) 4723 (node 1 (nil) 4729 (nil)))) 4733 (node 7 (node 3 (node 1 (nil) 4751 (nil)) 4759 (node 1 (nil) 4783 (nil))) 4787 (node 3 (node 1 (nil) 4789 (nil)) 4793 (node 1 (nil) 4799 (nil))))) 4801 (node 15 (node 7 (node 3 (node 1 (nil) 4813 (nil)) 4817 (node 1 (nil) 4831 (nil))) 4861 (node 3 (node 1 (nil) 4871 (nil)) 4877 (node 1 (nil) 4889 (nil)))) 4903 (node 7 (node 3 (node 1 (nil) 4909 (nil)) 4919 (node 1 (nil) 4931 (nil))) 4933 (node 3 (node 1 (nil) 4937 (nil)) 4943 (node 1 (nil) 4951 (nil))))))) 4957 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 4967 (nil)) 4969 (node 1 (nil) 4973 (nil))) 4987 (node 3 (node 1 (nil) 4993 (nil)) 4999 (node 1 (nil) 5003 (nil)))) 5009 (node 7 (node 3 (node 1 (nil) 5011 (nil)) 5021 (node 1 (nil) 5023 (nil))) 5039 (node 3 (node 1 (nil) 5051 (nil)) 5059 (node 1 (nil) 5077 (nil))))) 5081 (node 15 (node 7 (node 3 (node 1 (nil) 5087 (nil)) 5099 (node 1 (nil) 5101 (nil))) 5107 (node 3 (node 1 (nil) 5113 (nil)) 5119 (node 1 (nil) 5147 (nil)))) 5153 (node 7 (node 3 (node 1 (nil) 5167 (nil)) 5171 (node 1 (nil) 5179 (nil))) 5189 (node 3 (node 1 (nil) 5197 (nil)) 5209 (node 1 (nil) 5227 (nil)))))) 5231 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 5233 (nil)) 5237 (node 1 (nil) 5261 (nil))) 5273 (node 3 (node 1 (nil) 5279 (nil)) 5281 (node 1 (nil) 5297 (nil)))) 5303 (node 7 (node 3 (node 1 (nil) 5309 (nil)) 5323 (node 1 (nil) 5333 (nil))) 5347 (node 3 (node 1 (nil) 5351 (nil)) 5381 (node 1 (nil) 5387 (nil))))) 5393 (node 15 (node 7 (node 3 (node 1 (nil) 5399 (nil)) 5407 (node 1 (nil) 5413 (nil))) 5417 (node 3 (node 1 (nil) 5419 (nil)) 5431 (node 1 (nil) 5437 (nil)))) 5441 (node 7 (node 3 (node 1 (nil) 5443 (nil)) 5449 (node 1 (nil) 5471 (nil))) 5477 (node 3 (node 1 (nil) 5479 (nil)) 5483 (node 1 (nil) 5501 (nil)))))))))) 5503 (node 511 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 5507 (nil)) 5519 (node 1 (nil) 5521 (nil))) 5527 (node 3 (node 1 (nil) 5531 (nil)) 5557 (node 1 (nil) 5563 (nil)))) 5569 (node 7 (node 3 (node 1 (nil) 5573 (nil)) 5581 (node 1 (nil) 5591 (nil))) 5623 (node 3 (node 1 (nil) 5639 (nil)) 5641 (node 1 (nil) 5647 (nil))))) 5651 (node 15 (node 7 (node 3 (node 1 (nil) 5653 (nil)) 5657 (node 1 (nil) 5659 (nil))) 5669 (node 3 (node 1 (nil) 5683 (nil)) 5689 (node 1 (nil) 5693 (nil)))) 5701 (node 7 (node 3 (node 1 (nil) 5711 (nil)) 5717 (node 1 (nil) 5737 (nil))) 5741 (node 3 (node 1 (nil) 5743 (nil)) 5749 (node 1 (nil) 5779 (nil)))))) 5783 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 5791 (nil)) 5801 (node 1 (nil) 5807 (nil))) 5813 (node 3 (node 1 (nil) 5821 (nil)) 5827 (node 1 (nil) 5839 (nil)))) 5843 (node 7 (node 3 (node 1 (nil) 5849 (nil)) 5851 (node 1 (nil) 5857 (nil))) 5861 (node 3 (node 1 (nil) 5867 (nil)) 5869 (node 1 (nil) 5879 (nil))))) 5881 (node 15 (node 7 (node 3 (node 1 (nil) 5897 (nil)) 5903 (node 1 (nil) 5923 (nil))) 5927 (node 3 (node 1 (nil) 5939 (nil)) 5953 (node 1 (nil) 5981 (nil)))) 5987 (node 7 (node 3 (node 1 (nil) 6007 (nil)) 6011 (node 1 (nil) 6029 (nil))) 6037 (node 3 (node 1 (nil) 6043 (nil)) 6047 (node 1 (nil) 6053 (nil))))))) 6067 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 6073 (nil)) 6079 (node 1 (nil) 6089 (nil))) 6091 (node 3 (node 1 (nil) 6101 (nil)) 6113 (node 1 (nil) 6121 (nil)))) 6131 (node 7 (node 3 (node 1 (nil) 6133 (nil)) 6143 (node 1 (nil) 6151 (nil))) 6163 (node 3 (node 1 (nil) 6173 (nil)) 6197 (node 1 (nil) 6199 (nil))))) 6203 (node 15 (node 7 (node 3 (node 1 (nil) 6211 (nil)) 6217 (node 1 (nil) 6221 (nil))) 6229 (node 3 (node 1 (nil) 6247 (nil)) 6257 (node 1 (nil) 6263 (nil)))) 6269 (node 7 (node 3 (node 1 (nil) 6271 (nil)) 6277 (node 1 (nil) 6287 (nil))) 6299 (node 3 (node 1 (nil) 6301 (nil)) 6311 (node 1 (nil) 6317 (nil)))))) 6323 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 6329 (nil)) 6337 (node 1 (nil) 6343 (nil))) 6353 (node 3 (node 1 (nil) 6359 (nil)) 6361 (node 1 (nil) 6367 (nil)))) 6373 (node 7 (node 3 (node 1 (nil) 6379 (nil)) 6389 (node 1 (nil) 6397 (nil))) 6421 (node 3 (node 1 (nil) 6427 (nil)) 6449 (node 1 (nil) 6451 (nil))))) 6469 (node 15 (node 7 (node 3 (node 1 (nil) 6473 (nil)) 6481 (node 1 (nil) 6491 (nil))) 6521 (node 3 (node 1 (nil) 6529 (nil)) 6547 (node 1 (nil) 6551 (nil)))) 6553 (node 7 (node 3 (node 1 (nil) 6563 (nil)) 6569 (node 1 (nil) 6571 (nil))) 6577 (node 3 (node 1 (nil) 6581 (nil)) 6599 (node 1 (nil) 6607 (nil)))))))) 6619 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 6637 (nil)) 6653 (node 1 (nil) 6659 (nil))) 6661 (node 3 (node 1 (nil) 6673 (nil)) 6679 (node 1 (nil) 6689 (nil)))) 6691 (node 7 (node 3 (node 1 (nil) 6701 (nil)) 6703 (node 1 (nil) 6709 (nil))) 6719 (node 3 (node 1 (nil) 6733 (nil)) 6737 (node 1 (nil) 6761 (nil))))) 6763 (node 15 (node 7 (node 3 (node 1 (nil) 6779 (nil)) 6781 (node 1 (nil) 6791 (nil))) 6793 (node 3 (node 1 (nil) 6803 (nil)) 6823 (node 1 (nil) 6827 (nil)))) 6829 (node 7 (node 3 (node 1 (nil) 6833 (nil)) 6841 (node 1 (nil) 6857 (nil))) 6863 (node 3 (node 1 (nil) 6869 (nil)) 6871 (node 1 (nil) 6883 (nil)))))) 6899 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 6907 (nil)) 6911 (node 1 (nil) 6917 (nil))) 6947 (node 3 (node 1 (nil) 6949 (nil)) 6959 (node 1 (nil) 6961 (nil)))) 6967 (node 7 (node 3 (node 1 (nil) 6971 (nil)) 6977 (node 1 (nil) 6983 (nil))) 6991 (node 3 (node 1 (nil) 6997 (nil)) 7001 (node 1 (nil) 7013 (nil))))) 7019 (node 15 (node 7 (node 3 (node 1 (nil) 7027 (nil)) 7039 (node 1 (nil) 7043 (nil))) 7057 (node 3 (node 1 (nil) 7069 (nil)) 7079 (node 1 (nil) 7103 (nil)))) 7109 (node 7 (node 3 (node 1 (nil) 7121 (nil)) 7127 (node 1 (nil) 7129 (nil))) 7151 (node 3 (node 1 (nil) 7159 (nil)) 7177 (node 1 (nil) 7187 (nil))))))) 7193 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 7207 (nil)) 7211 (node 1 (nil) 7213 (nil))) 7219 (node 3 (node 1 (nil) 7229 (nil)) 7237 (node 1 (nil) 7243 (nil)))) 7247 (node 7 (node 3 (node 1 (nil) 7253 (nil)) 7283 (node 1 (nil) 7297 (nil))) 7307 (node 3 (node 1 (nil) 7309 (nil)) 7321 (node 1 (nil) 7331 (nil))))) 7333 (node 15 (node 7 (node 3 (node 1 (nil) 7349 (nil)) 7351 (node 1 (nil) 7369 (nil))) 7393 (node 3 (node 1 (nil) 7411 (nil)) 7417 (node 1 (nil) 7433 (nil)))) 7451 (node 7 (node 3 (node 1 (nil) 7457 (nil)) 7459 (node 1 (nil) 7477 (nil))) 7481 (node 3 (node 1 (nil) 7487 (nil)) 7489 (node 1 (nil) 7499 (nil)))))) 7507 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 7517 (nil)) 7523 (node 1 (nil) 7529 (nil))) 7537 (node 3 (node 1 (nil) 7541 (nil)) 7547 (node 1 (nil) 7549 (nil)))) 7559 (node 7 (node 3 (node 1 (nil) 7561 (nil)) 7573 (node 1 (nil) 7577 (nil))) 7583 (node 3 (node 1 (nil) 7589 (nil)) 7591 (node 1 (nil) 7603 (nil))))) 7607 (node 15 (node 7 (node 3 (node 1 (nil) 7621 (nil)) 7639 (node 1 (nil) 7643 (nil))) 7649 (node 3 (node 1 (nil) 7669 (nil)) 7673 (node 1 (nil) 7681 (nil)))) 7687 (node 7 (node 3 (node 1 (nil) 7691 (nil)) 7699 (node 1 (nil) 7703 (nil))) 7717 (node 3 (node 1 (nil) 7723 (nil)) 7727 (node 1 (nil) 7741 (nil))))))))) 7753 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 7757 (nil)) 7759 (node 1 (nil) 7789 (nil))) 7793 (node 3 (node 1 (nil) 7817 (nil)) 7823 (node 1 (nil) 7829 (nil)))) 7841 (node 7 (node 3 (node 1 (nil) 7853 (nil)) 7867 (node 1 (nil) 7873 (nil))) 7877 (node 3 (node 1 (nil) 7879 (nil)) 7883 (node 1 (nil) 7901 (nil))))) 7907 (node 15 (node 7 (node 3 (node 1 (nil) 7919 (nil)) 7927 (node 1 (nil) 7933 (nil))) 7937 (node 3 (node 1 (nil) 7949 (nil)) 7951 (node 1 (nil) 7963 (nil)))) 7993 (node 7 (node 3 (node 1 (nil) 8009 (nil)) 8011 (node 1 (nil) 8017 (nil))) 8039 (node 3 (node 1 (nil) 8053 (nil)) 8059 (node 1 (nil) 8069 (nil)))))) 8081 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 8087 (nil)) 8089 (node 1 (nil) 8093 (nil))) 8101 (node 3 (node 1 (nil) 8111 (nil)) 8117 (node 1 (nil) 8123 (nil)))) 8147 (node 7 (node 3 (node 1 (nil) 8161 (nil)) 8167 (node 1 (nil) 8171 (nil))) 8179 (node 3 (node 1 (nil) 8191 (nil)) 8209 (node 1 (nil) 8219 (nil))))) 8221 (node 15 (node 7 (node 3 (node 1 (nil) 8231 (nil)) 8233 (node 1 (nil) 8237 (nil))) 8243 (node 3 (node 1 (nil) 8263 (nil)) 8269 (node 1 (nil) 8273 (nil)))) 8287 (node 7 (node 3 (node 1 (nil) 8291 (nil)) 8293 (node 1 (nil) 8297 (nil))) 8311 (node 3 (node 1 (nil) 8317 (nil)) 8329 (node 1 (nil) 8353 (nil))))))) 8363 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 8369 (nil)) 8377 (node 1 (nil) 8387 (nil))) 8389 (node 3 (node 1 (nil) 8419 (nil)) 8423 (node 1 (nil) 8429 (nil)))) 8431 (node 7 (node 3 (node 1 (nil) 8443 (nil)) 8447 (node 1 (nil) 8461 (nil))) 8467 (node 3 (node 1 (nil) 8501 (nil)) 8513 (node 1 (nil) 8521 (nil))))) 8527 (node 15 (node 7 (node 3 (node 1 (nil) 8537 (nil)) 8539 (node 1 (nil) 8543 (nil))) 8563 (node 3 (node 1 (nil) 8573 (nil)) 8581 (node 1 (nil) 8597 (nil)))) 8599 (node 7 (node 3 (node 1 (nil) 8609 (nil)) 8623 (node 1 (nil) 8627 (nil))) 8629 (node 3 (node 1 (nil) 8641 (nil)) 8647 (node 1 (nil) 8663 (nil)))))) 8669 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 8677 (nil)) 8681 (node 1 (nil) 8689 (nil))) 8693 (node 3 (node 1 (nil) 8699 (nil)) 8707 (node 1 (nil) 8713 (nil)))) 8719 (node 7 (node 3 (node 1 (nil) 8731 (nil)) 8737 (node 1 (nil) 8741 (nil))) 8747 (node 3 (node 1 (nil) 8753 (nil)) 8761 (node 1 (nil) 8779 (nil))))) 8783 (node 15 (node 7 (node 3 (node 1 (nil) 8803 (nil)) 8807 (node 1 (nil) 8819 (nil))) 8821 (node 3 (node 1 (nil) 8831 (nil)) 8837 (node 1 (nil) 8839 (nil)))) 8849 (node 7 (node 3 (node 1 (nil) 8861 (nil)) 8863 (node 1 (nil) 8867 (nil))) 8887 (node 3 (node 1 (nil) 8893 (nil)) 8923 (node 1 (nil) 8929 (nil)))))))) 8933 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 8941 (nil)) 8951 (node 1 (nil) 8963 (nil))) 8969 (node 3 (node 1 (nil) 8971 (nil)) 8999 (node 1 (nil) 9001 (nil)))) 9007 (node 7 (node 3 (node 1 (nil) 9011 (nil)) 9013 (node 1 (nil) 9029 (nil))) 9041 (node 3 (node 1 (nil) 9043 (nil)) 9049 (node 1 (nil) 9059 (nil))))) 9067 (node 15 (node 7 (node 3 (node 1 (nil) 9091 (nil)) 9103 (node 1 (nil) 9109 (nil))) 9127 (node 3 (node 1 (nil) 9133 (nil)) 9137 (node 1 (nil) 9151 (nil)))) 9157 (node 7 (node 3 (node 1 (nil) 9161 (nil)) 9173 (node 1 (nil) 9181 (nil))) 9187 (node 3 (node 1 (nil) 9199 (nil)) 9203 (node 1 (nil) 9209 (nil)))))) 9221 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 9227 (nil)) 9239 (node 1 (nil) 9241 (nil))) 9257 (node 3 (node 1 (nil) 9277 (nil)) 9281 (node 1 (nil) 9283 (nil)))) 9293 (node 7 (node 3 (node 1 (nil) 9311 (nil)) 9319 (node 1 (nil) 9323 (nil))) 9337 (node 3 (node 1 (nil) 9341 (nil)) 9343 (node 1 (nil) 9349 (nil))))) 9371 (node 15 (node 7 (node 3 (node 1 (nil) 9377 (nil)) 9391 (node 1 (nil) 9397 (nil))) 9403 (node 3 (node 1 (nil) 9413 (nil)) 9419 (node 1 (nil) 9421 (nil)))) 9431 (node 7 (node 3 (node 1 (nil) 9433 (nil)) 9437 (node 1 (nil) 9439 (nil))) 9461 (node 3 (node 1 (nil) 9463 (nil)) 9467 (node 1 (nil) 9473 (nil))))))) 9479 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 9491 (nil)) 9497 (node 1 (nil) 9511 (nil))) 9521 (node 3 (node 1 (nil) 9533 (nil)) 9539 (node 1 (nil) 9547 (nil)))) 9551 (node 7 (node 3 (node 1 (nil) 9587 (nil)) 9601 (node 1 (nil) 9613 (nil))) 9619 (node 3 (node 1 (nil) 9623 (nil)) 9629 (node 1 (nil) 9631 (nil))))) 9643 (node 15 (node 7 (node 3 (node 1 (nil) 9649 (nil)) 9661 (node 1 (nil) 9677 (nil))) 9679 (node 3 (node 1 (nil) 9689 (nil)) 9697 (node 1 (nil) 9719 (nil)))) 9721 (node 7 (node 3 (node 1 (nil) 9733 (nil)) 9739 (node 1 (nil) 9743 (nil))) 9749 (node 3 (node 1 (nil) 9767 (nil)) 9769 (node 1 (nil) 9781 (nil)))))) 9787 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 9791 (nil)) 9803 (node 1 (nil) 9811 (nil))) 9817 (node 3 (node 1 (nil) 9829 (nil)) 9833 (node 1 (nil) 9839 (nil)))) 9851 (node 7 (node 3 (node 1 (nil) 9857 (nil)) 9859 (node 1 (nil) 9871 (nil))) 9883 (node 3 (node 1 (nil) 9887 (nil)) 9901 (node 1 (nil) 9907 (nil))))) 9923 (node 15 (node 7 (node 3 (node 1 (nil) 9929 (nil)) 9931 (node 1 (nil) 9941 (nil))) 9949 (node 3 (node 1 (nil) 9967 (nil)) 9973 (node 1 (nil) 10007 (nil)))) 10009 (node 7 (node 3 (node 1 (nil) 10037 (nil)) 10039 (node 1 (nil) 10061 (nil))) 10067 (node 3 (node 1 (nil) 10069 (nil)) 10079 (node 1 (nil) 10091 (nil))))))))))) 10093 (node 1023 (node 511 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 10099 (nil)) 10103 (node 1 (nil) 10111 (nil))) 10133 (node 3 (node 1 (nil) 10139 (nil)) 10141 (node 1 (nil) 10151 (nil)))) 10159 (node 7 (node 3 (node 1 (nil) 10163 (nil)) 10169 (node 1 (nil) 10177 (nil))) 10181 (node 3 (node 1 (nil) 10193 (nil)) 10211 (node 1 (nil) 10223 (nil))))) 10243 (node 15 (node 7 (node 3 (node 1 (nil) 10247 (nil)) 10253 (node 1 (nil) 10259 (nil))) 10267 (node 3 (node 1 (nil) 10271 (nil)) 10273 (node 1 (nil) 10289 (nil)))) 10301 (node 7 (node 3 (node 1 (nil) 10303 (nil)) 10313 (node 1 (nil) 10321 (nil))) 10331 (node 3 (node 1 (nil) 10333 (nil)) 10337 (node 1 (nil) 10343 (nil)))))) 10357 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 10369 (nil)) 10391 (node 1 (nil) 10399 (nil))) 10427 (node 3 (node 1 (nil) 10429 (nil)) 10433 (node 1 (nil) 10453 (nil)))) 10457 (node 7 (node 3 (node 1 (nil) 10459 (nil)) 10463 (node 1 (nil) 10477 (nil))) 10487 (node 3 (node 1 (nil) 10499 (nil)) 10501 (node 1 (nil) 10513 (nil))))) 10529 (node 15 (node 7 (node 3 (node 1 (nil) 10531 (nil)) 10559 (node 1 (nil) 10567 (nil))) 10589 (node 3 (node 1 (nil) 10597 (nil)) 10601 (node 1 (nil) 10607 (nil)))) 10613 (node 7 (node 3 (node 1 (nil) 10627 (nil)) 10631 (node 1 (nil) 10639 (nil))) 10651 (node 3 (node 1 (nil) 10657 (nil)) 10663 (node 1 (nil) 10667 (nil))))))) 10687 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 10691 (nil)) 10709 (node 1 (nil) 10711 (nil))) 10723 (node 3 (node 1 (nil) 10729 (nil)) 10733 (node 1 (nil) 10739 (nil)))) 10753 (node 7 (node 3 (node 1 (nil) 10771 (nil)) 10781 (node 1 (nil) 10789 (nil))) 10799 (node 3 (node 1 (nil) 10831 (nil)) 10837 (node 1 (nil) 10847 (nil))))) 10853 (node 15 (node 7 (node 3 (node 1 (nil) 10859 (nil)) 10861 (node 1 (nil) 10867 (nil))) 10883 (node 3 (node 1 (nil) 10889 (nil)) 10891 (node 1 (nil) 10903 (nil)))) 10909 (node 7 (node 3 (node 1 (nil) 10937 (nil)) 10939 (node 1 (nil) 10949 (nil))) 10957 (node 3 (node 1 (nil) 10973 (nil)) 10979 (node 1 (nil) 10987 (nil)))))) 10993 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 11003 (nil)) 11027 (node 1 (nil) 11047 (nil))) 11057 (node 3 (node 1 (nil) 11059 (nil)) 11069 (node 1 (nil) 11071 (nil)))) 11083 (node 7 (node 3 (node 1 (nil) 11087 (nil)) 11093 (node 1 (nil) 11113 (nil))) 11117 (node 3 (node 1 (nil) 11119 (nil)) 11131 (node 1 (nil) 11149 (nil))))) 11159 (node 15 (node 7 (node 3 (node 1 (nil) 11161 (nil)) 11171 (node 1 (nil) 11173 (nil))) 11177 (node 3 (node 1 (nil) 11197 (nil)) 11213 (node 1 (nil) 11239 (nil)))) 11243 (node 7 (node 3 (node 1 (nil) 11251 (nil)) 11257 (node 1 (nil) 11261 (nil))) 11273 (node 3 (node 1 (nil) 11279 (nil)) 11287 (node 1 (nil) 11299 (nil)))))))) 11311 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 11317 (nil)) 11321 (node 1 (nil) 11329 (nil))) 11351 (node 3 (node 1 (nil) 11353 (nil)) 11369 (node 1 (nil) 11383 (nil)))) 11393 (node 7 (node 3 (node 1 (nil) 11399 (nil)) 11411 (node 1 (nil) 11423 (nil))) 11437 (node 3 (node 1 (nil) 11443 (nil)) 11447 (node 1 (nil) 11467 (nil))))) 11471 (node 15 (node 7 (node 3 (node 1 (nil) 11483 (nil)) 11489 (node 1 (nil) 11491 (nil))) 11497 (node 3 (node 1 (nil) 11503 (nil)) 11519 (node 1 (nil) 11527 (nil)))) 11549 (node 7 (node 3 (node 1 (nil) 11551 (nil)) 11579 (node 1 (nil) 11587 (nil))) 11593 (node 3 (node 1 (nil) 11597 (nil)) 11617 (node 1 (nil) 11621 (nil)))))) 11633 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 11657 (nil)) 11677 (node 1 (nil) 11681 (nil))) 11689 (node 3 (node 1 (nil) 11699 (nil)) 11701 (node 1 (nil) 11717 (nil)))) 11719 (node 7 (node 3 (node 1 (nil) 11731 (nil)) 11743 (node 1 (nil) 11777 (nil))) 11779 (node 3 (node 1 (nil) 11783 (nil)) 11789 (node 1 (nil) 11801 (nil))))) 11807 (node 15 (node 7 (node 3 (node 1 (nil) 11813 (nil)) 11821 (node 1 (nil) 11827 (nil))) 11831 (node 3 (node 1 (nil) 11833 (nil)) 11839 (node 1 (nil) 11863 (nil)))) 11867 (node 7 (node 3 (node 1 (nil) 11887 (nil)) 11897 (node 1 (nil) 11903 (nil))) 11909 (node 3 (node 1 (nil) 11923 (nil)) 11927 (node 1 (nil) 11933 (nil))))))) 11939 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 11941 (nil)) 11953 (node 1 (nil) 11959 (nil))) 11969 (node 3 (node 1 (nil) 11971 (nil)) 11981 (node 1 (nil) 11987 (nil)))) 12007 (node 7 (node 3 (node 1 (nil) 12011 (nil)) 12037 (node 1 (nil) 12041 (nil))) 12043 (node 3 (node 1 (nil) 12049 (nil)) 12071 (node 1 (nil) 12073 (nil))))) 12097 (node 15 (node 7 (node 3 (node 1 (nil) 12101 (nil)) 12107 (node 1 (nil) 12109 (nil))) 12113 (node 3 (node 1 (nil) 12119 (nil)) 12143 (node 1 (nil) 12149 (nil)))) 12157 (node 7 (node 3 (node 1 (nil) 12161 (nil)) 12163 (node 1 (nil) 12197 (nil))) 12203 (node 3 (node 1 (nil) 12211 (nil)) 12227 (node 1 (nil) 12239 (nil)))))) 12241 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 12251 (nil)) 12253 (node 1 (nil) 12263 (nil))) 12269 (node 3 (node 1 (nil) 12277 (nil)) 12281 (node 1 (nil) 12289 (nil)))) 12301 (node 7 (node 3 (node 1 (nil) 12323 (nil)) 12329 (node 1 (nil) 12343 (nil))) 12347 (node 3 (node 1 (nil) 12373 (nil)) 12377 (node 1 (nil) 12379 (nil))))) 12391 (node 15 (node 7 (node 3 (node 1 (nil) 12401 (nil)) 12409 (node 1 (nil) 12413 (nil))) 12421 (node 3 (node 1 (nil) 12433 (nil)) 12437 (node 1 (nil) 12451 (nil)))) 12457 (node 7 (node 3 (node 1 (nil) 12473 (nil)) 12479 (node 1 (nil) 12487 (nil))) 12491 (node 3 (node 1 (nil) 12497 (nil)) 12503 (node 1 (nil) 12511 (nil))))))))) 12517 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 12527 (nil)) 12539 (node 1 (nil) 12541 (nil))) 12547 (node 3 (node 1 (nil) 12553 (nil)) 12569 (node 1 (nil) 12577 (nil)))) 12583 (node 7 (node 3 (node 1 (nil) 12589 (nil)) 12601 (node 1 (nil) 12611 (nil))) 12613 (node 3 (node 1 (nil) 12619 (nil)) 12637 (node 1 (nil) 12641 (nil))))) 12647 (node 15 (node 7 (node 3 (node 1 (nil) 12653 (nil)) 12659 (node 1 (nil) 12671 (nil))) 12689 (node 3 (node 1 (nil) 12697 (nil)) 12703 (node 1 (nil) 12713 (nil)))) 12721 (node 7 (node 3 (node 1 (nil) 12739 (nil)) 12743 (node 1 (nil) 12757 (nil))) 12763 (node 3 (node 1 (nil) 12781 (nil)) 12791 (node 1 (nil) 12799 (nil)))))) 12809 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 12821 (nil)) 12823 (node 1 (nil) 12829 (nil))) 12841 (node 3 (node 1 (nil) 12853 (nil)) 12889 (node 1 (nil) 12893 (nil)))) 12899 (node 7 (node 3 (node 1 (nil) 12907 (nil)) 12911 (node 1 (nil) 12917 (nil))) 12919 (node 3 (node 1 (nil) 12923 (nil)) 12941 (node 1 (nil) 12953 (nil))))) 12959 (node 15 (node 7 (node 3 (node 1 (nil) 12967 (nil)) 12973 (node 1 (nil) 12979 (nil))) 12983 (node 3 (node 1 (nil) 13001 (nil)) 13003 (node 1 (nil) 13007 (nil)))) 13009 (node 7 (node 3 (node 1 (nil) 13033 (nil)) 13037 (node 1 (nil) 13043 (nil))) 13049 (node 3 (node 1 (nil) 13063 (nil)) 13093 (node 1 (nil) 13099 (nil))))))) 13103 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 13109 (nil)) 13121 (node 1 (nil) 13127 (nil))) 13147 (node 3 (node 1 (nil) 13151 (nil)) 13159 (node 1 (nil) 13163 (nil)))) 13171 (node 7 (node 3 (node 1 (nil) 13177 (nil)) 13183 (node 1 (nil) 13187 (nil))) 13217 (node 3 (node 1 (nil) 13219 (nil)) 13229 (node 1 (nil) 13241 (nil))))) 13249 (node 15 (node 7 (node 3 (node 1 (nil) 13259 (nil)) 13267 (node 1 (nil) 13291 (nil))) 13297 (node 3 (node 1 (nil) 13309 (nil)) 13313 (node 1 (nil) 13327 (nil)))) 13331 (node 7 (node 3 (node 1 (nil) 13337 (nil)) 13339 (node 1 (nil) 13367 (nil))) 13381 (node 3 (node 1 (nil) 13397 (nil)) 13399 (node 1 (nil) 13411 (nil)))))) 13417 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 13421 (nil)) 13441 (node 1 (nil) 13451 (nil))) 13457 (node 3 (node 1 (nil) 13463 (nil)) 13469 (node 1 (nil) 13477 (nil)))) 13487 (node 7 (node 3 (node 1 (nil) 13499 (nil)) 13513 (node 1 (nil) 13523 (nil))) 13537 (node 3 (node 1 (nil) 13553 (nil)) 13567 (node 1 (nil) 13577 (nil))))) 13591 (node 15 (node 7 (node 3 (node 1 (nil) 13597 (nil)) 13613 (node 1 (nil) 13619 (nil))) 13627 (node 3 (node 1 (nil) 13633 (nil)) 13649 (node 1 (nil) 13669 (nil)))) 13679 (node 7 (node 3 (node 1 (nil) 13681 (nil)) 13687 (node 1 (nil) 13691 (nil))) 13693 (node 3 (node 1 (nil) 13697 (nil)) 13709 (node 1 (nil) 13711 (nil)))))))) 13721 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 13723 (nil)) 13729 (node 1 (nil) 13751 (nil))) 13757 (node 3 (node 1 (nil) 13759 (nil)) 13763 (node 1 (nil) 13781 (nil)))) 13789 (node 7 (node 3 (node 1 (nil) 13799 (nil)) 13807 (node 1 (nil) 13829 (nil))) 13831 (node 3 (node 1 (nil) 13841 (nil)) 13859 (node 1 (nil) 13873 (nil))))) 13877 (node 15 (node 7 (node 3 (node 1 (nil) 13879 (nil)) 13883 (node 1 (nil) 13901 (nil))) 13903 (node 3 (node 1 (nil) 13907 (nil)) 13913 (node 1 (nil) 13921 (nil)))) 13931 (node 7 (node 3 (node 1 (nil) 13933 (nil)) 13963 (node 1 (nil) 13967 (nil))) 13997 (node 3 (node 1 (nil) 13999 (nil)) 14009 (node 1 (nil) 14011 (nil)))))) 14029 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 14033 (nil)) 14051 (node 1 (nil) 14057 (nil))) 14071 (node 3 (node 1 (nil) 14081 (nil)) 14083 (node 1 (nil) 14087 (nil)))) 14107 (node 7 (node 3 (node 1 (nil) 14143 (nil)) 14149 (node 1 (nil) 14153 (nil))) 14159 (node 3 (node 1 (nil) 14173 (nil)) 14177 (node 1 (nil) 14197 (nil))))) 14207 (node 15 (node 7 (node 3 (node 1 (nil) 14221 (nil)) 14243 (node 1 (nil) 14249 (nil))) 14251 (node 3 (node 1 (nil) 14281 (nil)) 14293 (node 1 (nil) 14303 (nil)))) 14321 (node 7 (node 3 (node 1 (nil) 14323 (nil)) 14327 (node 1 (nil) 14341 (nil))) 14347 (node 3 (node 1 (nil) 14369 (nil)) 14387 (node 1 (nil) 14389 (nil))))))) 14401 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 14407 (nil)) 14411 (node 1 (nil) 14419 (nil))) 14423 (node 3 (node 1 (nil) 14431 (nil)) 14437 (node 1 (nil) 14447 (nil)))) 14449 (node 7 (node 3 (node 1 (nil) 14461 (nil)) 14479 (node 1 (nil) 14489 (nil))) 14503 (node 3 (node 1 (nil) 14519 (nil)) 14533 (node 1 (nil) 14537 (nil))))) 14543 (node 15 (node 7 (node 3 (node 1 (nil) 14549 (nil)) 14551 (node 1 (nil) 14557 (nil))) 14561 (node 3 (node 1 (nil) 14563 (nil)) 14591 (node 1 (nil) 14593 (nil)))) 14621 (node 7 (node 3 (node 1 (nil) 14627 (nil)) 14629 (node 1 (nil) 14633 (nil))) 14639 (node 3 (node 1 (nil) 14653 (nil)) 14657 (node 1 (nil) 14669 (nil)))))) 14683 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 14699 (nil)) 14713 (node 1 (nil) 14717 (nil))) 14723 (node 3 (node 1 (nil) 14731 (nil)) 14737 (node 1 (nil) 14741 (nil)))) 14747 (node 7 (node 3 (node 1 (nil) 14753 (nil)) 14759 (node 1 (nil) 14767 (nil))) 14771 (node 3 (node 1 (nil) 14779 (nil)) 14783 (node 1 (nil) 14797 (nil))))) 14813 (node 15 (node 7 (node 3 (node 1 (nil) 14821 (nil)) 14827 (node 1 (nil) 14831 (nil))) 14843 (node 3 (node 1 (nil) 14851 (nil)) 14867 (node 1 (nil) 14869 (nil)))) 14879 (node 7 (node 3 (node 1 (nil) 14887 (nil)) 14891 (node 1 (nil) 14897 (nil))) 14923 (node 3 (node 1 (nil) 14929 (nil)) 14939 (node 1 (nil) 14947 (nil)))))))))) 14951 (node 511 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 14957 (nil)) 14969 (node 1 (nil) 14983 (nil))) 15013 (node 3 (node 1 (nil) 15017 (nil)) 15031 (node 1 (nil) 15053 (nil)))) 15061 (node 7 (node 3 (node 1 (nil) 15073 (nil)) 15077 (node 1 (nil) 15083 (nil))) 15091 (node 3 (node 1 (nil) 15101 (nil)) 15107 (node 1 (nil) 15121 (nil))))) 15131 (node 15 (node 7 (node 3 (node 1 (nil) 15137 (nil)) 15139 (node 1 (nil) 15149 (nil))) 15161 (node 3 (node 1 (nil) 15173 (nil)) 15187 (node 1 (nil) 15193 (nil)))) 15199 (node 7 (node 3 (node 1 (nil) 15217 (nil)) 15227 (node 1 (nil) 15233 (nil))) 15241 (node 3 (node 1 (nil) 15259 (nil)) 15263 (node 1 (nil) 15269 (nil)))))) 15271 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 15277 (nil)) 15287 (node 1 (nil) 15289 (nil))) 15299 (node 3 (node 1 (nil) 15307 (nil)) 15313 (node 1 (nil) 15319 (nil)))) 15329 (node 7 (node 3 (node 1 (nil) 15331 (nil)) 15349 (node 1 (nil) 15359 (nil))) 15361 (node 3 (node 1 (nil) 15373 (nil)) 15377 (node 1 (nil) 15383 (nil))))) 15391 (node 15 (node 7 (node 3 (node 1 (nil) 15401 (nil)) 15413 (node 1 (nil) 15427 (nil))) 15439 (node 3 (node 1 (nil) 15443 (nil)) 15451 (node 1 (nil) 15461 (nil)))) 15467 (node 7 (node 3 (node 1 (nil) 15473 (nil)) 15493 (node 1 (nil) 15497 (nil))) 15511 (node 3 (node 1 (nil) 15527 (nil)) 15541 (node 1 (nil) 15551 (nil))))))) 15559 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 15569 (nil)) 15581 (node 1 (nil) 15583 (nil))) 15601 (node 3 (node 1 (nil) 15607 (nil)) 15619 (node 1 (nil) 15629 (nil)))) 15641 (node 7 (node 3 (node 1 (nil) 15643 (nil)) 15647 (node 1 (nil) 15649 (nil))) 15661 (node 3 (node 1 (nil) 15667 (nil)) 15671 (node 1 (nil) 15679 (nil))))) 15683 (node 15 (node 7 (node 3 (node 1 (nil) 15727 (nil)) 15731 (node 1 (nil) 15733 (nil))) 15737 (node 3 (node 1 (nil) 15739 (nil)) 15749 (node 1 (nil) 15761 (nil)))) 15767 (node 7 (node 3 (node 1 (nil) 15773 (nil)) 15787 (node 1 (nil) 15791 (nil))) 15797 (node 3 (node 1 (nil) 15803 (nil)) 15809 (node 1 (nil) 15817 (nil)))))) 15823 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 15859 (nil)) 15877 (node 1 (nil) 15881 (nil))) 15887 (node 3 (node 1 (nil) 15889 (nil)) 15901 (node 1 (nil) 15907 (nil)))) 15913 (node 7 (node 3 (node 1 (nil) 15919 (nil)) 15923 (node 1 (nil) 15937 (nil))) 15959 (node 3 (node 1 (nil) 15971 (nil)) 15973 (node 1 (nil) 15991 (nil))))) 16001 (node 15 (node 7 (node 3 (node 1 (nil) 16007 (nil)) 16033 (node 1 (nil) 16057 (nil))) 16061 (node 3 (node 1 (nil) 16063 (nil)) 16067 (node 1 (nil) 16069 (nil)))) 16073 (node 7 (node 3 (node 1 (nil) 16087 (nil)) 16091 (node 1 (nil) 16097 (nil))) 16103 (node 3 (node 1 (nil) 16111 (nil)) 16127 (node 1 (nil) 16139 (nil)))))))) 16141 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 16183 (nil)) 16187 (node 1 (nil) 16189 (nil))) 16193 (node 3 (node 1 (nil) 16217 (nil)) 16223 (node 1 (nil) 16229 (nil)))) 16231 (node 7 (node 3 (node 1 (nil) 16249 (nil)) 16253 (node 1 (nil) 16267 (nil))) 16273 (node 3 (node 1 (nil) 16301 (nil)) 16319 (node 1 (nil) 16333 (nil))))) 16339 (node 15 (node 7 (node 3 (node 1 (nil) 16349 (nil)) 16361 (node 1 (nil) 16363 (nil))) 16369 (node 3 (node 1 (nil) 16381 (nil)) 16411 (node 1 (nil) 16417 (nil)))) 16421 (node 7 (node 3 (node 1 (nil) 16427 (nil)) 16433 (node 1 (nil) 16447 (nil))) 16451 (node 3 (node 1 (nil) 16453 (nil)) 16477 (node 1 (nil) 16481 (nil)))))) 16487 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 16493 (nil)) 16519 (node 1 (nil) 16529 (nil))) 16547 (node 3 (node 1 (nil) 16553 (nil)) 16561 (node 1 (nil) 16567 (nil)))) 16573 (node 7 (node 3 (node 1 (nil) 16603 (nil)) 16607 (node 1 (nil) 16619 (nil))) 16631 (node 3 (node 1 (nil) 16633 (nil)) 16649 (node 1 (nil) 16651 (nil))))) 16657 (node 15 (node 7 (node 3 (node 1 (nil) 16661 (nil)) 16673 (node 1 (nil) 16691 (nil))) 16693 (node 3 (node 1 (nil) 16699 (nil)) 16703 (node 1 (nil) 16729 (nil)))) 16741 (node 7 (node 3 (node 1 (nil) 16747 (nil)) 16759 (node 1 (nil) 16763 (nil))) 16787 (node 3 (node 1 (nil) 16811 (nil)) 16823 (node 1 (nil) 16829 (nil))))))) 16831 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 16843 (nil)) 16871 (node 1 (nil) 16879 (nil))) 16883 (node 3 (node 1 (nil) 16889 (nil)) 16901 (node 1 (nil) 16903 (nil)))) 16921 (node 7 (node 3 (node 1 (nil) 16927 (nil)) 16931 (node 1 (nil) 16937 (nil))) 16943 (node 3 (node 1 (nil) 16963 (nil)) 16979 (node 1 (nil) 16981 (nil))))) 16987 (node 15 (node 7 (node 3 (node 1 (nil) 16993 (nil)) 17011 (node 1 (nil) 17021 (nil))) 17027 (node 3 (node 1 (nil) 17029 (nil)) 17033 (node 1 (nil) 17041 (nil)))) 17047 (node 7 (node 3 (node 1 (nil) 17053 (nil)) 17077 (node 1 (nil) 17093 (nil))) 17099 (node 3 (node 1 (nil) 17107 (nil)) 17117 (node 1 (nil) 17123 (nil)))))) 17137 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 17159 (nil)) 17167 (node 1 (nil) 17183 (nil))) 17189 (node 3 (node 1 (nil) 17191 (nil)) 17203 (node 1 (nil) 17207 (nil)))) 17209 (node 7 (node 3 (node 1 (nil) 17231 (nil)) 17239 (node 1 (nil) 17257 (nil))) 17291 (node 3 (node 1 (nil) 17293 (nil)) 17299 (node 1 (nil) 17317 (nil))))) 17321 (node 15 (node 7 (node 3 (node 1 (nil) 17327 (nil)) 17333 (node 1 (nil) 17341 (nil))) 17351 (node 3 (node 1 (nil) 17359 (nil)) 17377 (node 1 (nil) 17383 (nil)))) 17387 (node 7 (node 3 (node 1 (nil) 17389 (nil)) 17393 (node 1 (nil) 17401 (nil))) 17417 (node 3 (node 1 (nil) 17419 (nil)) 17431 (node 1 (nil) 17443 (nil))))))))) 17449 (node 255 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 17467 (nil)) 17471 (node 1 (nil) 17477 (nil))) 17483 (node 3 (node 1 (nil) 17489 (nil)) 17491 (node 1 (nil) 17497 (nil)))) 17509 (node 7 (node 3 (node 1 (nil) 17519 (nil)) 17539 (node 1 (nil) 17551 (nil))) 17569 (node 3 (node 1 (nil) 17573 (nil)) 17579 (node 1 (nil) 17581 (nil))))) 17597 (node 15 (node 7 (node 3 (node 1 (nil) 17599 (nil)) 17609 (node 1 (nil) 17623 (nil))) 17627 (node 3 (node 1 (nil) 17657 (nil)) 17659 (node 1 (nil) 17669 (nil)))) 17681 (node 7 (node 3 (node 1 (nil) 17683 (nil)) 17707 (node 1 (nil) 17713 (nil))) 17729 (node 3 (node 1 (nil) 17737 (nil)) 17747 (node 1 (nil) 17749 (nil)))))) 17761 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 17783 (nil)) 17789 (node 1 (nil) 17791 (nil))) 17807 (node 3 (node 1 (nil) 17827 (nil)) 17837 (node 1 (nil) 17839 (nil)))) 17851 (node 7 (node 3 (node 1 (nil) 17863 (nil)) 17881 (node 1 (nil) 17891 (nil))) 17903 (node 3 (node 1 (nil) 17909 (nil)) 17911 (node 1 (nil) 17921 (nil))))) 17923 (node 15 (node 7 (node 3 (node 1 (nil) 17929 (nil)) 17939 (node 1 (nil) 17957 (nil))) 17959 (node 3 (node 1 (nil) 17971 (nil)) 17977 (node 1 (nil) 17981 (nil)))) 17987 (node 7 (node 3 (node 1 (nil) 17989 (nil)) 18013 (node 1 (nil) 18041 (nil))) 18043 (node 3 (node 1 (nil) 18047 (nil)) 18049 (node 1 (nil) 18059 (nil))))))) 18061 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 18077 (nil)) 18089 (node 1 (nil) 18097 (nil))) 18119 (node 3 (node 1 (nil) 18121 (nil)) 18127 (node 1 (nil) 18131 (nil)))) 18133 (node 7 (node 3 (node 1 (nil) 18143 (nil)) 18149 (node 1 (nil) 18169 (nil))) 18181 (node 3 (node 1 (nil) 18191 (nil)) 18199 (node 1 (nil) 18211 (nil))))) 18217 (node 15 (node 7 (node 3 (node 1 (nil) 18223 (nil)) 18229 (node 1 (nil) 18233 (nil))) 18251 (node 3 (node 1 (nil) 18253 (nil)) 18257 (node 1 (nil) 18269 (nil)))) 18287 (node 7 (node 3 (node 1 (nil) 18289 (nil)) 18301 (node 1 (nil) 18307 (nil))) 18311 (node 3 (node 1 (nil) 18313 (nil)) 18329 (node 1 (nil) 18341 (nil)))))) 18353 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 18367 (nil)) 18371 (node 1 (nil) 18379 (nil))) 18397 (node 3 (node 1 (nil) 18401 (nil)) 18413 (node 1 (nil) 18427 (nil)))) 18433 (node 7 (node 3 (node 1 (nil) 18439 (nil)) 18443 (node 1 (nil) 18451 (nil))) 18457 (node 3 (node 1 (nil) 18461 (nil)) 18481 (node 1 (nil) 18493 (nil))))) 18503 (node 15 (node 7 (node 3 (node 1 (nil) 18517 (nil)) 18521 (node 1 (nil) 18523 (nil))) 18539 (node 3 (node 1 (nil) 18541 (nil)) 18553 (node 1 (nil) 18583 (nil)))) 18587 (node 7 (node 3 (node 1 (nil) 18593 (nil)) 18617 (node 1 (nil) 18637 (nil))) 18661 (node 3 (node 1 (nil) 18671 (nil)) 18679 (node 1 (nil) 18691 (nil)))))))) 18701 (node 127 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 18713 (nil)) 18719 (node 1 (nil) 18731 (nil))) 18743 (node 3 (node 1 (nil) 18749 (nil)) 18757 (node 1 (nil) 18773 (nil)))) 18787 (node 7 (node 3 (node 1 (nil) 18793 (nil)) 18797 (node 1 (nil) 18803 (nil))) 18839 (node 3 (node 1 (nil) 18859 (nil)) 18869 (node 1 (nil) 18899 (nil))))) 18911 (node 15 (node 7 (node 3 (node 1 (nil) 18913 (nil)) 18917 (node 1 (nil) 18919 (nil))) 18947 (node 3 (node 1 (nil) 18959 (nil)) 18973 (node 1 (nil) 18979 (nil)))) 19001 (node 7 (node 3 (node 1 (nil) 19009 (nil)) 19013 (node 1 (nil) 19031 (nil))) 19037 (node 3 (node 1 (nil) 19051 (nil)) 19069 (node 1 (nil) 19073 (nil)))))) 19079 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 19081 (nil)) 19087 (node 1 (nil) 19121 (nil))) 19139 (node 3 (node 1 (nil) 19141 (nil)) 19157 (node 1 (nil) 19163 (nil)))) 19181 (node 7 (node 3 (node 1 (nil) 19183 (nil)) 19207 (node 1 (nil) 19211 (nil))) 19213 (node 3 (node 1 (nil) 19219 (nil)) 19231 (node 1 (nil) 19237 (nil))))) 19249 (node 15 (node 7 (node 3 (node 1 (nil) 19259 (nil)) 19267 (node 1 (nil) 19273 (nil))) 19289 (node 3 (node 1 (nil) 19301 (nil)) 19309 (node 1 (nil) 19319 (nil)))) 19333 (node 7 (node 3 (node 1 (nil) 19373 (nil)) 19379 (node 1 (nil) 19381 (nil))) 19387 (node 3 (node 1 (nil) 19391 (nil)) 19403 (node 1 (nil) 19417 (nil))))))) 19421 (node 63 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 19423 (nil)) 19427 (node 1 (nil) 19429 (nil))) 19433 (node 3 (node 1 (nil) 19441 (nil)) 19447 (node 1 (nil) 19457 (nil)))) 19463 (node 7 (node 3 (node 1 (nil) 19469 (nil)) 19471 (node 1 (nil) 19477 (nil))) 19483 (node 3 (node 1 (nil) 19489 (nil)) 19501 (node 1 (nil) 19507 (nil))))) 19531 (node 15 (node 7 (node 3 (node 1 (nil) 19541 (nil)) 19543 (node 1 (nil) 19553 (nil))) 19559 (node 3 (node 1 (nil) 19571 (nil)) 19577 (node 1 (nil) 19583 (nil)))) 19597 (node 7 (node 3 (node 1 (nil) 19603 (nil)) 19609 (node 1 (nil) 19661 (nil))) 19681 (node 3 (node 1 (nil) 19687 (nil)) 19697 (node 1 (nil) 19699 (nil)))))) 19709 (node 31 (node 15 (node 7 (node 3 (node 1 (nil) 19717 (nil)) 19727 (node 1 (nil) 19739 (nil))) 19751 (node 3 (node 1 (nil) 19753 (nil)) 19759 (node 1 (nil) 19763 (nil)))) 19777 (node 7 (node 3 (node 1 (nil) 19793 (nil)) 19801 (node 1 (nil) 19813 (nil))) 19819 (node 3 (node 1 (nil) 19841 (nil)) 19843 (node 1 (nil) 19853 (nil))))) 19861 (node 15 (node 7 (node 3 (node 1 (nil) 19867 (nil)) 19889 (node 1 (nil) 19891 (nil))) 19913 (node 3 (node 1 (nil) 19919 (nil)) 19927 (node 1 (nil) 19937 (nil)))) 19949 (node 7 (node 3 (node 1 (nil) 19961 (nil)) 19963 (node 1 (nil) 19973 (nil))) 19979 (node 3 (node 1 (nil) 19991 (nil)) 19993 (node 1 (nil) 19997 (nil)))))))))))


lemma PTree_ofList : ofList (primesBelow20000.foldr (fun x y => x ++ y) []) = PTreeE := by rfl
lemma PTree_toList : PTreeE.toList = (primesBelow20000.foldr (fun x y => x ++ y) []) := by rfl

lemma PTree_bounded : PTreeE.Bounded ⊥ ⊤ := by
  rw [← PTree_ofList]
  exact Ordnode.ofList_bounded _


lemma primes_range (l₁ l₂ : ℕ) (hle : l₂ ≤ 20000) {p : ℕ} :
  p ∈ (Ordnode.extractRangeTree PTreeE (l₁ + 1) l₂).toList  ↔ Nat.Prime p ∧ l₁ < p ∧ p ≤ l₂ := by
  rw [Ordnode.extractRangeTree_toList_mem PTree_bounded,
    PTree_toList, primes_below_20000]
  apply Iff.intro
  · rintro ⟨⟨left, ⟨left_2, right_1⟩⟩, ⟨left_1, right⟩⟩
    simp_all only [and_true, true_and]
    exact left_1
  · rintro ⟨left, ⟨left_1, right⟩⟩
    simp_all only [true_and, and_true]
    exact ⟨⟨Nat.Prime.one_lt left, by omega⟩,  left_1 ⟩


example {p} :
  p ∈ [3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637,
    3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797,
    3803]  ↔ Nat.Prime p ∧ 3506 < p ∧ p ≤ 3804 := by
  convert primes_range 3506 3804 (by omega)


example {p} :
  p ∈ [13877, 13879, 13883, 13901, 13903, 13907, 13913, 13921, 13931, 13933, 13963, 13967, 13997, 13999,
  14009, 14011, 14029, 14033, 14051, 14057, 14071, 14081, 14083, 14087, 14107, 14143, 14149, 14153, 14159, 14173,
  14177, 14197, 14207, 14221, 14243, 14249, 14251, 14281, 14293, 14303, 14321, 14323, 14327, 14341, 14347, 14369, 14387, 14389, 14401, 14407, 14411, 14419, 14423, 14431, 14437, 14447, 14449, 14461, 14479,
  14489, 14503, 14519, 14533, 14537, 14543, 14549, 14551, 14557, 14561, 14563]  ↔ Nat.Prime p ∧ 13876 < p ∧ p ≤ 14565 := by
  convert primes_range 13876 14565 (by omega)
