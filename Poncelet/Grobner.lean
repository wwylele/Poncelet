import Mathlib

open scoped MonomialOrder

variable {K : Type*} [Field K]
variable {char : ℕ} {n : ℕ}

@[simp]
theorem Vector.get_zero {α : Type*} [Zero α] (i : Fin n) : (0 : Vector α n).get i = 0 := by
  change Vector.zero.get i = 0
  unfold zero
  simp

instance Vector.addCommMonoid {α : Type*} [AddCommMonoid α] :
    AddCommMonoid (Vector α n) where
  add_comm := Vector.add_comm _root_.add_comm
  add_assoc := Vector.add_assoc _root_.add_assoc
  zero_add := Vector.zero_add _root_.zero_add
  add_zero := Vector.add_zero _root_.add_zero
  nsmul := nsmulRec


attribute [-instance] Vector.instLE
attribute [-instance] Vector.instLT
attribute [-instance] Vector.instOrd

----- lex order ---------------------------------------------------------------------------

def Vector.lt {α : Type*} [LinearOrder α] (a b : Vector α n) : Bool :=
  List.lex a.toList b.toList

instance {α : Type*} [LinearOrder α] : LT (Vector α n) where
  lt a b := Vector.lt a b


instance {α : Type*} [LinearOrder α] : LE (Vector α n) where
  le a b := Vector.lt a b || a == b

theorem Vector.le_def {α : Type*} [LinearOrder α] (a b : Vector α n) :
    a ≤ b ↔ (Vector.lt a b || a == b) := by rfl

theorem Vector.lt_def {α : Type*} [LinearOrder α] (a b : Vector α n) :
    a < b ↔ Vector.lt a b := by rfl

instance {α : Type*} [LinearOrder α] : PartialOrder (Vector α n) where
  le_refl a := by
    simp [Vector.le_def]
  le_trans a b c hab hbc := by
    rw [Vector.le_def, Vector.lt] at ⊢ hab hbc
    simp [-Vector.lex_toList, -Vector.lt_toList] at ⊢ hab hbc
    grind
  le_antisymm a b hab hba := by
    rw [Vector.le_def, Vector.lt] at hab hba
    simp [-Vector.lex_toList, -Vector.lt_toList] at hab hba
    grind
  lt_iff_le_not_ge a b := by
    simp_rw [Vector.le_def, Vector.lt_def, Vector.lt]
    simp [-Vector.lex_toList, -Vector.lt_toList]
    grind

instance {α : Type*} [LinearOrder α] : LinearOrder (Vector α n) where
  le_total a b := by
    simp_rw [Vector.le_def,  Vector.lt]
    simp [-Vector.lex_toList, -Vector.lt_toList, ← Vector.toList_inj]
    grind
  toDecidableLE := by
    intro a b
    change Decidable (Vector.lt a b || a == b)
    infer_instance
  toDecidableLT := by
    intro a b
    change Decidable (Vector.lt a b)
    infer_instance

instance {α : Type*} [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid (Vector α n) := by
  apply IsOrderedCancelAddMonoid.of_add_lt_add_left
  intro a b c h
  change Vector.add a b < Vector.add a c
  rw [Vector.lt_def, Vector.lt] at ⊢ h
  simp_rw [Vector.add, Vector.toList_zipWith]
  set x := a.toList
  set y := b.toList
  set z := c.toList
  simp only [List.lex_eq_true_iff_lex, decide_eq_true_eq, List.lex_lt] at ⊢ h
  rw [List.lt_iff_exists] at ⊢ h
  convert h using 0
  have hc1 : (List.zipWith (fun x1 x2 ↦ x1 + x2) x y).length = y.length := by
    simp [x, y]
  have hc2 : ((List.zipWith (fun x1 x2 ↦ x1 + x2) x z).length) = z.length := by
    simp [x, z]
  simp_rw [hc1, hc2]
  congrm ?_ ∨ (∃ (i : ℕ) (h1 : _) (h2 : _), (∀ (j : ℕ) (hj : _), $(by simp)) ∧ $(by simp))
  simp [x, y ,z]

------------------------------------------------------------------------------------------

@[simp]
theorem Vector.get_add {α : Type*} [Add α] (a b : Vector α n) (i : Fin n) :
    (a + b).get i = a.get i + b.get i := by
  simp [Vector.get_eq_getElem]

class IsChar (char : ℕ) where
  eq_zero_or_prime : Nat.Prime char ∨ char = 0

instance : IsChar 0 where
  eq_zero_or_prime := Or.inr rfl

instance [h : Fact (Nat.Prime char)] : IsChar char where
  eq_zero_or_prime := Or.inl h.out

structure CMono (char : ℕ) (n : ℕ) where
  coeff : ℤ
  exp : Vector ℕ n
  coeff_ne_zero : ¬ (char : ℤ) ∣ coeff
deriving DecidableEq

instance [hchar : IsChar char] : Inhabited (CMono char n) where
  default := {
    coeff := 1
    exp := 0
    coeff_ne_zero := by
      have h := hchar.eq_zero_or_prime
      suffices char ≠ 1 by simpa [Int.natCast_dvd]
      contrapose h
      simp [h, Nat.not_prime_one]
  }

def CMono.eval (v : Fin n → K) (m : CMono char n) :=
  m.coeff * ∏ e : Fin n, v e ^ m.exp.get e

theorem CMono.eval_ne_zero [hchar : CharP K char]
    (v : Fin n → K) (m : CMono char n) (hm : m.exp = 0) :
    m.eval v ≠ 0 := by
  obtain h | h := CharP.char_is_prime_or_zero K char
  · simpa [eval, hm, CharP.intCast_eq_zero_iff] using m.coeff_ne_zero
  · have : CharP K 0 := h ▸ hchar
    have : CharZero K := CharP.charP_to_charZero K
    simpa [h, eval, hm] using m.coeff_ne_zero

def CMono.neg (a : CMono char n) : CMono char n where
  coeff := -a.coeff
  exp := a.exp
  coeff_ne_zero := by
    simpa using a.coeff_ne_zero

@[simp]
theorem CMono.eval_neg (a : CMono char n) (v : Fin n → K) :
    a.neg.eval v = -a.eval v := by
  simp [neg, eval]

@[simp]
theorem CMono.exp_neg (a : CMono char n) : a.neg.exp = a.exp := by
  simp [neg]

def CMono.mul [hc : IsChar char] (a b : CMono char n) : CMono char n where
  coeff := a.coeff * b.coeff
  exp := a.exp + b.exp
  coeff_ne_zero := by
    obtain hc | hc := hc.eq_zero_or_prime
    · rw [Int.natCast_dvd, Int.natAbs_mul]
      refine hc.not_dvd_mul ?_ ?_
      · simpa [← Int.natCast_dvd] using a.coeff_ne_zero
      · simpa [← Int.natCast_dvd] using b.coeff_ne_zero
    · obtain ha := a.coeff_ne_zero
      obtain hb := b.coeff_ne_zero
      simp_all

instance [IsChar char] : Mul (CMono char n) where
  mul := CMono.mul

@[simp]
theorem CMono.eval_mul [IsChar char] (v : Fin n → K) (a b : CMono char n) :
    (a * b).eval v = a.eval v * b.eval v := by
  change (mul a b).eval v = a.eval v * b.eval v
  simp_rw [mul, eval]
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  simp_rw [Vector.get_add, pow_add]
  norm_cast

@[simp]
theorem CMono.exp_mul [IsChar char] (a b : CMono char n) :
    (a * b).exp = a.exp + b.exp := by
  rfl

def ea : CMono 0 3 := ⟨
    5,
    #v[1,2,3],
    by simp
⟩

structure CPoly (char : ℕ) (n : ℕ) where
  terms : List (CMono char n)
  ordered : terms.Pairwise (fun a b ↦ b.exp < a.exp)
deriving DecidableEq

instance : Zero (CPoly char n) where
  zero := {
    terms := []
    ordered := by simp
  }

def CPoly.of (terms : List (CMono char n))
    (hterms : (terms.map (·.exp)).Nodup) :
    CPoly char n where
  terms := terms.mergeSort (fun a b ↦ b.exp ≤ a.exp)
  ordered := by
    simp_rw [lt_iff_le_and_ne]
    refine List.Pairwise.and ?_ ?_
    · have : IsTrans (CMono char n) (fun a b ↦ b.exp ≤ a.exp) := {
        trans a b c hab hbc := by simpa using le_trans hbc hab
      }
      have : Std.Total (fun (a : CMono char n) b ↦ b.exp ≤ a.exp) := {
        total a b := by apply le_total
      }
      apply List.pairwise_mergeSort'
    · suffices terms.Pairwise
          (fun a b ↦ b.exp ≠ a.exp) by
        apply List.Pairwise.perm this (List.mergeSort_perm _ _).symm (by grind)
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hterms
      apply (List.Pairwise.iff ?_).mp hterms
      intro a b
      simp only [ne_eq]
      grind

def CPoly.eval {K : Type*} [Field K] (v : Fin n → K) (a : CPoly char n) : K :=
    (a.terms.map (CMono.eval v)).sum

@[simp]
theorem CPoly.eval_zero {K : Type*} [Field K] (v : Fin n → K) :
    CPoly.eval v 0 (char := char) = 0 := by
  simp [CPoly.eval, show terms 0 = [] from rfl]

def CPoly.addTerms (ab : List (CMono char n) × List (CMono char n)) : List (CMono char n) :=
  match ab with
  | ([], b) => b
  | (a, []) => a
  | (ax :: as, bx :: bs) =>
    if ax.exp < bx.exp then
      bx :: addTerms ⟨(ax :: as), bs⟩
    else if bx.exp < ax.exp then
      ax :: addTerms ⟨as, (bx :: bs)⟩
    else
      if h : ¬(char : ℤ) ∣ ax.coeff + bx.coeff then
        {
          coeff := ax.coeff + bx.coeff
          exp := ax.exp
          coeff_ne_zero := h
        } :: addTerms ⟨as, bs⟩
      else
        addTerms ⟨as, bs⟩

theorem CPoly.exists_exp_mem_addTerms {a b : List (CMono char n)}
    {c : CMono char n} (h : c ∈ addTerms ⟨a, b⟩) :
    (∃ d ∈ a, d.exp = c.exp) ∨ ∃ d ∈ b, d.exp = c.exp := by
  unfold addTerms at h
  cases a with
  | nil => exact Or.inr ⟨c, h, rfl⟩
  | cons ax as =>
  cases b with
  | nil => exact Or.inl ⟨c, h, rfl⟩
  | cons bx bs =>
  simp only at h
  split_ifs at h with h1 h2 h3
  · obtain hc | hc := List.mem_cons.mp h
    · exact Or.inr ⟨c, List.mem_cons.mpr (Or.inl hc), rfl⟩
    · obtain ⟨d, hd, heq⟩ | ⟨d, hd, heq⟩ := exists_exp_mem_addTerms hc
      · exact Or.inl ⟨d, hd, heq⟩
      · exact Or.inr ⟨d, List.mem_cons.mpr (Or.inr hd), heq⟩
  · obtain hc | hc := List.mem_cons.mp h
    · exact Or.inl ⟨c, List.mem_cons.mpr (Or.inl hc), rfl⟩
    · obtain ⟨d, hd, heq⟩ | ⟨d, hd, heq⟩ := exists_exp_mem_addTerms hc
      · exact Or.inl ⟨d, List.mem_cons.mpr (Or.inr hd), heq⟩
      · exact Or.inr ⟨d, hd, heq⟩
  · obtain ⟨d, hd, heq⟩ | ⟨d, hd, heq⟩ := exists_exp_mem_addTerms h
    · exact Or.inl ⟨d, List.mem_cons.mpr (Or.inr hd), heq⟩
    · exact Or.inr ⟨d, List.mem_cons.mpr (Or.inr hd), heq⟩
  · obtain hc | hc := List.mem_cons.mp h
    · exact Or.inl ⟨ax, by simp, by simp [hc]⟩
    · obtain ⟨d, hd, heq⟩ | ⟨d, hd, heq⟩ := exists_exp_mem_addTerms hc
      · exact Or.inl ⟨d, List.mem_cons.mpr (Or.inr hd), heq⟩
      · exact Or.inr ⟨d, List.mem_cons.mpr (Or.inr hd), heq⟩
termination_by a.length + b.length

theorem CPoly.ordered_addTerms {a b : List (CMono char n)}
    (ha : a.Pairwise (fun a b ↦ b.exp < a.exp))
    (hb : b.Pairwise (fun a b ↦ b.exp < a.exp)) :
    (addTerms ⟨a, b⟩).Pairwise (fun a b ↦ b.exp < a.exp) := by
  unfold addTerms
  cases a with
  | nil => exact hb
  | cons ax as =>
  cases b with
  | nil => exact ha
  | cons bx bs =>
  simp only
  split_ifs with h1 h2 h3
  · refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · rw [List.pairwise_cons] at ha hb
      intro c hc
      obtain ⟨d, hd, hdeq⟩ | ⟨d, hd, hdeq⟩ := exists_exp_mem_addTerms hc
      · rw [← hdeq]
        obtain hd | hd := List.mem_cons.mp hd
        · simpa [hd] using h1
        · exact (ha.1 _ hd).trans h1
      · rw [← hdeq]
        exact hb.1 _ hd
    · rw [List.pairwise_cons] at hb
      exact CPoly.ordered_addTerms ha hb.2
  · refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · rw [List.pairwise_cons] at ha hb
      intro c hc
      obtain ⟨d, hd, hdeq⟩ | ⟨d, hd, hdeq⟩ := exists_exp_mem_addTerms hc
      · rw [← hdeq]
        exact ha.1 _ hd
      · rw [← hdeq]
        obtain hd | hd := List.mem_cons.mp hd
        · simpa [hd] using h2
        · exact (hb.1 _ hd).trans h2
    · rw [List.pairwise_cons] at ha
      exact CPoly.ordered_addTerms ha.2 hb
  · rw [List.pairwise_cons] at ha hb
    exact CPoly.ordered_addTerms ha.2 hb.2
  · rw [List.pairwise_cons] at ha hb
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro c hc
      obtain ⟨d, hd, hdeq⟩ | ⟨d, hd, hdeq⟩ := exists_exp_mem_addTerms hc
      · rw [← hdeq]
        exact ha.1 _ hd
      · rw [← hdeq]
        apply (hb.1 _ hd).trans_eq
        simpa using le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    · exact CPoly.ordered_addTerms ha.2 hb.2
termination_by a.length + b.length

def CPoly.add (a b : CPoly char n) : CPoly char n := {
  terms := CPoly.addTerms ⟨a.terms, b.terms⟩
  ordered := CPoly.ordered_addTerms a.ordered b.ordered
}

instance : Add (CPoly char n) where
  add := CPoly.add

theorem CPoly.eval_addTerms [CharP K char] (v : Fin n → K) (a b : List (CMono char n)) :
    ((addTerms ⟨a, b⟩).map (CMono.eval v)).sum =
    (a.map (CMono.eval v)).sum + (b.map (CMono.eval v)).sum := by
  unfold addTerms
  cases a with
  | nil => simp
  | cons ax as =>
  cases b with
  | nil => simp
  | cons bx bs =>
  simp only
  split_ifs with h1 h2 h3
  · simp only [List.map_cons, List.sum_cons]
    rw [eval_addTerms]
    grind
  · simp only [List.map_cons, List.sum_cons]
    rw [eval_addTerms]
    grind
  · rw [← CharP.intCast_eq_zero_iff K char] at h3
    simp only [List.map_cons, List.sum_cons]
    rw [eval_addTerms]
    obtain h := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    unfold CMono.eval
    simp_rw [h]
    rw [add_add_add_comm, ← add_mul, ← Int.cast_add, h3]
    ring
  · simp only [List.map_cons, List.sum_cons]
    rw [eval_addTerms]
    obtain h := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    unfold CMono.eval
    simp [h]
    ring
termination_by a.length + b.length

@[simp]
theorem CPoly.eval_add [CharP K char] (v : Fin n → K) (a b : CPoly char n) :
    (a + b).eval v = a.eval v + b.eval v :=
  CPoly.eval_addTerms v a.terms b.terms

@[simp]
theorem CPoly.eval_listSum [CharP K char] (v : Fin n → K) (a : List (CPoly char n)) :
    a.sum.eval v = (a.map (eval v)).sum := by
  induction a with
  | nil => rfl
  | cons ax as ih =>
    simp [ih]

def CPoly.neg (a : CPoly char n) : CPoly char n where
  terms := a.terms.map CMono.neg
  ordered := by
    rw [List.pairwise_map]
    exact (List.Pairwise.iff (by simp)).mp a.ordered

instance : Neg (CPoly char n) where
  neg a := a.neg

@[simp]
theorem CPoly.eval_neg (v : Fin n → K) (a : CPoly char n) :
    (-a).eval v = -a.eval v := by
  change a.neg.eval v = -a.eval v
  simp only [eval, neg, List.map_map, List.sum_neg]
  congr
  ext i
  simp

instance : Sub (CPoly char n) where
  sub a b := a + -b

@[simp]
theorem CPoly.eval_sub [CharP K char] (v : Fin n → K) (a b : CPoly char n) :
    (a - b).eval v = a.eval v - b.eval v := by
  change (a + -b).eval v = a.eval v - b.eval v
  simp [sub_eq_add_neg]

def CPoly.smul [IsChar char] (s : CMono char n) (a : CPoly char n) : CPoly char n where
  terms := a.terms.map (s * ·)
  ordered := by
    rw [List.pairwise_map]
    exact (List.Pairwise.iff (by simp)).mp a.ordered

@[simp]
theorem CPoly.eval_smul [IsChar char] (v : Fin n → K) (s : CMono char n) (a : CPoly char n) :
    (smul s a).eval v = s.eval v * a.eval v := by
  simp_rw [smul, eval, ← List.sum_map_mul_left, List.map_map]
  congrm (List.map ?_ _).sum
  ext a
  simp

def CPoly.mul [IsChar char] (a b : CPoly char n) : CPoly char n :=
  (a.terms.map (smul · b)).sum

instance [IsChar char] : Mul (CPoly char n) where
  mul := CPoly.mul

@[simp]
theorem CPoly.eval_mul [CharP K char] (v : Fin n → K) (a b : CPoly char n) :
    have : IsChar char := ⟨CharP.char_is_prime_or_zero K char⟩
    (a * b).eval v = a.eval v * b.eval v := by
  have : IsChar char := ⟨CharP.char_is_prime_or_zero K char⟩
  change (mul a b).eval v = a.eval v * b.eval v
  simp only [mul, eval_listSum, List.map_map]
  unfold eval
  rw [← List.sum_map_mul_right]
  congrm (List.map ?_ _).sum
  ext b
  rw [← List.sum_map_mul_left, Function.comp_apply]
  congrm List.sum ?_
  simp [smul]

instance (c : ℕ) : OfNat (CPoly char n) c where
  ofNat := if h : ¬ (char : ℤ) ∣ c then
    {
      terms := [{
        coeff := c
        exp := 0
        coeff_ne_zero := h
      }]
      ordered := by simp
    }
  else
    0

@[simp]
theorem CPoly.eval_ofNat [CharP K char] (c : ℕ) (v : Fin n → K) :
    (ofNat(c) : CPoly char n).eval v = c := by
  by_cases! h : ¬ (char : ℤ) ∣ c
  · suffices c * ∏ x, v x ^ (0 : Vector ℕ n).get x + 0 = c by
      simpa [eval, OfNat.ofNat, h, CMono.eval]
    simp
  · suffices (0 : K) = c by
      simpa [eval, OfNat.ofNat, h, Zero.zero]
    symm
    simpa [ringChar.spec, ringChar.eq, Int.natCast_dvd, Int.natAbs_natCast] using h

instance : NatCast (CPoly char n) where
  natCast m := ofNat(m)

@[simp]
theorem CPoly.eval_natCast [CharP K char] (c : ℕ) (v : Fin n → K) :
    (c : CPoly char n).eval v = c :=
  CPoly.eval_ofNat c v

example : (7 : CPoly 0 4).eval ![1, 2 , 3, 4] = (7 : ℚ) := by simp

example : One (CPoly 0 4) := inferInstance

instance [IsChar char] : Pow (CPoly char n) ℕ where
  pow a m := npowRec m a

@[simp]
theorem CPoly.eval_npow [CharP K char] (v : Fin n → K) (a : CPoly char n) (m : ℕ) :
    have : IsChar char := ⟨CharP.char_is_prime_or_zero K char⟩
    (a ^ m).eval v = a.eval v ^ m := by
  have : IsChar char := ⟨CharP.char_is_prime_or_zero K char⟩
  change (npowRec m a).eval v = a.eval v ^ m
  induction m with
  | zero => simp [npowRec]
  | succ m ih =>
  rw [npowRec]
  simp [ih, pow_add]

def CPoly.X [hchar : IsChar char] (i : Fin n) : CPoly char n where
  terms := [{
    coeff := 1
    exp := (Vector.replicate n 0).set i 1
    coeff_ne_zero := by
      have h := hchar.eq_zero_or_prime
      suffices char ≠ 1 by simpa [Int.natCast_dvd]
      contrapose h
      simp [h, Nat.not_prime_one]
  }]
  ordered := by simp

@[simp]
theorem CPoly.eval_X [CharP K char] (v : Fin n → K) (i : Fin n) :
    have : IsChar char := ⟨CharP.char_is_prime_or_zero K char⟩
    (X i : CPoly char n).eval v = v i := by
  simp [X, eval, CMono.eval, Vector.get_eq_getElem, Vector.getElem_set, ← Fin.ext_iff]

def eb : CPoly 0 9 := ⟨[
  ⟨5, #v[7,6,3,2,4,3,1,4,7], by simp⟩,
  ⟨5, #v[5,6,3,2,4,3,1,4,7], by simp⟩,
  ⟨5, #v[5,5,3,2,4,3,1,8,7], by simp⟩,
  ⟨5, #v[3,5,3,2,4,3,1,8,7], by simp⟩,
  ⟨5, #v[3,4,3,2,4,3,1,8,7], by simp⟩,
  ⟨5, #v[3,4,2,2,4,3,1,8,7], by simp⟩,
  ⟨5, #v[1,4,3,2,4,3,1,8,7], by simp⟩,
  ⟨4, #v[1,2,2,2,4,3,1,8,7], by simp⟩,
  ⟨4, #v[1,2,2,1,4,3,1,8,7], by simp⟩,
  ⟨4, #v[1,2,1,2,4,3,1,8,7], by simp⟩,
  ⟨4, #v[1,0,1,2,4,3,1,8,7], by simp⟩,
  ⟨4, #v[0,0,1,2,4,3,1,8,7], by simp⟩],
  (by decide)⟩

def CPoly.reduce [hc : IsChar char] (a b : CPoly char n) : CPoly char n × Bool :=
  match b.terms with
  | [] => ⟨a, false⟩
  | bx :: bs =>
  match a.terms with
  | [] => ⟨a, false⟩
  | ax :: as =>
  if ax.exp - bx.exp + bx.exp = ax.exp then
    ⟨smul ⟨Int.lcm ax.coeff bx.coeff / ax.coeff, 0, by
      rw [Int.dvd_ediv_iff_mul_dvd (Int.dvd_lcm_left _ _)]
      by_contra!
      obtain h := dvd_of_mul_left_dvd this
      rw [Int.natCast_dvd, Int.lcm_eq_natAbs_lcm_natAbs, Int.natAbs_natCast] at h
      obtain hc | hc := hc.eq_zero_or_prime
      · rw [hc.dvd_lcm] at h
        simp [← Int.natCast_dvd, ax.coeff_ne_zero, bx.coeff_ne_zero] at h
      · obtain ha := ax.coeff_ne_zero
        obtain hb := bx.coeff_ne_zero
        simp_all⟩ a +
    smul ⟨-(Int.lcm ax.coeff bx.coeff / bx.coeff), ax.exp - bx.exp, by
      rw [dvd_neg, Int.dvd_ediv_iff_mul_dvd (Int.dvd_lcm_right _ _)]
      by_contra!
      obtain h := dvd_of_mul_left_dvd this
      rw [Int.natCast_dvd, Int.lcm_eq_natAbs_lcm_natAbs, Int.natAbs_natCast] at h
      obtain hc | hc := hc.eq_zero_or_prime
      · rw [hc.dvd_lcm] at h
        simp [← Int.natCast_dvd, ax.coeff_ne_zero, bx.coeff_ne_zero] at h
      · obtain ha := ax.coeff_ne_zero
        obtain hb := bx.coeff_ne_zero
        simp_all⟩ b, true⟩
  else
    ⟨a, false⟩

theorem CPoly.eq_zero_of_reduce_eq_zero [CharP K char]
    [IsChar char] {a b : CPoly char n} {v : Fin n → K}
    (hb : b.eval v = 0) (ha : (a.reduce b).1.eval v = 0) :
    a.eval v = 0 := by
  unfold reduce at ha
  cases hbeq : b.terms with
  | nil => simpa [hbeq] using ha
  | cons bx bs =>
  cases haeq : a.terms with
  | nil => simpa [hbeq, haeq] using ha
  | cons ax as =>
  simp only [hbeq, haeq] at ha
  split_ifs at ha with hsub
  · simp only [eval_add, eval_smul, hb, mul_zero, add_zero, mul_eq_zero] at ha
    apply Or.resolve_left ha
    apply CMono.eval_ne_zero
    simp
  · exact ha

def CPoly.reduceAll [IsChar char] (a : CPoly char n) (b : List (CPoly char n)) :
    CPoly char n × Bool :=
  match b with
  | [] => ⟨a, false⟩
  | bx :: bs =>
  match CPoly.reduceAll a bs with
  | ⟨a', r⟩ =>
  match a'.reduce bx with
  | ⟨a'', r'⟩ =>
  ⟨a'', r || r'⟩

theorem CPoly.eq_zero_of_reduceAll_eq_zero [CharP K char] [IsChar char] {a : CPoly char n}
    {b : List (CPoly char n)} {v : Fin n → K} (hb : b.Forall (·.eval v = 0))
    (ha : (a.reduceAll b).1.eval v = 0) :
    a.eval v = 0 := by
  induction b with
  | nil => simpa using ha
  | cons bx bs hi =>
    rw [List.forall_cons] at hb
    simp only [reduceAll] at ha
    exact hi hb.2 <| CPoly.eq_zero_of_reduce_eq_zero hb.1 ha

def CPoly.reduceRepeat
    [IsChar char] (a : CPoly char n) (b : List (CPoly char n))
    (fuel : ℕ) : CPoly char n :=
  match fuel with
  | 0 => a
  | n + 1 =>
  match a.reduceAll b with
  | ⟨a', false⟩ => a'
  | ⟨a', true⟩ => a'.reduceRepeat b n

theorem CPoly.eq_zero_of_reduceRepeat_eq_zero [CharP K char] [IsChar char] {a : CPoly char n}
    {b : List (CPoly char n)} {v : Fin n → K} (hb : b.Forall (·.eval v = 0))
    (fuel : ℕ) (ha : (a.reduceRepeat b fuel).eval v = 0) :
    a.eval v = 0 := by
  induction fuel generalizing a with
  | zero => simpa using ha
  | succ n ih =>
    rw [reduceRepeat] at ha
    split at ha
    · rename_i hd c d h
      apply eq_zero_of_reduceAll_eq_zero hb
      simpa [h] using ha
    · rename_i hd c d h
      apply eq_zero_of_reduceAll_eq_zero hb
      rw [h]
      apply ih ha
