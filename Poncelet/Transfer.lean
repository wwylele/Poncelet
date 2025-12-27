import Mathlib
import Poncelet.TransferAux

open WeierstrassCurve.Affine

variable (cf : Config)

theorem fabcNormal_o_sub (x y : cf.K) (hx : x ≠ 0) :
    fabcNormal cf (cf.u ^ 2 / (cf.r ^ 2 * x)) (cf.u ^ 2 * y / (cf.r ^ 2 * x ^ 2))
      = (cf.u ^ 3 / (cf.r ^ 3 * x ^ 3)) •
    ![2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y +
      (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2
      + 2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2),
    -cf.k * (2 * cf.r ^ 2 * (cf.r * x + cf.u) * y -
      (cf.r * x - cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2
      + 2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)),
    (cf.r * x + cf.u) * ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x)] := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  unfold fabcNormal
  simp only [Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty]
  congrm ![?_, ?_, ?_]
  · field
  · field
  · field

theorem fxyz_o_sub (p : (elliptic cf).Point) :
    fxyz cf (o cf - p) = fxyz cf p := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  have hp0 : fxyz cf (o cf) = fxyz cf 0 := by
    suffices P2.mk ![cf.u ^ 2 * (cf.u + cf.r), 0, cf.u ^ 2] _ = P2.mk ![cf.u + cf.r, 0, 1] _ by
      simpa [o, fxyz, fxyzRaw]
    rw [P2.mk_eq_mk]
    use cf.u ^ 2
    simpa using cf.hu
  cases p with
  | zero =>
    change fxyz cf (o cf - 0) = fxyz cf 0
    simp
  | @some x y hxy =>
    rw [nonsingular_elliptic cf] at hxy
    obtain ⟨heq, hs⟩ := hxy
    by_cases hx0 : x = 0
    · rw [(eq_o_iff cf hxy).mpr hx0]
      simp
    have hxo : Point.some hxy ≠ o cf := (eq_o_iff cf hxy).ne.mpr hx0
    unfold fxyz
    rw [P2.mk_eq_mk]
    use cf.u ^ 2 / (cf.r ^ 2 * x ^ 2)
    refine ⟨by simp [cf.hr, cf.hu, hx0], ?_⟩
    rw [o_sub cf hxy hxo]
    simp only [fxyzRaw, smul_eq_mul, Matrix.smul_cons, Matrix.smul_empty,
      Matrix.vecCons_inj, and_true]
    refine ⟨?_, ?_, ?_⟩
    · field
    · field
    · field

theorem f_o_sub_1 (i : cf.K) :
    P2.mk' ![1, i * cf.k, cf.u + cf.r] =
    P2.mk' (rChord' cf ![cf.u + cf.r, 0, 1] ![1, -i * cf.k, cf.u + cf.r]) := by
  by_cases hur : cf.u + cf.r = 0
  · have hur' : cf.r ^ 2 - cf.u ^ 2 = 0 := by grind
    simp [rChord', hur, hur']
  have hur' : 2 * cf.u * (cf.u + cf.r) + cf.r ^ 2 - cf.u ^ 2 ≠ 0 := by grind
  symm
  apply P2.mk'_eq_mk' hur'
  suffices 2 * (cf.u + cf.r) * (cf.u + cf.r) - (2 * cf.u * (cf.u + cf.r) + cf.r ^ 2 - cf.u ^ 2) =
      2 * cf.u * (cf.u + cf.r) + cf.r ^ 2 - cf.u ^ 2 by
    simpa [rChord', hur']
  ring

theorem SingularAbc.fabc_o_sub {x y : cf.K}
    (h : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y)
    (ho : Point.some hxy ≠ o cf) :
    fabc cf (o cf - .some hxy) = P2.mk ![8 * cf.u ^ 3 * cf.k,
      4 * (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * cf.u ^ 2, 0]
      (by simp [cf.hu, h.k_ne_zero cf hxy]) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  have hx0 : x ≠ 0 := (eq_o_iff cf hxy).ne.mp ho
  rw [o_sub cf _ ho]
  by_cases hs : SingularAbc cf (cf.u ^ 2 / (cf.r ^ 2 * x)) (cf.u ^ 2 * y / (cf.r ^ 2 * x ^ 2))
  · obtain hy := h.y_eq
    obtain hy' := congr(cf.r ^ 3 * x ^ 3 / cf.u ^ 3 * $hs.y_eq)
    have hy' : -2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y =
        (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
        2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2) := by
      convert hy' using 1
      · field
      · field
    have hy0 : 4 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y = 0 := by
      linear_combination hy - hy'
    obtain hx := h.c_factor_eq_zero cf hxy
    have hrxu : cf.r * x - cf.u ≠ 0 := by grind
    rw [nonsingular_elliptic cf] at hxy
    obtain ⟨heq, hnonsingular⟩ := hxy
    have hy0 : y = 0 := by
      obtain hur1 | hy0 : (cf.u + cf.r) ^ 2 - 1 = 0 ∨ y = 0 := by simpa [hrxu, cf.hr] using hy0
      · have hur1' : (cf.u + cf.r) ^ 2 = 1 := sub_eq_zero.mp hur1
        rw [hur1'] at hx
        have hrxu : (cf.r * x + cf.u) ^ 2 = 0 := by linear_combination hx
        have hrxu : -(cf.r * x) = cf.u := by simpa [neg_eq_iff_add_eq_zero] using hrxu
        have hrxu : x = -cf.u / cf.r := by simp [← hrxu, cf.hr]
        have hrxu' : x * (cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2) = 0 := by
          suffices cf.r ^ 2 * (-cf.u / cf.r) ^ 2
            + (1 - cf.u ^ 2 - cf.r ^ 2) * (-cf.u / cf.r) + cf.u ^ 2 = 0
            by simpa [hrxu, cf.hr, cf.hu]
          field_simp
          convert congr(cf.u * $hur1) using 1
          · ring
          · ring
        simpa [hrxu', cf.hr] using heq
      exact hy0
    have hx : cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2 = 0 := by
      simpa [hy0, hx0] using heq
    obtain hrxu | hrxu : cf.r * x + cf.u = 0 ∨
        cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x
        + (cf.u + cf.r) * cf.u ^ 2 = 0 := by
      simpa [hy0] using hy
    · grind
    have hurx : (cf.u - cf.r) * ((cf.u + cf.r) ^ 2 - 1) * x = 0 := by
      linear_combination hrxu - hx * (cf.u + cf.r)
    obtain hur | hur : cf.u - cf.r = 0 ∨ (cf.u + cf.r) ^ 2 - 1 = 0 := by simpa [hx0] using hurx
    · have hu : cf.u = cf.r := sub_eq_zero.mp hur
      have hs : SingularAbc cf (cf.r ^ 2 / (cf.r ^ 2 * x)) (cf.r ^ 2 * y / (cf.r ^ 2 * x ^ 2)) := by
        simpa [hu] using hs
      suffices P2.mk ![2 * cf.r * cf.k * (4 * cf.r ^ 2),
        -((cf.r * (cf.r + cf.r) ^ 2 * (cf.r ^ 2 / (cf.r ^ 2 * x))
        - cf.r * ((cf.r + cf.r) ^ 2 - 2)) * (4 * cf.r ^ 2)), 0] _ =
        P2.mk ![8 * cf.r ^ 3 * cf.k,
        4 * (cf.r * (cf.r + cf.r) ^ 2 * x - cf.r * ((cf.r + cf.r) ^ 2 - 2)) * cf.r ^ 2, 0] _ by
        simpa [fabc, fabcRaw, hs, hu]
      congrm P2.mk ![$(by ring), ?_, 0] _
      apply eq_of_sub_eq_zero
      rw [← mul_left_inj' hx0]
      convert congr(-16 * cf.r ^ 3 * $hx) using 1
      · simp_rw [hu]
        field
      · simp
    have hur : (cf.u + cf.r) ^ 2 = 1 := sub_eq_zero.mp hur
    have hk : cf.k = 0 := by simpa [hur] using cf.k_sq
    suffices P2.mk ![0,
        (cf.r * (cf.u ^ 2 / (cf.r ^ 2 * x)) - cf.u * (1 - 2))
          * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2), 0] _ =
        P2.mk ![0, 4 * (cf.r * x - cf.u * (1 - 2)) * cf.u ^ 2, 0] _ by
      simpa [fabc, fabcRaw, hs, hk, hur]
    rw [P2.mk_eq_mk']
    grind
  simp only [fabc, fabcRaw, hs, ↓reduceIte]
  simp_rw [← P2.mk'_eq]
  rw [fabcNormal_o_sub cf x y hx0]
  rw [P2.mk'_smul (by simp [cf.hu, cf.hr, hx0])]
  rw [h.c_factor_eq_zero cf hxy, mul_zero]
  rw [← h.y_eq, ← two_mul]
  rw [mul_sub (-cf.k)]
  simp_rw [neg_mul]
  rw [← h.y_eq', ← neg_add', ← two_mul]
  have : y ≠ 0 ∧ (cf.u + cf.r) ^ 2 - 1 ≠ 0 ∧ cf.r * x - cf.u ≠ 0 := by
    contrapose! hs
    apply SingularAbc.mk cf (nonsingular_o_sub cf hxy)
    · have : -2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y = 0 := by
        simp only [mul_eq_zero]
        grind
      obtain ha := h.a_eq_zero cf
      rw [this] at ha
      field_simp
      convert congr(cf.u ^ 3 * $ha) using 1
      · congrm (_ * ?_)
        grind
      · simp
    · field_simp
      grind [h.c_factor_eq_zero cf hxy]
  obtain ⟨hy, hur, huxr⟩ := this
  have hk : cf.k ≠ 0 := by
    rw [← sq_eq_zero_iff.ne]
    simpa [cf.k_sq] using hur
  have : cf.r ^ 2 * cf.k * (cf.r * x - cf.u) * y / (2 * cf.u ^ 3) ≠ 0 := by
    simp [cf.hr, hk, hy, cf.hu, huxr]
  apply P2.mk'_eq_mk' this
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_zero,
    Matrix.smul_empty, Matrix.vecCons_inj, and_true]
  constructor
  · field_simp
    rw [cf.k_sq]
    ring
  · field_simp
    apply eq_of_sub_eq_zero
    linear_combination -4 * (h.c_factor_eq_zero cf hxy)

theorem SingularAbc.f_o_sub {x y : cf.K}
    (hsxy : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y)
    (ho : Point.some hxy ≠ o cf) :
    f cf (o cf - .some hxy) = rChord cf (f cf (.some hxy)) := by
  suffices fabc cf (o cf - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' cf p q)) _
      (fxyz cf (.some hxy)) (fabc cf (.some hxy)) by
    simpa [rChord, f, fxyz_o_sub cf]
  rw [hsxy.fabc_o_sub cf hxy ho, hsxy.fxyz_eq cf, hsxy.fabc_eq cf]
  obtain hk := hsxy.k_ne_zero cf hxy
  have h0 : 2 * cf.u * (2 * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2))
      + cf.r ^ 2 * (4 * cf.u ^ 2 * cf.k) - cf.u ^ 2 * (4 * cf.u ^ 2 * cf.k) = 0 := by
    ring
  by_cases hur2 : cf.u ^ 2 - cf.r ^ 2 = 0
  · have h0' : cf.r ^ 2 * (4 * cf.u ^ 2 * cf.k) - cf.u ^ 2 * (4 * cf.u ^ 2 * cf.k) = 0 := by
      simpa [hur2] using h0
    suffices P2.mk ![8 * cf.u ^ 3 * cf.k,
        4 * (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * cf.u ^ 2, 0] _ =
      P2.mk ![2 * cf.u * cf.k * (4 * cf.u ^ 2),
        (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * (4 * cf.u ^ 2), 0] _ by
      simpa [rChord', h0', hk, cf.hu, hur2]
    congrm P2.mk ![?_, ?_, _] _
    · ring
    · ring
  suffices P2.mk ![8 * cf.u ^ 3 * cf.k,
      4 * (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * cf.u ^ 2, 0] _ =
    P2.mk ![(cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * (cf.u ^ 2 - cf.r ^ 2),
      -(2 * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2)), 0] _ by
    simpa [rChord', h0, hur2, cf.hu, hk]
  rw [P2.mk_eq_mk']
  use 8 * cf.u ^ 3 * cf.k /
    ((cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * (cf.u ^ 2 - cf.r ^ 2))
  simp only [Matrix.smul_cons, smul_eq_mul, mul_neg, mul_zero, Matrix.smul_empty,
    Matrix.vecCons_inj, and_true]
  have h0 : cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2) ≠ 0 := by
    rw [← sq_eq_zero_iff.ne, ← hsxy.x_relation cf hxy]
    simp [cf.hu, hk]
  constructor
  · field
  · field_simp
    rw [← hsxy.x_relation cf hxy]
    ring

theorem f_o_sub (p : (elliptic cf).Point) :
    f cf (o cf - p) = rChord cf (f cf p) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  -- check case when p = 0
  cases p with
  | zero =>
    rw [show o cf - Point.zero = o cf by rfl]
    suffices P2.mk ![1, cf.k, cf.u + cf.r] _ =
      P2.mk' (rChord' cf ![cf.u + cf.r, 0, 1] ![1, -cf.k, cf.u + cf.r]) by
      simpa [rChord, f, fxyz_o_sub cf]
    rw [← P2.mk'_eq]
    simpa using f_o_sub_1 cf 1
  | @some x y hxy =>
  -- check case when p = o
  by_cases ho : .some hxy = o cf
  · suffices P2.mk ![1, -cf.k, cf.u + cf.r] _ =
        P2.mk' (rChord' cf ![cf.u + cf.r, 0, 1] ![1, cf.k, cf.u + cf.r]) by
      simpa [rChord, f, fxyz_o_sub cf, ho]
    rw [← P2.mk'_eq]
    simpa using f_o_sub_1 cf (-1)
  have hx0 : x ≠ 0 := (eq_o_iff cf hxy).ne.mp ho
  -- check case when p is SingularAbc
  by_cases hsxy : SingularAbc cf x y
  · exact hsxy.f_o_sub cf hxy ho
  -- check case when o - p is SingularAbc
  have : ∃ (ox oy : cf.K) (hoxy : (elliptic cf).Nonsingular ox oy),
      o cf - .some hxy = .some hoxy := by
    cases h : o cf - .some hxy with
    | zero =>
      rw [Eq.comm, ← sub_eq_zero.not, h] at ho
      absurd ho
      rfl
    | @some ox oy hoxy =>
      exact ⟨ox, oy, hoxy, rfl⟩
  obtain ⟨ox, oy, hoxy, hoxyeq⟩ := this
  have hoo : .some hoxy ≠ o cf := by
    by_contra!
    simp [this] at hoxyeq
  by_cases hosxy : SingularAbc cf ox oy
  · rw [hoxyeq]
    have hoxyeq' : Point.some hxy = o cf - Point.some hoxy := by
      simp [← hoxyeq]
    rw [hoxyeq']
    rw [← (rChord_bijOn cf).injOn.eq_iff (mapsTo_f cf (by simp))
      (mapsTo_rChord cf (mapsTo_f cf (by simp)))]
    rw [rChord_rChord cf (mapsTo_f cf (by simp))]
    exact (hosxy.f_o_sub cf hoxy hoo).symm
  -- non-singular case
  suffices fabc cf (o cf - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' cf p q)) _
      (fxyz cf (Point.some hxy)) (fabc cf (Point.some hxy)) by
    simpa [rChord, f, fxyz_o_sub cf]
  rw [hoxyeq]
  suffices P2.mk (fabcNormal cf ox oy) _ =
      P2.mk' (rChord' cf (fxyzRaw cf (Point.some hxy)) (fabcNormal cf x y)) by
    simpa [fabc, fxyz, fabcRaw, hsxy, hosxy]
  rw [o_sub cf hxy ho, Point.some.injEq] at hoxyeq
  have hdeno : (cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x ≠ 0 := by
    by_contra! h
    obtain ha | ha := eq_or_eq_neg_of_sq_eq_sq _ _ <| presingular cf hxy h
    · contrapose! hsxy
      refine SingularAbc.mk cf hxy ?_ (by simp [h])
      linear_combination -ha
    · contrapose! hosxy
      rw [← hoxyeq.1, ← hoxyeq.2]
      refine SingularAbc.mk cf (nonsingular_o_sub cf hxy) ?_ ?_
      · field_simp
        linear_combination cf.u ^3 * ha
      · field_simp
        linear_combination cf.u ^ 3 * (cf.u + cf.r * x) * h
  have hne : 2 * cf.u * fxyzRaw cf (Point.some hxy) 0 + cf.r ^ 2 * fxyzRaw cf (Point.some hxy) 2 -
      cf.u ^ 2 * fxyzRaw cf (Point.some hxy) 2 ≠ 0 := by
    suffices 2 * cf.u * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
        2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) * x + cf.u ^ 2 * (cf.u + cf.r))
        + cf.r ^ 2 * (cf.r * x + cf.u) ^ 2 - cf.u ^ 2 * (cf.r * x + cf.u) ^ 2 ≠ 0 by
      simpa [fxyzRaw]
    contrapose! hdeno
    linear_combination hdeno
  rw [← P2.mk'_eq]
  rw [← hoxyeq.1, ← hoxyeq.2]
  have hl : (cf.r ^ 3 * x ^ 3 * ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x))
      / cf.u ^ 3 ≠ 0 := by
    simp [cf.hu, cf.hr, hx0, hdeno]
  symm
  apply P2.mk'_eq_mk' hl
  simp only [rChord', Fin.isValue, hne, ↓reduceIte]
  simp only [fxyzRaw, neg_mul, Fin.isValue, Matrix.cons_val_zero, fabcNormal, Matrix.cons_val,
    Matrix.cons_val_one, mul_neg, sub_neg_eq_add, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty,
    Matrix.vecCons_inj, and_true]
  exact ⟨by field, by field, by field⟩

theorem fabcNormal_w :
    fabcNormal cf (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 3) = ![
    cf.u ^ 3 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r) / cf.r ^ 3,
    -cf.k * cf.u ^ 3 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r) / cf.r ^ 3,
    (cf.u + cf.r) * cf.u ^ 3 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r) / cf.r ^ 3] := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]

@[simp]
theorem fabc_w : fabc cf (w cf) = P2.mk ![1, -cf.k, cf.u + cf.r] (by simp) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  unfold fabc
  rw [P2.mk_eq_mk']
  by_cases hs : SingularAbc cf (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 3)
  · obtain h := hs.c_factor_eq_zero cf (nonsingular_w cf)
    have h : (cf.u ^ 2 - cf.r ^ 2) ^ 2 = -4 * cf.u * cf.r := by
      field_simp at h
      grind
    suffices (cf.r * (cf.u + cf.r) ^ 2 * (cf.u ^ 2 / cf.r ^ 2) - cf.u * ((cf.u + cf.r) ^ 2 - 2)) *
        (-(4 * cf.u * cf.r) - 4 * cf.u ^ 2) =
        -(2 * cf.u * cf.k * (-(4 * cf.u * cf.r) + 4 * cf.u ^ 2) * cf.k) ∧
        8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2) =
        2 * cf.u * cf.k * (-(4 * cf.u * cf.r) + 4 * cf.u ^ 2) * (cf.u + cf.r) by
      simpa [fabcRaw, w, hs, h]
    constructor
    · have : -(2 * cf.u * cf.k * (-(4 * cf.u * cf.r) + 4 * cf.u ^ 2) * cf.k) =
        -(2 * cf.u * (-(4 * cf.u * cf.r) + 4 * cf.u ^ 2) * (cf.k ^ 2)) := by ring
      rw [this, cf.k_sq]
      field_simp
      linear_combination -h
    · ring
  simp [fabcRaw, w, hs, fabcNormal_w cf]
  grind

@[simp]
theorem fxyz_w : fxyz cf (w cf) =
    P2.mk ![(cf.u - cf.r) * (cf.u + cf.r) ^ 2 + 2 * cf.r, -2 * cf.k * cf.r, (cf.u + cf.r) ^ 2]
    (by
      by_cases h : cf.u + cf.r = 0
      · have h : cf.k ≠ 0 := by
          rw [← sq_eq_zero_iff.ne, cf.k_sq, h]
          simp
        simp [h, cf.hr]
      · simp [h]
    ) := by
  obtain _ := cf.hr
  simp only [fxyz, fxyzRaw, w]
  rw [P2.mk_eq_mk']
  use cf.u ^ 2 / cf.r ^ 2
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![$(by field), $(by field), $(by field)]

theorem fabcNormal_neg_w :
    fabcNormal cf (cf.u ^ 2 / cf.r ^ 2) (-cf.u ^ 2 / cf.r ^ 3) = ![
    cf.u ^ 3 * ((cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r) + 4 * cf.r ^ 2) / cf.r ^ 3,
    -cf.k * cf.u ^ 3 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2) / cf.r ^ 3,
    cf.u ^ 3 * (cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r) / cf.r ^ 3] := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]


theorem not_singularAbc_neg_w :
    ¬ SingularAbc cf (cf.u ^ 2 / cf.r ^ 2) (-cf.u ^ 2 / cf.r ^ 3) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  by_contra! h
  obtain ha := h.a_eq_zero
  obtain hc := h.c_factor_eq_zero cf (nonsingular_neg_w cf)
  field_simp at ha hc
  grind

theorem fabc_neg_w_ne_zero :
    ![(cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r) + 4 * cf.r ^ 2,
      -cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2),
      (cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r)] ≠ 0 := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain h := not_singularAbc_neg_w cf
  contrapose! h
  unfold SingularAbc fabcNormal
  obtain h := congr((cf.u ^ 3 / cf.r ^ 3) • $h)
  simp_rw [Matrix.smul_vec3, smul_zero, smul_eq_mul] at h
  refine Eq.trans ?_ h
  congrm ![$(by field), $(by field), $(by field)]

@[simp]
theorem fabc_neg_w :
    fabc cf (-w cf) = P2.mk ![
      (cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r) + 4 * cf.r ^ 2,
      -cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2),
      (cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r)] (fabc_neg_w_ne_zero cf) := by
  rw [neg_w]
  simp only [fabc, fabcRaw, not_singularAbc_neg_w cf, ↓reduceIte, fabcNormal_neg_w cf]
  rw [P2.mk_eq_mk']
  use cf.u ^ 3 / cf.r ^ 3
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · ring
  · ring
  · ring

@[simp]
theorem fxyz_neg_w : fxyz cf (-w cf) =
    P2.mk ![(cf.u - cf.r) * (cf.u + cf.r) ^ 2 + 2 * cf.r, 2 * cf.k * cf.r, (cf.u + cf.r) ^ 2]
    (by
      by_cases h : cf.u + cf.r = 0
      · have h : cf.k ≠ 0 := by
          rw [← sq_eq_zero_iff.ne, cf.k_sq, h]
          simp
        simp [h, cf.hr]
      · simp [h]
    ) := by
  obtain _ := cf.hr
  simp only [fxyz, fxyzRaw, w]
  rw [P2.mk_eq_mk']
  use cf.u ^ 2 / cf.r ^ 2
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![$(by field), $(?_), $(by field)]
  simp [elliptic]
  field

theorem fabcNormal_2w :
    fabcNormal cf ((cf.r ^ 2 - cf.u ^ 2) ^ 2 / (4 * cf.r ^ 2))
    ((cf.r ^ 2 - cf.u ^ 2) * ((cf.r ^ 2 - cf.u ^ 2) ^ 2
      - 2 * (cf.r ^ 2 + cf.u ^ 2)) / (8 * cf.r ^ 3)) =
    ![(cf.u + cf.r) * ((cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r) + 4 * cf.r ^ 2) *
      (((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u * cf.r) ^ 2 + 16 * cf.u * cf.r * (cf.u - cf.r) ^ 2) /
      (64 * cf.r ^ 3),
    -cf.k * (cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2) *
      (((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u * cf.r) ^ 2 + 16 * cf.u * cf.r * (cf.u - cf.r) ^ 2) /
      (64 * cf.r ^ 3),
    (cf.u + cf.r) ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r) *
      (((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u * cf.r) ^ 2 + 16 * cf.u * cf.r * (cf.u - cf.r) ^ 2) /
      (64 * cf.r ^ 3)] := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]

@[simp]
theorem fabc_2w :
    fabc cf (w cf + w cf) = P2.mk ![
      (cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r) + 4 * cf.r ^ 2,
      -cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2),
      (cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r)] (fabc_neg_w_ne_zero cf) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  rw [two_w]
  by_cases hsxy : SingularAbc cf ((cf.r ^ 2 - cf.u ^ 2) ^ 2 / (4 * cf.r ^ 2))
      ((cf.r ^ 2 - cf.u ^ 2) *
      ((cf.r ^ 2 - cf.u ^ 2) ^ 2 - 2 * (cf.r ^ 2 + cf.u ^ 2)) / (8 * cf.r ^ 3))
  · obtain hc := hsxy.c_factor_eq_zero cf (nonsingular_2w cf)
    field_simp at hc
    have hc : (cf.u + cf.r) ^ 2 *
        (((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u * cf.r) ^ 2 +
        16 * cf.u * cf.r * (cf.u - cf.r) ^ 2) = 0 := by
      linear_combination hc
    obtain hc | hc : cf.u + cf.r = 0 ∨
      ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u * cf.r) ^ 2 +
      16 * cf.u * cf.r * (cf.u - cf.r) ^ 2 = 0 := by simpa using hc
    · have hr : cf.r = -cf.u := (neg_eq_of_add_eq_zero_right hc).symm
      simp only [fabc, fabcRaw, hsxy, ↓reduceIte]
      suffices P2.mk ![2 * cf.u * cf.k * (4 * cf.u ^ 2), -(cf.u * 2 * (4 * cf.u ^ 2)), 0] _ =
          P2.mk ![4 * cf.u ^ 2, cf.k * (4 * cf.u ^ 2), 0] _ by
        simpa [hr]
      symm
      rw [P2.mk_eq_mk']
      use -cf.k / (2 * cf.u)
      simp_rw [Matrix.smul_vec3, smul_eq_mul, mul_zero]
      congrm ![?_ ,?_, 0]
      · field_simp
        simp [cf.k_sq, hr]
      · field_simp
    have hk : cf.k ≠ 0 := by
      grind
    have hur : cf.u - cf.r ≠ 0 := by
      grind
    suffices P2.mk
      ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
        (cf.r * (cf.u + cf.r) ^ 2 * ((cf.r ^ 2 - cf.u ^ 2) ^ 2 / (4 * cf.r ^ 2))
        - cf.u * ((cf.u + cf.r) ^ 2 - 2)) *
          ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
        8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)] _ =
      P2.mk
        ![(cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r) + 4 * cf.r ^ 2,
          -(cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2)),
          (cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r)] _ by
      simpa [fabc, fabcRaw, hsxy]
    symm
    rw [P2.mk_eq_mk']
    use ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r) / (8 * cf.u ^ 2 * cf.k * (cf.u - cf.r))
    simp_rw [Matrix.smul_vec3, smul_eq_mul]
    congrm ![?_, ?_, ?_]
    · field_simp
      grind
    · field_simp
      rw [cf.k_sq]
      grind
    · field
  simp only [fabc, fabcRaw, hsxy, ↓reduceIte, fabcNormal_2w cf]
  rw [P2.mk_eq_mk']
  use (cf.u + cf.r) * (((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u * cf.r) ^ 2
    + 16 * cf.u * cf.r * (cf.u - cf.r) ^ 2) / (64 * cf.r ^ 3)
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · ring
  · ring
  · ring

@[simp]
theorem fxyz_2w : fxyz cf (w cf + w cf) =
    P2.mk' ![((cf.u + cf.r) * ((cf.u - cf.r) ^ 4 * (cf.u + cf.r) ^ 4
      - 8 * cf.r ^ 2 * (cf.u - cf.r) ^ 2 * (cf.u + cf.r) ^ 2 +
      8 * cf.r * (cf.r ^ 3 - cf.r ^ 2 * cf.u + cf.r * cf.u ^ 2 + cf.u ^ 3))),
    4 * cf.r * cf.k * (cf.u^2 - cf.r^2) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 2 * (cf.u ^ 2 + cf.r ^ 2)),
    (cf.r^4 - 2 * cf.r^2 * cf.u^2 + 4 * cf.r * cf.u + cf.u^4)^2] := by
  obtain _ := cf.hr
  rw [two_w]
  obtain _ := cf.hr
  simp only [fxyz, fxyzRaw]
  have : 1 / (16 * cf.r ^ 2) ≠ 0 := by simpa using cf.hr
  rw [← P2.mk'_eq]
  apply P2.mk'_eq_mk' this
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · field
  · field
  · field

theorem fabc_w_sub_singularAbc {x y wx wy : cf.K}
    (hxy : (elliptic cf).Nonsingular x y) (hwxy : (elliptic cf).Nonsingular wx wy)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf)
    (hwxyeq : w cf - .some hxy = .some hwxy)
    (hsxy : SingularAbc cf x y) :
    fabc cf (.some hwxy) = fabc cf (.some hxy) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  have hadd : .some hxy + .some hwxy = w cf := by
    grind
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  by_cases hwsxy : SingularAbc cf wx wy
  · rw [w_sub cf hxy hx, Point.some.injEq] at hwxyeq
    obtain ⟨hwx, hwy⟩ := hwxyeq
    suffices P2.mk ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
        (cf.r * (cf.u + cf.r) ^ 2 * wx - cf.u * ((cf.u + cf.r) ^ 2 - 2)) *
        ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
        8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)] _ =
      P2.mk ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
        (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) *
        ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
        8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)] _ by
      simpa [fabc, fabcRaw, hsxy, hwsxy]
    obtain hlinear := hsxy.xy_linear cf hxy
    obtain hwlinear := hwsxy.xy_linear cf hwxy
    congrm P2.mk ![_, ?_, _] _
    suffices (wx = x ∨ cf.u + cf.r = 0) ∨ (cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2 = 0 by
      simpa [cf.hr]
    by_cases hur : cf.u + cf.r = 0
    · simp [hur]
    by_cases hxwx : x = wx
    · simp [hxwx]
    have : x - wx ≠ 0 := by
      simpa [sub_eq_zero] using hxwx
    have hslope : -2 * cf.r ^ 2 * (cf.u + cf.r) * (y - wy) =
        cf.r * (cf.u - cf.r) * ((cf.u + cf.r) ^ 2 - 2) * (x - wx) := by
      linear_combination hlinear - hwlinear
    have hslope : (elliptic cf).slope x wx y wy =
        -(cf.u - cf.r) * ((cf.u + cf.r) ^ 2 - 2) / (2 * cf.r * (cf.u + cf.r)) := by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxwx]
      field_simp
      rw [← mul_left_inj' cf.hr]
      linear_combination -hslope
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxwx] at hadd
    rw [w, Point.some.injEq, addX, hslope] at hadd
    obtain haddx := hadd.1
    have haddx : ((cf.r - cf.u) * ((cf.u + cf.r) ^ 2 - 2) / (2 * cf.r * (cf.u + cf.r))) ^ 2
        - (1 - cf.u ^ 2 - cf.r ^ 2) / cf.r ^ 2 - x - wx = cf.u ^ 2 / cf.r ^ 2 := by
      simpa [elliptic] using haddx
    rw [sub_sub _ x _] at haddx
    have hxx : x + wx = (2 * cf.u  * (cf.u + cf.r) ^ 2 - 4 * cf.u) / ((cf.u + cf.r) ^ 2 * cf.r) :=
      SingularAbc.c_factor_add cf hsxy hwsxy hxy hwxy hxwx hur
    rw [hxx] at haddx
    field_simp at haddx
    have : (cf.u + cf.r) ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2) = 0 := by
      linear_combination haddx
    obtain h | h : cf.u + cf.r = 0 ∨ (cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2 = 0 := by
      simpa using this
    · simp [h]
    · simp [h]
  have hk : cf.k ≠ 0 := hsxy.k_ne_zero cf hxy
  by_cases hur : cf.u ^ 2 - cf.r ^ 2 = 0
  · have hur : (cf.u + cf.r) * (cf.u - cf.r) = 0 := by linear_combination hur
    obtain hur | hur : cf.u + cf.r = 0 ∨ cf.u = cf.r := by simpa [sub_eq_zero] using hur
    · rw [w_sub cf hxy hx, Point.some.injEq] at hwxyeq
      obtain ⟨hwx, hwy⟩ := hwxyeq
      obtain hx0 := hsxy.x_eq_zero_of_casePos cf hxy hur
      obtain hy0 := hsxy.y_eq_zero_of_casePos cf hxy hur
      have hr : cf.r = -cf.u := by linear_combination hur
      suffices P2.mk (fabcNormal cf wx wy) _ =
        P2.mk ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
          (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) *
          ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
          8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)] _ by
        simpa [fabc, fabcRaw, hsxy, hwsxy]
      unfold fabcNormal
      symm
      rw [P2.mk_eq_mk']
      simp_rw [Matrix.smul_vec3, smul_eq_mul]
      use -2 * cf.u * cf.k
      simp_rw [← hwx, ← hwy, hx0, hy0, hr]
      congrm ![?_, ?_, ?_]
      · field
      · field_simp
        rw [cf.k_sq, hr]
        ring
      · field
    · exact fabc_w_sub_singularAbc_not_singularAbc_u_eq_r cf hxy hwxy hpw hpnw hwxyeq hsxy hwsxy hur
  exact fabc_w_sub_singularAbc_not_singularAbc cf hxy hwxy hpw hpnw hwxyeq hsxy hwsxy hur


theorem fabc_w_sub (p : (elliptic cf).Point) :
    fabc cf (w cf - p) = fabc cf p := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  cases p with
  | zero =>
    change fabc cf (w cf - 0) = fabc cf Point.zero
    simp
  | @some x y hxy =>
  by_cases hpw : .some hxy = w cf
  · simp [hpw]
  by_cases hpnw : .some hxy = -w cf
  · simp_rw [hpnw, sub_neg_eq_add, fabc_2w, fabc_neg_w]
  have : ∃ (wx wy : cf.K) (hwxy : (elliptic cf).Nonsingular wx wy),
      w cf - .some hxy = .some hwxy := by
    cases h : w cf - .some hxy with
    | zero =>
      rw [Eq.comm, ← sub_eq_zero.not, h] at hpw
      absurd hpw
      rfl
    | @some wx wy hwxy =>
      exact ⟨wx, wy, hwxy, rfl⟩
  obtain ⟨wx, wy, hwxy, hwxyeq⟩ := this
  have hww : .some hwxy ≠ w cf := by
    by_contra!
    simp [this] at hwxyeq
  rw [hwxyeq]
  by_cases hsxy : SingularAbc cf x y
  · exact fabc_w_sub_singularAbc cf hxy hwxy hpw hpnw hwxyeq hsxy
  by_cases hwsxy : SingularAbc cf wx wy
  · have hwxyeq' : w cf - Point.some hwxy = Point.some hxy := by
      simp [← hwxyeq]
    by_cases hww2 : Point.some hwxy = -w cf
    · simp_rw [← hwxyeq', hww2, sub_neg_eq_add, fabc_2w, fabc_neg_w]
    exact (fabc_w_sub_singularAbc cf hwxy hxy (by simp [← hwxyeq]) hww2 hwxyeq' hwsxy).symm
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  by_cases hinf : (cf.r * x + cf.u) *
    ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x) = 0
  · exact fabc_w_sub_c_eq_zero cf hxy hwxy hpw hpnw hwxyeq hsxy hwsxy hinf
  · exact fabc_w_sub_c_ne_zero cf hxy hwxy hpw hpnw hwxyeq hsxy hwsxy hinf

theorem f_w_eq_rPoint : f cf (w cf) = rPoint cf (f cf 0) := by
  suffices fxyz cf (w cf) =
    P2.mk' (rPoint' cf ![cf.u + cf.r, 0, 1] ![1, -cf.k, cf.u + cf.r]) by
    simpa [f, rPoint, fabc_w_sub]
  by_cases hur : cf.u + cf.r = 0
  · suffices P2.mk ![2 * cf.r, -(2 * cf.k * cf.r), 0] _ = P2.mk ![-cf.k, -1, 0] _ by
      simpa [rPoint', hur]
    rw [P2.mk_eq_mk']
    use 2 * cf.r * cf.k
    simp_rw [Matrix.smul_vec3, smul_eq_mul]
    congrm ![?_, $(by ring), $(by simp)]
    trans -2 * cf.r * cf.k ^ 2
    · simp [cf.k_sq, hur]
    ring
  suffices P2.mk ![(cf.u - cf.r) * (cf.u + cf.r) ^ 2 + 2 * cf.r,
      -(2 * cf.k * cf.r), (cf.u + cf.r) ^ 2] _ =
    P2.mk ![2 * (cf.u + cf.r) + 2 * cf.u * ((cf.u + cf.r) ^ 2 - 1)
      - (cf.u + cf.r) * (cf.u + cf.r) ^ 2,
      -(2 * cf.k * (cf.u + cf.r)) + 2 * cf.u * cf.k, (cf.u + cf.r) ^ 2] _ by
    simpa [rPoint', hur, cf.k_sq]
  rw [P2.mk_eq_mk']
  use 1
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![$(by ring), $(by ring), $(by simp)]

theorem f_two_w_eq_rPoint : f cf (w cf + w cf) = rPoint cf (f cf (-w cf)) := by
  by_cases hur : cf.u + cf.r = 0
  · have hr : cf.r = -cf.u := by linear_combination hur
    have hk : cf.k ≠ 0 := by
      rw [← sq_eq_zero_iff.ne, cf.k_sq, hr]
      simp
    suffices P2.mk' ![0, 0,
        ((-cf.u) ^ 4 - 2 * cf.u ^ 2 * cf.u ^ 2 + -(4 * cf.u * cf.u) + cf.u ^ 4) ^ 2] =
      P2.mk' ![0, 0, 2 * cf.u * (cf.k * (4 * cf.u ^ 2))] by
      simpa [f, rPoint, rPoint', hr]
    suffices P2.mk' ![0, 0, 16 * cf.u ^ 4] = P2.mk' ![0, 0, 8 * cf.u ^ 3 * cf.k] by
      convert this using 5
      · ring
      · ring
    have : 2 * cf.u / cf.k ≠ 0 := by simp [cf.hu, hk]
    apply P2.mk'_eq_mk' this
    simp
    field
  by_cases hur2 : (cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r = 0
  · have hk : cf.k ≠ 0 := by
      contrapose! hur2 with hk
      rw [← sq_eq_zero_iff, cf.k_sq, sub_eq_zero, sq_eq_one_iff] at hk
      obtain hur | hur := hk
      · have hr : cf.r = 1 - cf.u := by linear_combination hur
        rw [hr]
        ring_nf
        simp
      · have hr : cf.r = -1 - cf.u := by linear_combination hur
        rw [hr]
        ring_nf
        simp
    have h3 : (cf.r ^ 4 - 2 * cf.r ^ 2 * cf.u ^ 2 + 4 * cf.r * cf.u + cf.u ^ 4) ^ 2 = 0 := by
      linear_combination congr($hur2 ^ 2)
    suffices P2.mk'
      ![(cf.u + cf.r) *
        ((cf.u - cf.r) ^ 4 * (cf.u + cf.r) ^ 4
        - 8 * cf.r ^ 2 * (cf.u - cf.r) ^ 2 * (cf.u + cf.r) ^ 2 +
        8 * cf.r * (cf.r ^ 3 - cf.r ^ 2 * cf.u + cf.r * cf.u ^ 2 + cf.u ^ 3)),
        4 * cf.r * cf.k * (cf.u ^ 2 - cf.r ^ 2) *
        ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 2 * (cf.u ^ 2 + cf.r ^ 2)),
        0] =
      P2.mk'
      ![-(cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2)),
        -(4 * cf.r ^ 2) + -((cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r)), 0] by
      simpa [f, rPoint, rPoint', hur2, hur, h3]
    have h10 : (cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2 ≠ 0 := by
      by_contra h
      have : 4 * (cf.u + cf.r) * cf.r = 0 := by linear_combination hur2 - h
      simp [hur, cf.hr] at this
    have h1 : 4 * cf.r * cf.k * (cf.u ^ 2 - cf.r ^ 2) *
        ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 2 * (cf.u ^ 2 + cf.r ^ 2)) =
        ((cf.u + cf.r) *
        ((cf.u - cf.r) ^ 4 * (cf.u + cf.r) ^ 4
        - 8 * cf.r ^ 2 * (cf.u - cf.r) ^ 2 * (cf.u + cf.r) ^ 2 +
        8 * cf.r * (cf.r ^ 3 - cf.r ^ 2 * cf.u + cf.r * cf.u ^ 2 + cf.u ^ 3)) /
        -(cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2))) *
        (-(4 * cf.r ^ 2) + -((cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r))) := by
      field_simp
      rw [cf.k_sq]
      linear_combination - (cf.u + cf.r) * congr($hur2 ^ 3)
    have h0 : (cf.u + cf.r) *
        ((cf.u - cf.r) ^ 4 * (cf.u + cf.r) ^ 4
        - 8 * cf.r ^ 2 * (cf.u - cf.r) ^ 2 * (cf.u + cf.r) ^ 2 +
        8 * cf.r * (cf.r ^ 3 - cf.r ^ 2 * cf.u + cf.r * cf.u ^ 2 + cf.u ^ 3)) /
        -(cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2)) ≠ 0 := by
      by_contra! h0
      have : cf.u ^ 2 - cf.r ^ 2 = 0 ∨
          (cf.u ^ 2 - cf.r ^ 2) ^ 2 - 2 * (cf.u ^ 2 + cf.r ^ 2) = 0 := by
        simpa [h0, hk, cf.hr] using h1
      obtain h | h := this
      · simp [h, cf.hu, cf.hr] at hur2
      · have : 2 * (cf.u + cf.r) ^ 2 = 0 := by linear_combination hur2 - h
        have : cf.u + cf.r = 0 := by simpa using this
        simp [this] at hur
    apply P2.mk'_eq_mk' h0
    simp_rw [Matrix.smul_vec3, smul_eq_mul, mul_zero]
    congrm ![?_, $h1, 0]
    rw [div_mul_cancel₀ _ (by simp [hk, h10])]
  simp only [f, fxyz_2w, fabc_2w, neg_mul, rPoint, ne_eq, rPoint', Fin.isValue, neg_sub, fxyz_neg_w,
    fabc_neg_w, P2.lift₂_mk, Matrix.cons_val, mul_eq_zero, hur, hur2, or_self, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one, even_two, Even.neg_pow, mul_neg, sub_neg_eq_add,
    Matrix.cons_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    Matrix.zero_empty, and_true, and_false, P2.mk'_eq, Prod.mk.injEq]
  symm
  rw [← P2.mk'_eq]
  have : (cf.u + cf.r) ^ 4 ≠ 0 := by simpa using hur
  apply P2.mk'_eq_mk' this
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, $(by ring), $(by ring)]
  suffices 2 * ((cf.u - cf.r) * (cf.u + cf.r) ^ 2 * (cf.u + 3 * cf.r) + 4 * cf.r ^ 2) *
    (cf.u + cf.r) ^ 2 *
    ((cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r)) +
    2 * cf.u * (cf.k ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.r ^ 2) ^ 2) * (cf.u + cf.r) ^ 2 -
    ((cf.u - cf.r) * (cf.u + cf.r) ^ 2 + 2 * cf.r) *
    ((cf.u + cf.r) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u * cf.r)) ^ 2 =
    (cf.u + cf.r) ^ 4 *
    ((cf.u + cf.r) *
    ((cf.u - cf.r) ^ 4 * (cf.u + cf.r) ^ 4 - 8 * cf.r ^ 2 * (cf.u - cf.r) ^ 2 * (cf.u + cf.r) ^ 2 +
    8 * cf.r * (cf.r ^ 3 - cf.r ^ 2 * cf.u + cf.r * cf.u ^ 2 + cf.u ^ 3))) by
    linear_combination this
  rw [cf.k_sq]
  ring

theorem f_w_sub_not_singularAbc {x y : cf.K} (hxy : (elliptic cf).Nonsingular x y)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf)
    (hsxy : ¬ SingularAbc cf x y) :
    f cf (w cf - (.some hxy)) = rPoint cf (f cf (.some hxy)) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  by_cases hp2 : fabcNormal cf x y 2 = 0
  · by_cases huxr : cf.r * x + cf.u = 0
    · suffices fxyz cf (w cf - Point.some hxy) =
          P2.lift₂ (fun p q hp hq ↦ P2.mk' (rPoint' cf p q)) _
          (fxyz cf (Point.some hxy)) (fabc cf (Point.some hxy)) by
        simpa [f, rPoint, fabc_w_sub]
      have hxeq : x = -cf.u / cf.r := by
        field_simp
        linear_combination huxr
      rw [nonsingular_elliptic cf] at hxy
      obtain ⟨heq, hnonsingular⟩ := hxy
      rw [hxeq] at heq
      have hy : cf.r ^ 4 * y ^ 2 + cf.u ^ 2 * (cf.u + cf.r) ^ 2 - cf.u ^ 2 = 0 := by
        field_simp at heq
        linear_combination heq
      have hk : cf.k ≠ 0 := by
        contrapose! hsxy with hk
        have hur : (cf.u + cf.r) ^ 2 = 1 := by
          rw [← sq_eq_zero_iff, cf.k_sq, sub_eq_zero] at hk
          exact hk
        apply SingularAbc.mk cf hxy
        · simp [hur, huxr]
        · simp [huxr]
      have hur1 : (cf.u + cf.r) ^ 2 - 1 ≠ 0 := by
        rw [← sq_eq_zero_iff.ne, cf.k_sq] at hk
        exact hk
      have hur0 : cf.u + cf.r ≠ 0 := by
        contrapose! hx with hur0
        have : cf.u = -cf.r := eq_neg_of_add_eq_zero_left hur0
        rw [hxeq, this]
        field
      have hur0' : -cf.r - cf.u ≠ 0 := by
        contrapose! hur0
        linear_combination - hur0
      rw [w_sub cf hxy hx]
      simp only [fxyz, fxyzRaw, neg_mul, ne_eq, rPoint', Fin.isValue, neg_sub, huxr,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, fabc, fabcRaw, hsxy, ↓reduceIte,
        P2.lift₂_mk, hp2, Matrix.cons_val]
      simp only [hxeq, fabcNormal, neg_mul, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        mul_neg]
      apply P2.mk_eq_mk'_of_l _ ((4 * (cf.u * ((cf.u + cf.r) ^ 2 - 1) + cf.r^2 * y)^2)
        / (8 * cf.k * cf.u^3 * (cf.u + cf.r)^4 * ((cf.u + cf.r) ^ 2 - 1)))
      simp_rw [Matrix.smul_vec3, smul_eq_mul]
      congrm ![?_, ?_, ?_]
      · field_simp
        linear_combination 16 * cf.u * ((cf.u + cf.r) ^ 2 - 1) * (cf.u + cf.r) ^ 6 * hy
      · field_simp
        rw [cf.k_sq]
        linear_combination -16 * (cf.u - cf.r) *
          ((cf.u + cf.r) ^ 2 - 1) * (cf.u + cf.r) ^ 4 *
          (2*cf.u^3 + 4*cf.u^2*cf.r + y*cf.r^2 + 2*cf.u*cf.r^2 - 2*cf.u) * hy
      · field
    exact f_w_sub_not_singularAbc_p2 cf hxy hpw hpnw hsxy hp2 huxr (fabc_w_sub cf _)
  exact f_w_sub_normal cf hxy hpw hpnw hsxy hp2 (fabc_w_sub cf _)

theorem f_w_sub (p : (elliptic cf).Point) : f cf (w cf - p) = rPoint cf (f cf p) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  cases p with
  | zero =>
    rw [show Point.zero = 0 from rfl]
    simpa using f_w_eq_rPoint cf
  | @some x y hxy =>
  by_cases hpw : .some hxy = w cf
  · rw [← (rPoint_bijOn cf).injOn.eq_iff (mapsTo_f cf (by simp))
      (mapsTo_rPoint cf (mapsTo_f cf (by simp))), rPoint_rPoint cf (mapsTo_f cf (by simp))]
    rw [hpw]
    simpa using (f_w_eq_rPoint cf).symm
  by_cases hpnw : .some hxy = -w cf
  · simpa [hpnw] using f_two_w_eq_rPoint cf
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  by_cases hsxy : SingularAbc cf x y
  · by_cases hur : cf.u ^ 2 - cf.r ^ 2 = 0
    · suffices fxyz cf (w cf - Point.some hxy) =
        P2.lift₂ (fun p q hp hq ↦ P2.mk' (rPoint' cf p q)) _
        (fxyz cf (Point.some hxy)) (fabc cf (Point.some hxy)) by
        simpa [f, rPoint, fabc_w_sub]
      rw [w_sub cf hxy hx]
      have hp2 : fxyzRaw cf (Point.some hxy) 2 ≠ 0 := by
        simpa [fxyzRaw] using hsxy.rx_add_u_ne_zero cf hxy
      suffices P2.mk (fxyzRaw cf (Point.some _)) _ =
          P2.mk' ![-((cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2))
            * (4 * cf.u ^ 2)),
          -(2 * cf.u * cf.k * (4 * cf.u ^ 2)), 0] by
        simpa [fabc, fabcRaw, hsxy, rPoint', fxyz, hur, hp2]
      have : (cf.u + cf.r) * (cf.u - cf.r) = 0 := by linear_combination hur
      obtain hur | hur : cf.u + cf.r = 0 ∨ cf.u - cf.r = 0 := by simpa using this
      · obtain hx := hsxy.x_eq_zero_of_casePos cf hxy hur
        obtain hy := hsxy.y_eq_zero_of_casePos cf hxy hur
        have hr : cf.r = -cf.u := by linear_combination hur
        symm
        have : 4 * cf.u ^ 2 ≠ 0 := by simpa using cf.hu
        rw [← P2.mk'_eq]
        apply P2.mk'_eq_mk' this
        simp only [fxyzRaw]
        simp_rw [Matrix.smul_vec3, smul_eq_mul, hx, hy, hr]
        congrm ![$(by field), $(by field), $(by field)]
      · have hu : cf.u = cf.r := (sub_eq_zero.mp hur)
        have hy : y = 0 := hsxy.y_eq_zero_of_caseNeg cf hxy hu
        obtain hx := hsxy.c_factor_eq_zero cf hxy
        rw [hu] at hx
        have hx : cf.r ^ 2 * (x - 1) ^ 2 + x = 0 := by
          suffices 4 * cf.r ^ 2 * (cf.r ^ 2 * (x - 1) ^ 2 + x) = 0 by
            simpa [cf.hr]
          linear_combination hx
        simp only [ne_eq, fxyzRaw, hu, hy, mul_zero, add_zero, neg_mul, add_sub_cancel_right,
          sub_add_cancel]
        rw [← P2.mk'_eq]
        have hx1 : x ≠ 1 := by
          by_contra!
          simp [this] at hx
        have hx1' : x - 1 ≠ 0 := sub_eq_zero.ne.mpr hx1
        have hxn1 : x ≠ -1 := by
          obtain h := hsxy.rx_add_u_ne_zero cf hxy
          contrapose! h
          simp [h, hu]
        have hxn1' : x + 1 ≠ 0 := by simpa using sub_eq_zero.ne.mpr hxn1
        have h0 : cf.r ^ 2 * (x - 1) ^ 2 + 2 * x ≠ 0 := by
          by_contra! h
          have : x = 0 := by
            linear_combination  h - hx
          simp [this, cf.hr] at h
        have : ((x + 1) * (cf.r ^ 2 * (x - 1) ^ 2 + 2 * x))
            / (4 * cf.r^4 * (x-1)^3) ≠ 0 := by
          simp [h0, hxn1', hx1', cf.hr]
        apply P2.mk'_eq_mk' this
        simp_rw [Matrix.smul_vec3, smul_eq_mul]
        congrm ![?_, ?_, ?_]
        · field_simp
          linear_combination 4 * (x^3*cf.r^2 - x^2*cf.r^2 - x*cf.r^2 + 2*x^2 + cf.r^2) * hx
        · field
        · field_simp
          linear_combination 16 * cf.r ^ 2 * congr($hx ^ 2)
    exact f_w_sub_singularAbc cf hxy hsxy hpw hpnw hur (fabc_w_sub cf _)
  exact f_w_sub_not_singularAbc cf hxy hpw hpnw hsxy
