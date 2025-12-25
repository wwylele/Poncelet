import Mathlib
import Poncelet.TransferAux

open WeierstrassCurve.Affine

variable (u r : ℂ)

variable {r} in
theorem fabcNormal_o_sub (hr : r ≠ 0) (x y : ℂ) (hx : x ≠ 0) :
    fabcNormal u r (u ^ 2 / (r ^ 2 * x)) (u ^ 2 * y / (r ^ 2 * x ^ 2)) = (u ^ 3 / (r ^ 3 * x ^ 3)) •
    ![2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
      (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2),
    -k u r * (2 * r ^ 2 * (r * x + u) * y -
      (r * x - u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)),
    (r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)] := by
  unfold fabcNormal
  simp only [Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty]
  congrm ![?_, ?_, ?_]
  · field
  · field
  · field


variable {u r} in
theorem fxyz_o_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    fxyz u hr (o hu hr - p) = fxyz u hr p := by
  have hp0 : fxyz u hr (o hu hr) = fxyz u hr 0 := by
    suffices P2.mk ![u ^ 2 * (u + r), 0, u ^ 2] _ = P2.mk ![u + r, 0, 1] _ by
      simpa [o, fxyz, fxyzRaw]
    rw [P2.mk_eq_mk]
    use u ^ 2
    simpa using hu
  cases p with
  | zero =>
    change fxyz u hr (o hu hr - 0) = fxyz u hr 0
    simp
  | @some x y hxy =>
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hs⟩ := hxy
    by_cases hx0 : x = 0
    · rw [(eq_o_iff hu hr hxy).mpr hx0]
      simp
    have hxo : Point.some hxy ≠ o hu hr := (eq_o_iff hu hr hxy).ne.mpr hx0
    unfold fxyz
    rw [P2.mk_eq_mk]
    use u ^ 2 / (r ^ 2 * x ^ 2)
    refine ⟨by simp [hr, hu, hx0], ?_⟩
    rw [o_sub hu hr hxy hxo]
    simp only [fxyzRaw, smul_eq_mul, Matrix.smul_cons, Matrix.smul_empty,
      Matrix.vecCons_inj, and_true]
    refine ⟨?_, ?_, ?_⟩
    · field
    · field
    · field

variable {u} in
theorem f_o_sub_1 (hu : u ≠ 0) (i : ℂ) :
    P2.mk' ![1, i * k u r, u + r] =
    P2.mk' (rChord' u r ![u + r, 0, 1] ![1, -i * k u r, u + r]) := by
  by_cases hur : u + r = 0
  · have hur' : r ^ 2 - u ^ 2 = 0 := by grind
    simp [rChord', hur, hur']
  have hur' : 2 * u * (u + r) + r ^ 2 - u ^ 2 ≠ 0 := by grind
  symm
  apply P2.mk'_eq_mk' hur'
  suffices 2 * (u + r) * (u + r) - (2 * u * (u + r) + r ^ 2 - u ^ 2) =
      2 * u * (u + r) + r ^ 2 - u ^ 2 by
    simpa [rChord', hur']
  ring

variable {u r} in
theorem SingularAbc.fabc_o_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : (elliptic u r).Nonsingular x y)
    (ho : Point.some hxy ≠ o hu hr) :
    fabc hu hr (o hu hr - .some hxy) = P2.mk ![8 * u ^ 3 * k u r,
      4 * (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * u ^ 2, 0]
      (by simp [hu, h.k_ne_zero u hr hxy]) := by
  have hx0 : x ≠ 0 := (eq_o_iff hu hr hxy).ne.mp ho
  rw [o_sub hu hr _ ho]
  by_cases hs : SingularAbc u r (u ^ 2 / (r ^ 2 * x)) (u ^ 2 * y / (r ^ 2 * x ^ 2))
  · obtain hy := h.y_eq
    obtain hy' := congr(r ^ 3 * x ^ 3 / u ^ 3 * $hs.y_eq)
    have hy' : -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y =
        (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 +
        2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2) := by
      convert hy' using 1
      · field
      · field
    have hy0 : 4 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y = 0 := by
      linear_combination hy - hy'
    obtain hx := h.c_factor_eq_zero u hr hxy
    have hrxu : r * x - u ≠ 0 := by grind
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hnonsingular⟩ := hxy
    have hy0 : y = 0 := by
      obtain hur1 | hy0 : (u + r) ^ 2 - 1 = 0 ∨ y = 0 := by simpa [hrxu, hr] using hy0
      · have hur1' : (u + r) ^ 2 = 1 := sub_eq_zero.mp hur1
        rw [hur1'] at hx
        have hrxu : (r * x + u) ^ 2 = 0 := by linear_combination hx
        have hrxu : -(r * x) = u := by simpa [neg_eq_iff_add_eq_zero] using hrxu
        have hrxu : x = -u / r := by simp [← hrxu, hr]
        have hrxu' : x * (r ^ 2 * x ^ 2 + (1 - u ^ 2 - r ^ 2) * x + u ^ 2) = 0 := by
          suffices r ^ 2 * (-u / r) ^ 2 + (1 - u ^ 2 - r ^ 2) * (-u / r) + u ^ 2 = 0
            by simpa [hrxu, hr, hu]
          field_simp
          convert congr(u * $hur1) using 1
          · ring
          · ring
        simpa [hrxu', hr] using heq
      exact hy0
    have hx : r ^ 2 * x ^ 2 + (1 - u ^ 2 - r ^ 2) * x + u ^ 2 = 0 := by
      simpa [hy0, hx0] using heq
    obtain hrxu | hrxu : r * x + u = 0 ∨
        r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2 = 0 := by
      simpa [hy0] using hy
    · grind
    have hurx : (u - r) * ((u + r) ^ 2 - 1) * x = 0 := by
      linear_combination hrxu - hx * (u + r)
    obtain hur | hur : u - r = 0 ∨ (u + r) ^ 2 - 1 = 0 := by simpa [hx0] using hurx
    · have hu : u = r := sub_eq_zero.mp hur
      have hs : SingularAbc r r (r ^ 2 / (r ^ 2 * x)) (r ^ 2 * y / (r ^ 2 * x ^ 2)) := by
        simpa [hu] using hs
      suffices P2.mk ![2 * r * k r r * (4 * r ^ 2),
        -((r * (r + r) ^ 2 * (r ^ 2 / (r ^ 2 * x)) - r * ((r + r) ^ 2 - 2)) * (4 * r ^ 2)), 0] _ =
        P2.mk ![8 * r ^ 3 * k r r,
        4 * (r * (r + r) ^ 2 * x - r * ((r + r) ^ 2 - 2)) * r ^ 2, 0] _ by
        simpa [fabc, fabcRaw, hs, hu]
      congrm P2.mk ![$(by ring), ?_, 0] _
      apply eq_of_sub_eq_zero
      rw [← mul_left_inj' hx0]
      convert congr(-16 * r ^ 3 * $hx) using 1
      · simp_rw [hu]
        field
      · simp
    have hur : (u + r) ^ 2 = 1 := sub_eq_zero.mp hur
    have hk : k u r = 0 := by simpa [hur] using k_sq u r
    suffices P2.mk ![0,
        (r * (u ^ 2 / (r ^ 2 * x)) - u * (1 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2), 0] _ =
        P2.mk ![0, 4 * (r * x - u * (1 - 2)) * u ^ 2, 0] _ by
      simpa [fabc, fabcRaw, hs, hk, hur]
    rw [P2.mk_eq_mk']
    grind
  simp only [fabc, fabcRaw, hs, ↓reduceIte]
  simp_rw [← P2.mk'_eq]
  rw [fabcNormal_o_sub u hr x y hx0]
  rw [P2.mk'_smul (by simp [hu, hr, hx0])]
  rw [h.c_factor_eq_zero u hr hxy, mul_zero]
  rw [← h.y_eq, ← two_mul]
  rw [mul_sub (-k u r)]
  simp_rw [neg_mul]
  rw [← h.y_eq', ← neg_add', ← two_mul]
  have : y ≠ 0 ∧ (u + r) ^ 2 - 1 ≠ 0 ∧ r * x - u ≠ 0 := by
    contrapose! hs
    apply SingularAbc.mk u hr (nonsingular_o_sub hu hr hxy)
    · have : -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y = 0 := by
        simp only [mul_eq_zero]
        grind
      obtain ha := h.a_eq_zero u r
      rw [this] at ha
      field_simp
      convert congr(u ^ 3 * $ha) using 1
      · congrm (_ * ?_)
        grind
      · simp
    · field_simp
      grind [h.c_factor_eq_zero u hr hxy]
  obtain ⟨hy, hur, huxr⟩ := this
  have hk : k u r ≠ 0 := by
    rw [← sq_eq_zero_iff.ne]
    simpa [k_sq] using hur
  have : r ^ 2 * k u r * (r * x - u) * y / (2 * u ^ 3) ≠ 0 := by
    simp [hr, hk, hy, hu, huxr]
  apply P2.mk'_eq_mk' this
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_zero,
    Matrix.smul_empty, Matrix.vecCons_inj, and_true]
  constructor
  · field_simp
    rw [k_sq]
    ring
  · field_simp
    apply eq_of_sub_eq_zero
    linear_combination -4 * (h.c_factor_eq_zero u hr hxy)

variable {u r} in
theorem SingularAbc.f_o_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (hsxy : SingularAbc u r x y) (hxy : (elliptic u r).Nonsingular x y)
    (ho : Point.some hxy ≠ o hu hr) :
    f hu hr (o hu hr - .some hxy) = rChord u r (f hu hr (.some hxy)) := by
  suffices fabc hu hr (o hu hr - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' u r p q)) _
      (fxyz u hr (.some hxy)) (fabc hu hr (.some hxy)) by
    simpa [rChord, f, fxyz_o_sub hu hr]
  rw [hsxy.fabc_o_sub hu hr hxy ho, hsxy.fxyz_eq hu hr, hsxy.fabc_eq hu hr]
  obtain hk := hsxy.k_ne_zero u hr hxy
  have h0 : 2 * u * (2 * u * k u r * (u ^ 2 - r ^ 2)) + r ^ 2 * (4 * u ^ 2 * k u r) -
      u ^ 2 * (4 * u ^ 2 * k u r) = 0 := by
    ring
  by_cases hur2 : u ^ 2 - r ^ 2 = 0
  · have h0' : r ^ 2 * (4 * u ^ 2 * k u r) - u ^ 2 * (4 * u ^ 2 * k u r) = 0 := by
      simpa [hur2] using h0
    suffices P2.mk ![8 * u ^ 3 * k u r,
        4 * (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * u ^ 2, 0] _ =
      P2.mk ![2 * u * k u r * (4 * u ^ 2),
        (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (4 * u ^ 2), 0] _ by
      simpa [rChord', h0', hk, hu, hur2]
    congrm P2.mk ![?_, ?_, _] _
    · ring
    · ring
  suffices P2.mk ![8 * u ^ 3 * k u r,
      4 * (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * u ^ 2, 0] _ =
    P2.mk ![(r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (u ^ 2 - r ^ 2),
      -(2 * u * k u r * (u ^ 2 - r ^ 2)), 0] _ by
    simpa [rChord', h0, hur2, hu, hk]
  rw [P2.mk_eq_mk']
  use 8 * u ^ 3 * k u r / ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (u ^ 2 - r ^ 2))
  simp only [Matrix.smul_cons, smul_eq_mul, mul_neg, mul_zero, Matrix.smul_empty,
    Matrix.vecCons_inj, and_true]
  have h0 : r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2) ≠ 0 := by
    rw [← sq_eq_zero_iff.ne, ← hsxy.x_relation u hr hxy]
    simp [hu, hk]
  constructor
  · field
  · field_simp
    rw [← hsxy.x_relation u hr hxy]
    ring

variable {u r} in
theorem f_o_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    f hu hr (o hu hr - p) = rChord u r (f hu hr p) := by
  -- check case when p = 0
  cases p with
  | zero =>
    rw [show o hu hr - Point.zero = o hu hr by rfl]
    suffices P2.mk ![1, k u r, u + r] _ =
      P2.mk' (rChord' u r ![u + r, 0, 1] ![1, -k u r, u + r]) by simpa [rChord, f, fxyz_o_sub hu hr]
    rw [← P2.mk'_eq]
    simpa using f_o_sub_1 r hu 1
  | @some x y hxy =>
  -- check case when p = o
  by_cases ho : .some hxy = o hu hr
  · suffices P2.mk ![1, -k u r, u + r] _ =
        P2.mk' (rChord' u r ![u + r, 0, 1] ![1, k u r, u + r]) by
      simpa [rChord, f, fxyz_o_sub hu hr, ho]
    rw [← P2.mk'_eq]
    simpa using f_o_sub_1 r hu (-1)
  have hx0 : x ≠ 0 := (eq_o_iff hu hr hxy).ne.mp ho
  -- check case when p is SingularAbc
  by_cases hsxy : SingularAbc u r x y
  · exact hsxy.f_o_sub hu hr hxy ho
  -- check case when o - p is SingularAbc
  have : ∃ (ox oy : ℂ) (hoxy : (elliptic u r).Nonsingular ox oy),
      o hu hr - .some hxy = .some hoxy := by
    cases h : o hu hr - .some hxy with
    | zero =>
      rw [Eq.comm, ← sub_eq_zero.not, h] at ho
      absurd ho
      rfl
    | @some ox oy hoxy =>
      exact ⟨ox, oy, hoxy, rfl⟩
  obtain ⟨ox, oy, hoxy, hoxyeq⟩ := this
  have hoo : .some hoxy ≠ o hu hr := by
    by_contra!
    simp [this] at hoxyeq
  by_cases hosxy : SingularAbc u r ox oy
  · rw [hoxyeq]
    have hoxyeq' : Point.some hxy = o hu hr - Point.some hoxy := by
      simp [← hoxyeq]
    rw [hoxyeq']
    rw [← (rChord_bijOn u r hu).injOn.eq_iff (mapsTo_f hu hr (by simp))
      (mapsTo_rChord u r hu (mapsTo_f hu hr (by simp)))]
    rw [rChord_rChord u r hu (mapsTo_f hu hr (by simp))]
    exact (hosxy.f_o_sub hu hr hoxy hoo).symm
  -- non-singular case
  suffices fabc hu hr (o hu hr - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' u r p q)) _
      (fxyz u hr (Point.some hxy)) (fabc hu hr (Point.some hxy)) by
    simpa [rChord, f, fxyz_o_sub hu hr]
  rw [hoxyeq]
  suffices P2.mk (fabcNormal u r ox oy) _ =
      P2.mk' (rChord' u r (fxyzRaw u r (Point.some hxy)) (fabcNormal u r x y)) by
    simpa [fabc, fxyz, fabcRaw, hsxy, hosxy]
  rw [o_sub hu hr hxy ho, Point.some.injEq] at hoxyeq
  have hdeno : (r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x ≠ 0 := by
    by_contra! h
    obtain ha | ha := eq_or_eq_neg_of_sq_eq_sq _ _ <| presingular u hr hxy h
    · contrapose! hsxy
      refine SingularAbc.mk u hr hxy ?_ (by simp [h])
      linear_combination -ha
    · contrapose! hosxy
      rw [← hoxyeq.1, ← hoxyeq.2]
      refine SingularAbc.mk u hr (nonsingular_o_sub hu hr hxy) ?_ ?_
      · field_simp
        linear_combination u ^3 * ha
      · field_simp
        linear_combination u ^ 3 * (u + r * x) * h
  have hne : 2 * u * fxyzRaw u r (Point.some hxy) 0 + r ^ 2 * fxyzRaw u r (Point.some hxy) 2 -
      u ^ 2 * fxyzRaw u r (Point.some hxy) 2 ≠ 0 := by
    suffices 2 * u * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r ^ 2 - r * u) * x + u ^ 2 * (u + r))
        + r ^ 2 * (r * x + u) ^ 2 - u ^ 2 * (r * x + u) ^ 2 ≠ 0 by
      simpa [fxyzRaw]
    contrapose! hdeno
    linear_combination hdeno
  rw [← P2.mk'_eq]
  rw [← hoxyeq.1, ← hoxyeq.2]
  have hl : (r ^ 3 * x ^ 3 * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)) / u ^ 3 ≠ 0 := by
    simp [hu, hr, hx0, hdeno]
  symm
  apply P2.mk'_eq_mk' hl
  simp only [rChord', Fin.isValue, hne, ↓reduceIte]
  simp only [fxyzRaw, neg_mul, Fin.isValue, Matrix.cons_val_zero, fabcNormal, Matrix.cons_val,
    Matrix.cons_val_one, mul_neg, sub_neg_eq_add, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty,
    Matrix.vecCons_inj, and_true]
  exact ⟨by field, by field, by field⟩

variable {u r} in
theorem fabcNormal_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabcNormal u r (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3) = ![
    u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3,
    -k u r * u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3,
    (u + r) * u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3] := by
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]

variable {u r} in
@[simp]
theorem fabc_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr (w hu hr) = P2.mk ![1, -k u r, u + r] (by simp) := by
  unfold fabc
  rw [P2.mk_eq_mk']
  by_cases hs : SingularAbc u r (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3)
  · obtain h := hs.c_factor_eq_zero u hr (nonsingular_w hu hr)
    have h : (u ^ 2 - r ^ 2) ^ 2 = -4 * u * r := by
      field_simp at h
      grind
    suffices (r * (u + r) ^ 2 * (u ^ 2 / r ^ 2) - u * ((u + r) ^ 2 - 2)) *
        (-(4 * u * r) - 4 * u ^ 2) = -(2 * u * k u r * (-(4 * u * r) + 4 * u ^ 2) * k u r) ∧
        8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2) =
        2 * u * k u r * (-(4 * u * r) + 4 * u ^ 2) * (u + r) by
      simpa [fabcRaw, w, hs, h]
    constructor
    · have : -(2 * u * k u r * (-(4 * u * r) + 4 * u ^ 2) * k u r) =
        -(2 * u * (-(4 * u * r) + 4 * u ^ 2) * (k u r ^ 2)) := by ring
      rw [this, k_sq]
      field_simp
      linear_combination -h
    · ring
  simp [fabcRaw, w, hs, fabcNormal_w hu hr]
  grind

variable {u r} in
theorem fabcNormal_neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabcNormal u r (u ^ 2 / r ^ 2) (-u ^ 2 / r ^ 3) = ![
    u ^ 3 * ((u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2) / r ^ 3,
    -k u r * u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2) / r ^ 3,
    u ^ 3 * (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3] := by
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]


variable {u r} in
theorem not_singularAbc_neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    ¬ SingularAbc u r (u ^ 2 / r ^ 2) (-u ^ 2 / r ^ 3) := by
  by_contra! h
  obtain ha := h.a_eq_zero
  obtain hc := h.c_factor_eq_zero u hr (nonsingular_neg_w hu hr)
  field_simp at ha hc
  grind

variable {u r} in
theorem fabc_neg_w_ne_zero (hu : u ≠ 0) (hr : r ≠ 0) :
    ![(u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
      -k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2),
      (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] ≠ 0 := by
  obtain h := not_singularAbc_neg_w hu hr
  contrapose! h
  unfold SingularAbc fabcNormal
  obtain h := congr((u ^ 3 / r ^ 3) • $h)
  simp_rw [Matrix.smul_vec3, smul_zero, smul_eq_mul] at h
  refine Eq.trans ?_ h
  congrm ![$(by field), $(by field), $(by field)]

variable {u r} in
theorem fabc_neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr (-w hu hr) = P2.mk ![
      (u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
      -k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2),
      (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] (fabc_neg_w_ne_zero hu hr) := by
  rw [neg_w]
  simp only [fabc, fabcRaw, not_singularAbc_neg_w hu hr, ↓reduceIte, fabcNormal_neg_w hu hr]
  rw [P2.mk_eq_mk']
  use u ^ 3 / r ^ 3
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · ring
  · ring
  · ring

variable {r} in
theorem fabcNormal_2w (hr : r ≠ 0) :
    fabcNormal u r ((r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2))
    ((r ^ 2 - u ^ 2) * ((r ^ 2 - u ^ 2) ^ 2 - 2 * (r ^ 2 + u ^ 2)) / (8 * r ^ 3)) =
    ![(u + r) * ((u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2) *
      (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3),
    -k u r * (u + r) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2) *
      (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3),
    (u + r) ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) *
      (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3)] := by
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]

variable {u r} in
theorem fabc_2w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr (w hu hr + w hu hr) = P2.mk ![
      (u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
      -k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2),
      (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] (fabc_neg_w_ne_zero hu hr) := by
  rw [two_w]
  by_cases hsxy : SingularAbc u r ((r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2))
      ((r ^ 2 - u ^ 2) * ((r ^ 2 - u ^ 2) ^ 2 - 2 * (r ^ 2 + u ^ 2)) / (8 * r ^ 3))
  · obtain hc := hsxy.c_factor_eq_zero u hr (nonsingular_2w hu hr)
    field_simp at hc
    have hc : (u + r) ^ 2 *
        (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) = 0 := by
      linear_combination hc
    obtain hc | hc : u + r = 0 ∨
      ((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2 = 0 := by simpa using hc
    · have hr : r = -u := (neg_eq_of_add_eq_zero_right hc).symm
      simp only [fabc, fabcRaw, hsxy, ↓reduceIte]
      suffices P2.mk ![2 * u * k u (-u) * (4 * u ^ 2), -(u * 2 * (4 * u ^ 2)), 0] _ =
          P2.mk ![4 * u ^ 2, k u (-u) * (4 * u ^ 2), 0] _ by
        simpa [hr]
      symm
      rw [P2.mk_eq_mk']
      use -k u (-u) / (2 * u)
      simp_rw [Matrix.smul_vec3, smul_eq_mul, mul_zero]
      congrm ![?_ ,?_, 0]
      · field_simp
        simp [k_sq]
      · field_simp
    have hk : k u r ≠ 0 := by
      grind
    have hur : u - r ≠ 0 := by
      grind
    suffices P2.mk
      ![2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2),
        (r * (u + r) ^ 2 * ((r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2)) - u * ((u + r) ^ 2 - 2)) *
          ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2),
        8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)] _ =
      P2.mk
        ![(u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
          -(k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2)),
          (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] _ by
      simpa [fabc, fabcRaw, hsxy]
    symm
    rw [P2.mk_eq_mk']
    use ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / (8 * u ^ 2 * k u r * (u - r))
    simp_rw [Matrix.smul_vec3, smul_eq_mul]
    congrm ![?_, ?_, ?_]
    · field_simp
      grind
    · field_simp
      rw [k_sq]
      grind
    · field
  simp only [fabc, fabcRaw, hsxy, ↓reduceIte, fabcNormal_2w u hr]
  rw [P2.mk_eq_mk']
  use (u + r) * (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3)
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · ring
  · ring
  · ring

variable {u r} in
theorem fabc_w_sub_singularAbc (hu : u ≠ 0) (hr : r ≠ 0) {x y wx wy : ℂ}
    (hxy : (elliptic u r).Nonsingular x y) (hwxy : (elliptic u r).Nonsingular wx wy)
    (hpw : .some hxy ≠ w hu hr) (hpnw : .some hxy ≠ -w hu hr)
    (hwxyeq : w hu hr - .some hxy = .some hwxy)
    (hsxy : SingularAbc u r x y) :
    fabc hu hr (.some hwxy) = fabc hu hr (.some hxy) := by
  obtain hx := x_not_at_w hu hr hxy hpw hpnw
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this

  by_cases hwsxy : SingularAbc u r wx wy
  · rw [w_sub hu hr hxy hx, Point.some.injEq] at hwxyeq
    obtain ⟨hwx, hwy⟩ := hwxyeq
    suffices P2.mk ![2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2),
        (r * (u + r) ^ 2 * wx - u * ((u + r) ^ 2 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2),
        8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)] _ =
      P2.mk ![2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2),
        (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2),
        8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)] _ by
      simpa [fabc, fabcRaw, hsxy, hwsxy]
    rw [← hwx, ← hwy] at hwsxy
    obtain hc := hsxy.c_factor_eq_zero u hr hxy
    obtain hwc := hwsxy.c_factor_eq_zero u hr (nonsingular_w_sub hu hr hxy hx)
    field_simp at hwc
    congrm P2.mk ![_, ?_, _] _
    simp [hr]

    sorry
  have hk : k u r ≠ 0 := hsxy.k_ne_zero u hr hxy
  by_cases hur : u ^ 2 - r ^ 2 = 0
  ·
    sorry
  exact fabc_w_sub_singularAbc_not_singularAbc hu hr hxy hwxy hpw hpnw hwxyeq hsxy hwsxy hur


variable {u r} in
theorem fabc_w_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    fabc hu hr (w hu hr - p) = fabc hu hr p := by
  cases p with
  | zero =>
    change fabc hu hr (w hu hr - 0) = fabc hu hr Point.zero
    simp
  | @some x y hxy =>
  by_cases hpw : .some hxy = w hu hr
  · simp [hpw]
  by_cases hpnw : .some hxy = -w hu hr
  · simp_rw [hpnw, sub_neg_eq_add, fabc_2w, fabc_neg_w]
  have : ∃ (wx wy : ℂ) (hwxy : (elliptic u r).Nonsingular wx wy),
      w hu hr - .some hxy = .some hwxy := by
    cases h : w hu hr - .some hxy with
    | zero =>
      rw [Eq.comm, ← sub_eq_zero.not, h] at hpw
      absurd hpw
      rfl
    | @some wx wy hwxy =>
      exact ⟨wx, wy, hwxy, rfl⟩
  obtain ⟨wx, wy, hwxy, hwxyeq⟩ := this
  have hww : .some hwxy ≠ w hu hr := by
    by_contra!
    simp [this] at hwxyeq
  rw [hwxyeq]
  by_cases hsxy : SingularAbc u r x y
  · exact fabc_w_sub_singularAbc hu hr hxy hwxy hpw hpnw hwxyeq hsxy
  by_cases hwsxy : SingularAbc u r wx wy
  · have hwxyeq' : w hu hr - Point.some hwxy = Point.some hxy := by
      simp [← hwxyeq]
    by_cases hww2 : Point.some hwxy = -w hu hr
    · simp_rw [← hwxyeq', hww2, sub_neg_eq_add, fabc_2w, fabc_neg_w]
    exact (fabc_w_sub_singularAbc hu hr hwxy hxy (by simp [← hwxyeq]) hww2 hwxyeq' hwsxy).symm
  obtain hx := x_not_at_w hu hr hxy hpw hpnw
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  by_cases hinf : (r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x) = 0
  · exact fabc_w_sub_c_eq_zero hu hr hxy hwxy hpw hpnw hwxyeq hsxy hwsxy hinf
  · exact fabc_w_sub_c_ne_zero hu hr hxy hwxy hpw hpnw hwxyeq hsxy hwsxy hinf

variable {u r} in
theorem f_w_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    f hu hr (w hu hr - p) = rPoint u r (f hu hr p) := by sorry
