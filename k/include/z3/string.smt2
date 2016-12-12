; floats as uninterpreted with a partial order relation
(declare-sort Float)
(declare-fun float_nan () Float)
(declare-fun float_zero () Float)

(declare-fun float_lt (Float Float) Bool)
; transitivity
(assert (forall ((x1 Float) (x2 Float) (x3 Float)) (implies (and (float_lt x1 x2) (float_lt x2 x3)) (float_lt x1 x3))))
; irreflexivity
(assert (forall ((x1 Float) (x2 Float)) (not (and (float_lt x1 x2) (float_lt x2 x1)))))
; total order without nan
(assert (forall ((x1 Float) (x2 Float)) (implies (and (not (= x1 float_nan)) (not (= x2 float_nan))) (or (float_lt x1 x2) (= x1 x2) (float_lt x2 x1)))))
; nan
(assert (forall ((x Float)) (and (not (float_lt x float_nan)) (not (float_lt float_nan x)))))

(define-fun float_le ((x1 Float) (x2 Float)) Bool (or (float_lt x1 x2) (= x1 x2)))
(define-fun float_gt ((x1 Float) (x2 Float)) Bool (float_lt x2 x1))
(define-fun float_ge ((x1 Float) (x2 Float)) Bool (float_le x2 x1))

(define-fun float_max ((x Float) (y Float)) Float (ite (float_lt x y) y x))
(define-fun float_min ((x Float) (y Float)) Float (ite (float_lt x y) x y))

; float sets as arrays
(define-sort FloatSet () (Array Float Bool))
(define-fun float_set_mem ((x Float) (s FloatSet)) Bool (select s x))
(define-fun float_set_add ((s FloatSet) (x Float)) FloatSet  (store s x true))
(define-fun float_set_emp () FloatSet ((as const FloatSet) false))
(define-fun float_set_cup ((s1 FloatSet) (s2 FloatSet)) FloatSet ((_ map or) s1 s2))
(define-fun float_set_cap ((s1 FloatSet) (s2 FloatSet)) FloatSet ((_ map and) s1 s2))
(define-fun float_set_com ((s FloatSet)) FloatSet ((_ map not) s))
(define-fun float_set_ele ((x Float)) FloatSet (float_set_add float_set_emp x))
(define-fun float_set_dif ((s1 FloatSet) (s2 FloatSet)) FloatSet (float_set_cap s1 (float_set_com s2)))
(define-fun float_set_sub ((s1 FloatSet) (s2 FloatSet)) Bool (= float_set_emp (float_set_dif s1 s2)))
(define-fun float_set_lt  ((s1 FloatSet) (s2 FloatSet)) Bool (forall ((i Float) (j Float)) (implies (and (select s1 i) (select s2 j)) (float_lt i j))))
(define-fun float_set_le  ((s1 FloatSet) (s2 FloatSet)) Bool (forall ((i Float) (j Float)) (implies (and (select s1 i) (select s2 j)) (float_le i j))))


; strings as uninterpreted with a total order relation
(declare-sort String)

(declare-fun string_lt (String String) Bool)
; transitivity
(assert (forall ((x1 String) (x2 String) (x3 String)) (implies (and (string_lt x1 x2) (string_lt x2 x3)) (string_lt x1 x3))))
; irreflexivity
(assert (forall ((x1 String) (x2 String)) (not (and (string_lt x1 x2) (string_lt x2 x1)))))
; total order
(assert (forall ((x1 String) (x2 String)) (or (string_lt x1 x2) (= x1 x2) (string_lt x2 x1))))

(define-fun string_le ((x1 String) (x2 String)) Bool (or (string_lt x1 x2) (= x1 x2)))
(define-fun string_gt ((x1 String) (x2 String)) Bool (string_lt x2 x1))
(define-fun string_ge ((x1 String) (x2 String)) Bool (string_le x2 x1))

; string sets as arrays
(define-sort StringSet () (Array String Bool))
(define-fun string_set_mem ((x String) (s StringSet)) Bool (select s x))
(define-fun string_set_add ((s StringSet) (x String)) StringSet  (store s x true))
(define-fun string_set_emp () StringSet ((as const StringSet) false))
(define-fun string_set_cup ((s1 StringSet) (s2 StringSet)) StringSet ((_ map or) s1 s2))
(define-fun string_set_cap ((s1 StringSet) (s2 StringSet)) StringSet ((_ map and) s1 s2))
(define-fun string_set_com ((s StringSet)) StringSet ((_ map not) s))
(define-fun string_set_ele ((x String)) StringSet (string_set_add string_set_emp x))
(define-fun string_set_dif ((s1 StringSet) (s2 StringSet)) StringSet (string_set_cap s1 (string_set_com s2)))
(define-fun string_set_sub ((s1 StringSet) (s2 StringSet)) Bool (= string_set_emp (string_set_dif s1 s2)))
(define-fun string_set_lt  ((s1 StringSet) (s2 StringSet)) Bool (forall ((i String) (j String)) (implies (and (select s1 i) (select s2 j)) (string_lt i j))))
(define-fun string_set_le  ((s1 StringSet) (s2 StringSet)) Bool (forall ((i String) (j String)) (implies (and (select s1 i) (select s2 j)) (string_le i j))))

; sequence axioms
(declare-sort IntSeq)
(declare-fun smt_seq_concat (IntSeq IntSeq) IntSeq)
(declare-fun smt_seq_elem (Int) IntSeq)
(declare-fun smt_seq_nil () IntSeq)

; int extra
(define-fun int_max ((x Int) (y Int)) Int (ite (< x y) y x))
(define-fun int_min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun int_abs ((x Int)) Int (ite (< x 0) (- 0 x) x))

; bool to int
(define-fun smt_bool2int ((b Bool)) Int (ite b 1 0))

