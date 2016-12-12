(set-option :auto-config false)
(set-option :smt.mbqi false)

; int extra
(define-fun int_max ((x Int) (y Int)) Int (ite (< x y) y x))
(define-fun int_min ((x Int) (y Int)) Int (ite (< x y) x y))
(define-fun int_abs ((x Int)) Int (ite (< x 0) (- 0 x) x))

; bool to int
(define-fun smt_bool2int ((b Bool)) Int (ite b 1 0))

; set axioms
(declare-sort IntSet)

(declare-fun smt_set_cup (IntSet IntSet) IntSet)
(declare-fun smt_set_ele (Int) IntSet)
(declare-fun smt_set_emp () IntSet)
(declare-fun smt_set_mem (Int IntSet) Bool)

(assert (forall ((s1 IntSet) (s2 IntSet) (s3 IntSet)) (= (smt_set_cup (smt_set_cup s1 s2) s3) (smt_set_cup s1 (smt_set_cup s2 s3)))))
(assert (forall ((s1 IntSet) (s2 IntSet)) (= (smt_set_cup s1 s2) (smt_set_cup s2 s1))))
(assert (forall ((e Int)) (not (= (smt_set_ele e) smt_set_emp))))

(assert (forall ((s IntSet)) (= (smt_set_cup s s) s)))

(declare-fun smt_set_lt ((IntSet) (IntSet)) Bool)
(declare-fun smt_set_le ((IntSet) (IntSet)) Bool)

(assert (forall ((s1 IntSet) (s2 IntSet) (s3 IntSet)) (= (smt_set_lt (smt_set_cup s1 s2) s3) (and (smt_set_lt s1 s3) (smt_set_lt s2 s3)))))
(assert (forall ((s1 IntSet) (s2 IntSet) (s3 IntSet)) (= (smt_set_lt s1 (smt_set_cup s2 s3)) (and (smt_set_lt s1 s2) (smt_set_lt s1 s3)))))
(assert (forall ((e1 Int) (e2 Int)) (= (smt_set_lt (smt_set_ele e1) (smt_set_ele e2)) (< e1 e2))))
(assert (forall ((s IntSet)) (smt_set_lt s smt_set_emp)))
(assert (forall ((s IntSet)) (smt_set_lt smt_set_emp s)))

(assert (forall ((s1 IntSet) (s2 IntSet) (s3 IntSet)) (= (smt_set_le (smt_set_cup s1 s2) s3) (and (smt_set_le s1 s3) (smt_set_le s2 s3)))))
(assert (forall ((s1 IntSet) (s2 IntSet) (s3 IntSet)) (= (smt_set_le s1 (smt_set_cup s2 s3)) (and (smt_set_le s1 s2) (smt_set_le s1 s3)))))
(assert (forall ((e1 Int) (e2 Int)) (= (smt_set_le (smt_set_ele e1) (smt_set_ele e2)) (<= e1 e2))))
(assert (forall ((s IntSet)) (smt_set_le s smt_set_emp)))
(assert (forall ((s IntSet)) (smt_set_le smt_set_emp s)))

(assert (forall ((e Int) (s1 IntSet) (s2 IntSet)) (! (implies (and (smt_set_le s1 (smt_set_ele e)) (smt_set_le (smt_set_ele e) s2)) (smt_set_le s1 s2))
    :pattern ((smt_set_le s1 (smt_set_ele e)) (smt_set_le (smt_set_ele e) s2))
    :pattern ((smt_set_ele e) (smt_set_le s1 s2))
)))
(assert (forall ((e Int) (s1 IntSet) (s2 IntSet)) (implies (and (smt_set_lt s1 (smt_set_ele e)) (smt_set_le (smt_set_ele e) s2)) (smt_set_lt s1 s2))))
(assert (forall ((e Int) (s1 IntSet) (s2 IntSet)) (implies (and (smt_set_le s1 (smt_set_ele e)) (smt_set_lt (smt_set_ele e) s2)) (smt_set_lt s1 s2))))
(assert (forall ((s1 IntSet) (s2 IntSet)) (implies (smt_set_lt s1 s2) (smt_set_le s1 s2))))

; sequence axioms
(declare-sort IntSeq)

(declare-fun smt_seq_concat (IntSeq IntSeq) IntSeq)
(declare-fun smt_seq_elem (Int) IntSeq)
(declare-fun smt_seq_nil () IntSeq)
(declare-fun smt_seq_len (IntSeq) Int)

(declare-fun smt_seq_sum (IntSeq) Int)
(declare-fun smt_seq2set (IntSeq) IntSet)
(declare-fun smt_seq_sorted (IntSeq) Bool)

(assert (forall ((s1 IntSeq) (s2 IntSeq)) (! (= (smt_seq_sorted (smt_seq_concat s1 s2)) (and (smt_set_le (smt_seq2set s1) (smt_seq2set s2)) (smt_seq_sorted s1) (smt_seq_sorted s2)))
	:pattern ((smt_seq_sorted (smt_seq_concat s1 s2)))
	:pattern ((smt_seq_sorted s1) (smt_seq_sorted s2))
)))

(assert (forall ((e Int)) (= (smt_seq_sorted (smt_seq_elem e)) true)))
(assert (= (smt_seq_sorted smt_seq_nil) true))

(assert (forall ((s IntSeq)) (>= (smt_seq_len s) 0)))

(assert (forall ((e Int) (s IntSet)) (not (= (smt_set_cup (smt_set_ele e) s) smt_set_emp))))
