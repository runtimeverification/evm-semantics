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

(declare-fun smt_set_lt ((IntSet) (IntSet)) Bool)
(declare-fun smt_set_le ((IntSet) (IntSet)) Bool)

; sequence axioms
(declare-sort IntSeq)

(declare-fun smt_seq_concat (IntSeq IntSeq) IntSeq)
(declare-fun smt_seq_elem (Int) IntSeq)
(declare-fun smt_seq_nil () IntSeq)
(declare-fun smt_seq_len (IntSeq) Int)

(declare-fun smt_seq_sum (IntSeq) Int)
(declare-fun smt_seq2set (IntSeq) IntSet)
(declare-fun smt_seq_sorted (IntSeq) Bool)

(declare-fun smt_seq_filter (Int IntSeq) IntSeq)
