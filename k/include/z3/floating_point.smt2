(set-logic QF_FPA)

; TODO: remove sort/fun declarations that are not actually used
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
