(set-option :auto-config false)
(set-option :smt.mbqi false)

; int extra
(declare-fun int_and (Int Int) Int)
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

; stack axioms
(declare-sort WordStack)
(declare-fun appWordStack (WordStack WordStack) WordStack)
(declare-fun word_stack_empty () WordStack)
(declare-fun sizeWordStack (WordStack) Int)
(declare-fun asByteStack (Int WordStack) WordStack)

(declare-fun uint (Int) WordStack)

(assert (= (sizeWordStack word_stack_empty) 0))
(assert (forall ((w1 WordStack) (w2 WordStack))
   (= (sizeWordStack (appWordStack w1 w2)) (+ (sizeWordStack w1) (sizeWordStack w2)))))

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
