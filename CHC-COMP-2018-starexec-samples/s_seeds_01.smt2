(set-logic HORN)
(set-info :status sat)
(declare-fun itp (Int Int ) Bool)

(assert (forall ((m Int) (i Int)) (=> (and (= m 0) (= i 0)) (itp m i))))
(assert (forall ((i Int) (m Int) (m1 Int) (i1 Int))
  (=> (and (itp m i) (= i1 (+ i 55)) (= m1 (+ m 66))) (itp m1 i1))))
(assert (forall ((m Int) (i Int))
  (let ((a!1 (and (itp m i) (not (>= (+ m i) 0)))))
    (=> a!1 false))))
(check-sat)

