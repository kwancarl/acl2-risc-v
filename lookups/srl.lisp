(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)


;; The following two encapsulates prove the table decomposition of SLL
;; lemmas about ash
(encapsulate
 nil
 ;; show (ash (+ x y) n) = (+ (ash x n) (ash y n))
 (local (include-book "arithmetic-5/top" :dir :system))
 (local (defthm mod-x-1
  (implies (integerp x) (equal (mod x 1) 0))))
 (defthm +-of-left-ash
  (implies (and (integerp x) (integerp y) (natp n))
	   (equal (ash (+ x y) n) (+ (ash x n) (ash y n))))
  :hints (("Goal" :in-theory (enable ash)))))
;; end encapsulate

(encapsulate
 nil
 (define sum-list ((lst nat-listp))
  :returns (sum integerp)
  (if (or (atom lst) (not (nat-listp lst)))
      0
      (+ (car lst) (sum-list (cdr lst))))
  ///
 (define sum-list-ash ((lst nat-listp) (n natp))
  :returns (sum integerp)
  (if (or (atom lst) (not (nat-listp lst)))
      0
      (+ (ash (car lst) n) (sum-list-ash (cdr lst) n)))
  ///
  (local (defthm ash-0-lemma (equal (ash 0 n) 0)))
  (local (in-theory (disable ash)))
  (defthm sum-list-ash-sum-list
    (implies (and (nat-listp chunks) (natp n))
	     (equal (sum-list-ash chunks n)
		    (ash (sum-list chunks) n)))
    :hints (("Subgoal *1/3" :use ((:instance +-of-left-ash (x (car chunks)) (y (sum-list (cdr chunks)))))))))))
;; end encapsulate




(include-book "centaur/gl/gl" :dir :system)

(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;
;;	     ;;
;;    SRL    ;;
;;	     ;;
;;;;;;;;;;;;;;;


(define SRLi-helper ((x natp) (y natp) (k natp))
 (if (zp k)
     (* (eqw k y) (ash x (- y)))
     (+ (* (eqw k y) (ash x (- y)))
        (srli-helper x y (1- k))))
 ///
 (local (defthm srli-helper-subterm
  (implies (and (natp y) (natp k) (< k y))
 	   (equal (* (eqw k y) (ash x (- y))) 0))))

 (local (defthm srli-helper-when-k-<-y
  (implies (and (natp y) (natp k) (< k y))
	   (equal (srli-helper x y k) 0))))

 (local (defthm srli-helper-when-k-=-y
  (implies (and (natp y) (natp k) (= k y))
	   (equal (srli-helper x y k) (ash x (- y))))))

 (local (defthm srli-helper-when-y-<-k
  (implies (and (natp y) (natp k) (< y k))
	   (equal (srli-helper x y k) (ash x (- y))))))

 (local (defthm srli-helper-ash
  (implies (and (natp y) (natp k))
	   (equal (srli-helper x y k)
		  (if (< k y) 
                      0
		      (ash x (- y)))))
  :hints (("Goal" :cases ((= k y) (< y k) (< k y))))))
)





