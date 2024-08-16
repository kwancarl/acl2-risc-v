(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "eq")


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
;;;;;;;;;;;;;;;;;;
;;	        ;;
;;    SHIFTS    ;;
;;	        ;;
;;;;;;;;;;;;;;;;;;
(define sllk ((x natp) (k natp) )
 (ash x k)
 ///
 (defthm sllk-of-zero
  (equal (sllk x 0) (ifix x))))
;; see :doc ash*
;(local (include-book "ihs/logops-lemmas" :DIR :SYSTEM))

(define sll-helper ((x natp) (y natp) (k natp))
 (if (zp k)
     (* (eqw k y) (sllk x k))
     (+ (* (eqw k y) (sllk x k))
	(sll-helper x y (1- k))))
 ///
 (defthm eqw-when-not-equal
  (implies (and (natp k) (natp y) (not (equal k y)))
           (equal (eqw k y) 0))
  :hints (("Goal" :use ((:instance eqw-equal-equiv (x k))))))

 (defthm eqw-when-equal
  (implies (and (natp k) (natp y) (equal k y))
           (equal (eqw k y) 1))
  :hints (("Goal" :use ((:instance eqw-equal-equiv (x k))))))

 (local (defthm sll-helper-when-k-<-y
  (implies (and (natp k) (natp y) (< k y))
           (equal (sll-helper x y k) 0))))

 (local (defthm sll-helper-when-y-=-k
  (implies (and (natp k) (natp y) (= k y))
           (equal (sll-helper x y k) 
		  (sllk x y)))))

 (local (defthm sll-helper-subterm-when-y-<-k
  (implies (and (natp k) (natp y) (< k y))
           (equal (* (eqw k y) (sllk x k)) 0))))

 (local (defthm sll-helper-when-y-<-k
  (implies (and (natp k) (natp y) (< y k))
           (equal (sll-helper x y k) 
		  (sllk x y)))))

 (local (defthm sll-helper-sllk
  (implies (and (natp k) (natp y) (<= y k))
           (equal (sll-helper x y k) 
		  (sllk x y)))
  :hints (("Goal" :cases ((= y k) (< y k))))))

 (local (defthm sll-helper-ash
  (implies (and (natp k) (natp y) (<= y k))
           (equal (sll-helper x y k) 
		  (ash x y)))
  :hints (("Goal" :in-theory (enable sllk)))))

 (local (defthm expt-lemma
  (implies (posp y) (<= y (expt 2 y)))
  :hints (("Goal" :in-theory (enable expt)))))

 (define sll ((x natp) (y natp))
  :guard-hints (("Goal" :cases ((zp y) (posp y))))
  (mbe :logic (if (not (natp y))
                  (ifix x)
		  (sll-helper x y (expt 2 y)))
       :exec  (ash x y))
  ///
  (defthm sll-ash
   (implies (and (natp y))
            (equal (sll x y) (ash x y)))
   :hints (("Goal" :cases ((zp y) (posp y)))))))




