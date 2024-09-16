(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
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

 (local (in-theory (enable eqw-equal-equiv)))
 
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
  :hints (("Goal" :cases ((= k y) (< y k) (< k y)))))))


;;;;;;;;;;;;;
;;
;; Chunking and append
;;
;;;;;;;;;;;;;
;(include-book "centaur/bitops/ihsext-basics" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system)


(include-book "centaur/bitops/part-select" :DIR :SYSTEM)
(include-book "centaur/bitops/merge" :DIR :SYSTEM)

;(define chunk-for-shift-32 (x)
;  :enabled t
;  (b* (((unless (unsigned-byte-p 32 x)) 0)
;       ;; chunk
;       (u8-0 (part-select x :low  0 :width 8))
;       (u8-1 (part-select x :low  8 :width 8))
;       (u8-2 (part-select x :low 16 :width 8))
;       (u8-3 (part-select x :low 24 :width 8))

(gl::def-gl-thm part-select-lemma-1
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (ash (part-select x :low 8 :width 8) 8)
	       (logand x #b1111111100000000))
 :g-bindings (gl::auto-bindings (:nat x 32)))


(gl::def-gl-thm part-select-lemma-2
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (part-select x :low 0 :width 8)
	       (logand x #b11111111))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-param-thm lemma-3
 :hyp (and (unsigned-byte-p 12 x) (unsigned-byte-p 5 y))
 :concl (equal (+ (ash (logand x #x000000ff) y)
	          (ash (logand x #x0000ff00) y)
	          (ash (logand x #x00ff0000) y)
	          (ash (logand x #xff000000) y))
	       (ash (+ (logand x #x000000ff)
                       (logand x #x0000ff00)
                       (logand x #x00ff0000)
                       (logand x #xff000000))
		      y))
    :param-bindings
    `((((low  0) (high  4)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low  4) (high  8)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low  8) (high 12)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 12) (high 16)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 16) (high 20)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 20) (high 24)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 24) (high 28)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 28) (high 32)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 32) (high 33)) ,(gl::auto-bindings (:nat x 32) (:nat y 5))))
    :param-hyp (or (and (<= (expt 2 low) x) (< x (expt 2 high))) (= x 0))
    :cov-bindings (gl::auto-bindings (:nat x 32) (:nat y 5)))

;(gl::def-gl-thm part-select-lemma-3
; :hyp (and (unsigned-byte-p 5 y) (unsigned-byte-p 32 x))
; :concl (equal (ash (part-select x :low 8 :width 8) 8)
;	       (ash (logand x #b1111111100000000) (- y))
; :g-bindings (gl::auto-bindings (:nat x 32)))


(define chunk-and-shift-32 (x y)
  :enabled t
  (b* (((unless (unsigned-byte-p 32 x)) 0)
       ((unless (unsigned-byte-p  5 y)) 0)
       ;; chunk
       (u8-0 (part-select x :low  0 :width 8))
       (u8-1 (part-select x :low  8 :width 8))
       (u8-2 (part-select x :low 16 :width 8))
       (u8-3 (part-select x :low 24 :width 8))
       ;; shift chunks
       (u8-0 (ash      u8-0     (- y)))
       (u8-1 (ash (ash u8-1  8) (- y)))
       (u8-2 (ash (ash u8-2 16) (- y)))
       (u8-3 (ash (ash u8-3 24) (- y))))
       ;; add chunks
      (+ u8-3 u8-2 u8-1 u8-0)))


(include-book "centaur/fgl/top" :dir :system)

;; start an external shell from which the SAT solver can be called
(value-triple (acl2::tshell-ensure))

(fgl::def-fgl-param-thm lemma-1
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
 :concl (equal (+ (ash (logand x #x000000ff) y)
	          (ash (logand x #x0000ff00) y)
	          (ash (logand x #x00ff0000) y)
	          (ash (logand x #xff000000) y))
	       (ash (+ (logand x #x000000ff)
                       (logand x #x0000ff00)
                       (logand x #x00ff0000)
                       (logand x #xff000000))
		      y))
    :param-bindings
    `((((low  0) (high  4)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low  4) (high  8)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low  8) (high 12)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 12) (high 16)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 16) (high 20)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 20) (high 24)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 24) (high 28)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 28) (high 32)) ,(gl::auto-bindings (:nat x 32) (:nat y 5)))
      (((low 32) (high 33)) ,(gl::auto-bindings (:nat x 32) (:nat y 5))))
    :param-hyp (or (and (<= (expt 2 low) x) (< x (expt 2 high))) (= x 0))
    :cov-bindings (gl::auto-bindings (:nat x 32) (:nat y 5)))

(fgl::def-fgl-thm srl-correctness-32
 :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
 :concl (equal (chunk-and-shift-32 x y)
               (ash x (- y))))
 ;:g-bindings (gl::auto-bindings (:nat x 32) (:nat y 5)))


(define chunk-for-shift (x n)
  :enabled t
  :returns (chunks true-listp)
  :measure (acl2-count n)
  (if (or (not (natp n)) (not (natp x)))
      nil
      (if (zerop n)
          nil
          (cons (loghead 8 x)
    	        (chunk-for-shift (logtail 8 x) (1- n))))))

(define concat-chunks (chunks)
  :returns (word natp)
  (if (atom chunks)
      0 
      (logapp 8 (nfix (car chunks)) (concat-chunks (cdr chunks)))))

(gl::def-gl-thm concat-chunks-32
  :hyp (unsigned-byte-p 32 x)
  :concl (equal (concat-chunks (chunk-for-shift x 4)) x)
  :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm concat-chunks-64
  :hyp (unsigned-byte-p 64 x)
  :concl (equal (concat-chunks (chunk-for-shift x 8)) x)
  :g-bindings (gl::auto-bindings (:nat x 64)))

;; Chunk and shifting
;; takes the i-th chunk and shifts it right by y
(define shift-chunk (chunk i y)
 :enabled t
 :returns (shifted natp)
 (if (not (and (natp i) (natp chunk) (natp y)))
     0
     (ash (ash chunk i) (- y))))

(define shift-chunks (chunks i y)
 :enabled t
 :returns (shifted-chunks true-listp)
 (if (or (atom chunks) (not (natp i)))
     nil
     (cons (shift-chunk  (car chunks) i y)
	   (shift-chunks (cdr chunks) (+ i 8) y))))

(defthm chunk-for-shift-32-expand
  (implies (unsigned-byte-p 32 x)
           (equal (chunk-for-shift x 4)
		  (list (loghead 8 x) 
			(loghead 8 (logtail 8 x)) 
			(loghead 8 (logtail 16 x)) 
			(loghead 8 (logtail 24 x)) )))
  :hints (("Goal" :expand ((chunk-for-shift x 4)
  		 	   (chunk-for-shift (logtail 8 x) 3)
  		 	   (chunk-for-shift (logtail 16 x) 2)))))

(defthm shift-chunks-chunk-for-shift-32
  (implies (and (unsigned-byte-p 32 x) (natp y))
           (equal (shift-chunks (chunk-for-shift x 4) 0 y)
		  (list (ash (loghead 8 x) (- y))
			(ash (ash (loghead 8 (logtail 8 x)) 8) (- y))
			(ash (ash (loghead 8 (logtail 16 x)) 16) (- y))
			(ash (ash (loghead 8 (logtail 24 x)) 24) (- y)))))
  :hints (("Goal" :expand ((chunk-for-shift x 4)
  		 	   (chunk-for-shift (logtail 8 x) 3)
  		 	   (chunk-for-shift (logtail 16 x) 2)))))


;(gl::def-gl-thm lemma-1
; :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
; :concl (equal (ash (ash (loghead 8 (logtail 8 x)) 8) (- y))
;	       (ash (




(define srl-combine (chunks)
  (if (atom chunks)
      0
      (+ (nfix (car chunks)) (srl-combine (cdr chunks)))))

(fgl::def-fgl-thm shift-and-concat-chunks-32
  :hyp (and (unsigned-byte-p 32 x) (unsigned-byte-p 5 y))
  :concl (equal (srl-combine
		  (shift-chunks 
		    (chunk-for-shift x 4)
		    0
		    y))
		(ash x (- y))))








