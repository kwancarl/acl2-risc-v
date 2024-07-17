
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;; EQ
;; Equality of bit
;; (x_0*y_0 + (1-x_0)*(1-y_0)) == 1
(define b-eqw ((x0 bitp) (y0 bitp))
  (b-xor (b-and x0 y0)
	 (b-and (b-xor 1 x0)
		(b-xor 1 y0)))
  ///
  (defthm b-eqw-equal-equiv
    (implies (and (bitp x0) (bitp y0))
             (equal (b-eqw x0 y0)
               	    (if (equal x0 y0) 1 0)))
    :hints (("Goal" :cases ((equal x0 0)))))

 (defthmd symmetry-of-b-ewq
   (equal (b-eqw x y) (b-eqw y x)))

 (defthmd transitivity-of-b-ewq
   (implies (and (b-eqw x y) (b-eqw y w))
            (b-eqw x w))))


(local (defthm natp-of-integer-length
  (natp (integer-length x))))
(local (defthm natp-when-not-bitp
  (implies (and (natp x) (not (bitp x)))
	   (<= 2 x))
  :hints (("Goal" :in-theory (enable bitp))))) 
(local (defthm integer-length->-0
  (implies (and (natp x) (not (bitp x)))
	   (< 0 (integer-length x)))
  :hints (("Goal" :in-theory (enable integer-length)))))

;; Equality of a chunk of size w/c
;; (x_0*y_0 + (1-x_0)*(1-y_0)) * recurse
(define eqw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  :returns (eq? bitp)
  (b* (((unless (and (natp x) (natp y))) 0)
       ((if (and (bitp x) (bitp y))) (b-eqw x y))
       ((if (xor (bitp x) (bitp y))) 0)
       (x0  	(loghead 1 x))
       (y0  	(loghead 1 y))
       (eq0 	(b-eqw x0 y0))
       (x-rest  (ash x -1))
       (y-rest  (ash y -1)))
      (b-and eq0 (eqw x-rest y-rest)))
  ///

  (local (defthm lemma-1 
    (implies (natp x)
	     (equal x (logapp 1 (loghead 1 x) (logtail 1 x))))
    :rule-classes nil))

  (defthm equal-logapp-loghead-logtail-1
    (implies (and (equal (logtail 1 x) (logtail 1 y))
		  (equal (loghead 1 x) (loghead 1 y))
		  (natp x) 
 		  (natp y))
 	     (equal x y))
    :hints (("Goal" :use ((:instance lemma-1)
			  (:instance lemma-1 (x y)))))
    :rule-classes nil)


  (defthmd eqw-equal-equiv
    (implies (and (natp x) (natp y))
	     (equal (eqw x y)
	            (if (equal x y) 1 0)))
    :hints (("Subgoal *1/3" :use ((:instance equal-logapp-loghead-logtail-1)))))) ;; end define

(gl::def-gl-thm eqw-equal-equiv-gl
  :hyp   (and (unsigned-byte-p 128 x)
              (unsigned-byte-p 128 y))
  :concl (equal (eqw x y)
      	  (if (equal x y) 1 0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 128) (:nat y 128))))

(local
  (defthm natp-lemma-1
    (implies (and (posp a) (posp c))
	     (< (nfix (- a c))
		a))))

(local
  (defthm natp-lemma-2
    (implies (and (natp a) (natp b) (natp c) (natp d) (< a b) (< c d))
	     (< (+ a c) (+ b d)))))


(local
  (defthm natp-lemma-3
    (implies (and (natp a) (natp b) (posp c) (not (zerop a)) (not (zerop b)))
	     (< (+ (nfix (- a c)) (nfix (- b c)))
		(+ a b)))
    :hints (("Goal" :use ((:instance natp-lemma-1)
			  (:instance natp-lemma-1 (a b)))))))


(define eqwc ((x :type unsigned-byte)
	     (y :type unsigned-byte)
	     (wc natp))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :use ((:instance natp-lemma-3
				   (a (integer-length x))
				   (b (integer-length y))
				   (c wc)))))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((unless (posp wc)) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 1)
       ((if (xor (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (car-chunk-x  (loghead wc x))
       (car-chunk-y  (loghead wc y))
       (car-chunk-eq (eqw car-chunk-x car-chunk-y))
       (cdr-chunk-x  (logtail wc x))
       (cdr-chunk-y  (logtail wc y)))
      (b-and car-chunk-eq 
	     (eqwc cdr-chunk-x cdr-chunk-y wc)))
  ///

  (local (defthm lemma-1 
    (implies (and (natp x) (natp k))
	     (equal x (logapp k (loghead k x) (logtail k x))))
    :rule-classes nil))

  (defthm equal-logapp-loghead-logtail-k
      (implies (and (equal (logtail k x) (logtail k y))
  		    (equal (loghead k x) (loghead k y))
  		    (natp x) 
   		    (natp y)
   	 	    (natp k))
   	     (equal x y))
      :hints (("Goal" :use ((:instance lemma-1)
  			  (:instance lemma-1 (x y)))))
      :rule-classes nil)

  (local
    (defthm integer-length-0-implies-0
      (implies (and (natp x) (zerop (integer-length x)))
	       (zerop x))
      :hints (("Goal" :in-theory (enable integer-length)))
      :rule-classes :type-prescription))

  (local (in-theory (enable eqw-equal-equiv)))
  (defthm eqwc-equal-equiv
    (implies (and (natp x)
		  (natp y)
		  (posp wc))
	     (equal (eqwc x y wc)
		    (if (equal x y) 1 0)))
    :hints (("Subgoal *1/1" :use ((:instance integer-length-0-implies-0)
				  (:instance integer-length-0-implies-0 (x y))))
            ("Subgoal *1/3" :use ((:instance equal-logapp-loghead-logtail-k
					     (k wc))))))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;		         	;;
;;    Set Less Than Unsigned    ;;
;;			        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define b-ltu ((x0 bitp) (y0 bitp))
  :returns (lt bitp)
  :enabled t
  (b-and (b-xor 1 x0) y0)
  ///
  (defthm b-ltu-<-equiv
    (implies (and (bitp x) (bitp y))
	     (equal (b-ltu x y)
		    (if (< x y) 1 0)))))
(define ltu-i ((x :type unsigned-byte)
	       (y :type unsigned-byte)
               (i natp))
  :returns (lti bitp)
  (b-and (b-ltu (logbit i x) (logbit i y))
	 (eqw (logtail i x) (logtail i y)))
  /// 

;  (defthm ltu-i-when-<
;    (implies (and (< x y) 
;		  (natp x)
;		  (natp y)
;		  (logbitp i y)
;		  (not (logbitp i x))
;		  (equal (logtail i x) (logtail i y)))
;	     (equal (ltu-i x y i) 1)))

		    

;  (defthm ltu-i-when->=
;    (implies (and (natp i) (natp x) (natp y) (<= y x))
;	     (equal (ltu-i x y i) 0)))
;    :hints (("Goal" :cases ((equal (logtail i x)
;				   (logtail i y)))))
)

;(local (in-theory (enable ltu-i)))
;(gl::def-gl-thm ltu-i-when-<
;  :hyp (and (< x y)
;	    (unsigned-byte-p 32 x)
;	    (unsigned-byte-p 32 y)
;  	    (natp i)
;	    (< i 65)
;	    (logbitp i y)
;	    (not (logbitp i x))
;	    (equal (logtail i x) (logtail i y)))
;  :concl (equal (ltu-i x y i) 1)
;  :g-bindings (gl::auto-bindings (:mix (:nat x 32)
;				       (:nat y 32))
;				 (:nat i 7)))

;(defthm loghead-logtail-<
;  (implies (and (natp x)
;	       	(natp y)
;		(natp i)
;;		(< x y)
;		(equal (logtail i x) (logtail i y)))
;	   (< (loghead i x) (loghead i y)))
;  :hints (("Goal" :in-theory (enable logtail loghead))))

(define ltu-0 ((x :type unsigned-byte) (y :type unsigned-byte))
  :enabled t
  (b-and (b-ltu (logbit 1 x) (logbit 1 y))
	 (eqw (logtail 1 x) (logtail 1 y)))
  ///
;  (defthm ltu-0-when-<
;   (implies (and (< x y) 
;		 (natp x)
;		 (natp y)
;		 (logbitp 1 y)
;		 (not (logbitp 1 x))
;		 (equal (logtail 1 x) (logtail 1 y)))
;	     (equal (ltu-0 x y) 1)))
;
;
;  (defthm ltu-0-when->=
;    (implies (and (natp i) (natp x) (natp y) (<= y x))
;	     (equal (ltu-0 x y) 0))
;    :hints (("Goal" :cases ((equal (logtail 1 x)
;				   (logtail 1 y))))))
;)

)

(define ltuw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (max (integer-length x) (integer-length y))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (xcar (loghead 1 x))
       (ycar (loghead 1 y))
       (xcdr (logtail 1 x))
       (ycdr (logtail 1 y))
       (ltu0 (b-and (b-and (b-xor 1 xcar) ycar)
		    (eqw xcdr ycdr))))
      (b-xor ltu0 (ltuw xcdr ycdr)))
)

;(gl::def-gl-thm ltu-<-equiv-gl
;  :hyp   (and (unsigned-byte-p 256 x)
;              (unsigned-byte-p 256 y))
;  :concl (equal (ltuw x y)
;      	  	(if (< x y) 1 0))
;  :g-bindings (gl::auto-bindings (:mix (:nat x 256) (:nat y 256))))

(gl::def-gl-thm ltu-<-equiv-gl
  :hyp   (and (unsigned-byte-p 64 x)
              (unsigned-byte-p 64 y))
  :concl (equal (ltuw x y)
      	  	(if (< x y) 1 0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 256) (:nat y 256))))


(define ltuwc ((x :type unsigned-byte) (y :type unsigned-byte) (wc posp))
  :returns (ltu? bitp)
  :measure (max (integer-length x) (integer-length y))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((unless (posp wc)) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (car-chunk-x    (loghead wc x))
       (car-chunk-y    (loghead wc y))
       (cdr-chunk-x    (logtail wc x))
       (cdr-chunk-y    (logtail wc y))
       (cdr-chunk-eq   (eqw cdr-chunk-x cdr-chunk-y))
       (car-chunk-ltuw (ltuw car-chunk-x car-chunk-y)))
      (b-xor (b-and car-chunk-ltuw cdr-chunk-eq)
	     (ltuwc cdr-chunk-x cdr-chunk-y wc))))

(def-gl-thm ltuwc-<-equiv-gl
  :hyp (and (unsigned-byte-p 64 x)
  	    (unsigned-byte-p 64 y))
  :concl (equal (ltuwc x y 8)
		(if (< x y) 1 0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 256) (:nat y 256))))


;;;;;;;;;;;;;;;
;;	     ;;
;;    AND    ;;
;;	     ;;
;;;;;;;;;;;;;;;

(define andw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :in-theory (enable logcdr integer-length)))
  (b* (((unless (and (natp x) (natp y) 0)))
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0))
      (+ (b-and (logcar x) (logcar y))
         (* 2 (andw (logcdr x) (logcdr y))))))

(local (include-book "ihs/logops-lemmas" :dir :system))
(defthm andw-logand-equiv
  (implies (and (natp x) (natp y))
	   (equal (andw x y) (logand x y)))
  :hints (("Goal" :in-theory (enable andw))))

(gl::def-gl-thm andw-logand-equiv-gl
  :hyp   (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
  :concl (equal (andw x y) (logand x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 256) (:nat y 256))))


;;;;;;;;;;;;;;
;;	    ;;
;;    OR    ;;
;;	    ;;
;;;;;;;;;;;;;;

(define orw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :in-theory (enable logcdr integer-length)))
  (b* (((unless (and (natp x) (natp y) 0)))
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (x0 (logcar x))
       (y0 (logcar y)))
      (+ (b-xor (b-xor x0 y0) (b-and x0 y0))
         (* 2 (orw (logcdr x) (logcdr y))))))

;(defthmd b-owr-b-ior-equiv
;  (implies (and (bitp x) (bitp y))
;	   (equal (b-xor (b-xor x y) (b-and x y)) (b-ior x y)))
;  :hints (("Goal" :cases ((equal x 0)))))

(defthm orw-logior-equiv
  (implies (and (natp x) (natp y))
	   (equal (orw x y) (logior x y)))
  :hints (("Goal" :in-theory (enable orw))))

(gl::def-gl-thm orw-logior-equiv-gl
  :hyp   (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
  :concl (equal (orw x y) (logior x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 256) (:nat y 256))))


;;;;;;;;;;;;;;;
;;	     ;;
;;    XOR    ;;
;;	     ;;
;;;;;;;;;;;;;;;

(define xorw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :in-theory (enable logcdr integer-length)))
  (b* (((unless (and (natp x) (natp y) 0)))
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (x0 (logcar x))
       (y0 (logcar y)))
      (+ (b-xor (b-and x0 (b-xor 1 y0)) (b-and y0 (b-xor 1 x0)))
         (* 2 (xorw (logcdr x) (logcdr y))))))

(local (defthm b-xowr-b-xor-equiv
  (implies (and (bitp x0) (bitp y0))
           (equal (b-xor (b-and x0 (b-xor 1 y0)) (b-and y0 (b-xor 1 x0)))
		  (b-xor x0 y0)))
  :hints (("Goal" :cases ((equal x0 0))))))

(gl::def-gl-thm xorw-logxor-equiv-gl
  :hyp   (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
  :concl (equal (xorw x y) (logxor x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 256) (:nat y 256))))

;; ACL2 has trouble believing xorw x 0 = x for some reason.
;; Since there is little motivation to prove arbitrary length, I'll leave this for now
;(local (defthm lemma-1
;  (implies (and (natp x))
;	   (equal (xorw x 0) x))
;  :hints (("Goal" ;:induct (xorw x 0)
;  		  :expand (xorw x 0)))))
;
;(defthm xorw-logxor-equiv
;  (implies (and (natp x) (natp y))
;	   (equal (xorw x y) (logxor x y)))
;  :hints (("Goal" :in-theory (enable xorw))))


;;;;;;;;;;;;;;;
;;	     ;;
;;    ADD    ;;
;;	     ;;
;;;;;;;;;;;;;;;

(define addw-helper ((z integerp)) 
  (b* (((unless (natp z)) 0)
       ((if (zerop (integer-length z))) 0))
      (+ (logcar z) (* 2 (addw-helper (logcdr z)))))
  ///
  (defthm addw-helper-identity
    (equal (addw-helper z) (nfix z))))
	
(define addw ((x integerp) (y integerp))
  (addw-helper (+ x y))
  ///
  (defthm addw-+-equiv 
    (implies (and (natp x) (natp y)) 
	     (equal (addw x y) (+ x y)))))


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
  ;(local (include-book "ihs/logops-lemmas" :DIR :SYSTEM))
  (defthm sll-ash
   (implies (and (natp y))
             (equal (sll x y) (ash x y)))
   :hints (("Goal" :cases ((zp y) (posp y)))))))
;; end define







;;;;;;;;;;;;;;;
;;	     ;;
;;    SUB    ;;
;;	     ;;
;;;;;;;;;;;;;;;

;; Prove guard conjecture for subw
(local (include-book "centaur/bitops/integer-length" :dir :system))
(define subw ((x :type signed-byte) (y :type signed-byte))
  (addw x (logxor 1 (lognot y))))

;(gl::def-gl-thm subw---equiv-gl
;  :hyp   (and (signed-byte-p 2 x) (signed-byte-p 2 y))
;  :concl (equal (subw x y) (- x y))
;  :g-bindings (gl::auto-bindings (:mix (:nat x 256) (:nat y 256))))
;
;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;			      ;;
;;    Set Less Than Signed    ;;
;;			      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(define ltsw ((x :type signed-byte) (y :type signed-byte) (w natp))
;  (b* (((unless (natp w)) 0)
;       ((unless (and (signed-byte-p w x) 
;		     (signed-byte-p w y))) 0)
;       (xs (logbit (- w 1) x))
;       (ys (logbit (- w 1) y))
;       (xr (loghead (- w 1) x))
;       (yr (loghead (- w 1) y)))
;      (b-xor (b-and xs (b-xor 1 ys)) 
;	     (b-and (b-eqw xs ys) (ltuw xr yr)))))
;
;(defthm ltsw-<-equiv


;(define ltsw32 ((x :type unsigned-byte) (y :type unsigned-byte))
;  (b* (((unless (and (unsigned-byte-p 32 x) 
;		     (unsigned-byte-p 32 y))) 0)
;       (xs (logbit (- 32 1) x))
;       (ys (logbit (- 32 1) y))
;       (xr (loghead (- 32 1) x))
;       (yr (loghead (- 32 1) y)))
;      (b-xor (b-and xs (b-xor 1 ys)) 
;	     (b-and (b-eqw xs ys) (ltuw xr yr)))))
;
;
;
;;; sbcl has a control stack problem, try with ccl
;(gl::def-gl-thm ltsw-<-equiv-gl
;  :hyp   (and (unsigned-byte-p 32 x) 
;              (unsigned-byte-p 32 y))
;  :concl (equal (ltsw32 x y) (if (< (fast-logext 32 x) (fast-logext 32 y)) 1 0))
;  :g-bindings (gl::auto-bindings (:nat x 32) (:nat y 32)))

;; Immediate Load (Equivalent to ADD
	














