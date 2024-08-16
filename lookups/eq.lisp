(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;
;;	    ;;
;;    EQ    ;;
;;	    ;;
;;;;;;;;;;;;;;

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
					     (k wc)))))))
