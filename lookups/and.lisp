(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
;(local (include-book "ihs/basic-definitions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;(local (include-book "centaur/bitops/fast-logext" :dir :system))
;(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;
;;           ;;
;;    AND    ;;
;;           ;;
;;;;;;;;;;;;;;;

(define andw ((x :type unsigned-byte) (y :type unsigned-byte))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :in-theory (enable logcdr integer-length)))
  (b* (((unless (and (natp x) (natp y) 0)))
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0))
      (+ (b-and (logcar x) (logcar y))
         (* 2 (andw (logcdr x) (logcdr y))))))
  
(defthm andw-logand-equiv
  (implies (and (natp x) (natp y))
           (equal (andw x y) (logand x y)))
  :hints (("Goal" :in-theory (enable andw))))

(gl::def-gl-thm andw-logand-equiv-gl
  :hyp   (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
  :concl (equal (andw x y) (logand x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

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
(define and-wc ((x :type unsigned-byte)
                (y :type unsigned-byte)
                (wc natp))
  :measure (+ (integer-length x) (integer-length y))
  :hints (("Goal" :use ((:instance natp-lemma-3
                                   (a (integer-length x))
                                   (b (integer-length y))
                                   (c wc)))))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((unless (posp wc)) 0)
       ((if (or (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (car-chunk-x   (loghead wc x))
       (car-chunk-y   (loghead wc y))
       (car-chunk-and (andw car-chunk-x car-chunk-y))
       (cdr-chunk-x   (logtail wc x))
       (cdr-chunk-y   (logtail wc y)))
      (logapp wc 
              car-chunk-and
              (and-wc cdr-chunk-x cdr-chunk-y wc))))

(gl::def-gl-thm andw-and-wc-equiv-32-gl
 :hyp (and (unsigned-byte-p 32 x)
           (unsigned-byte-p 32 y))
 :concl (equal (and-wc x y 8) (andw x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))


