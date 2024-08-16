(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "centaur/gl/gl" :dir :system)

(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))

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

(defthmd b-owr-b-ior-equiv
  (implies (and (bitp x) (bitp y))
	   (equal (b-xor (b-xor x y) (b-and x y)) (b-ior x y)))
  :hints (("Goal" :cases ((equal x 0)))))

(defthm orw-logior-equiv
  (implies (and (natp x) (natp y))
	   (equal (orw x y) (logior x y)))
  :hints (("Goal" :in-theory (enable orw))))

(gl::def-gl-thm orw-logior-equiv-gl
  :hyp   (and (unsigned-byte-p 32 x) (unsigned-byte-p 32 y))
  :concl (equal (orw x y) (logior x y))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32 ))))

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
(local
  (defthm natp-lemma-4
    (implies (and (natp a) (posp c) (not (zerop a)))
             (< (nfix (- a c)) a))))
(define or-wc  ((x :type unsigned-byte)
                (y :type unsigned-byte)
                (wc natp))
  :measure (max (integer-length x) (integer-length y))
  :hints (("Goal" :use ((:instance natp-lemma-4 (a (integer-length y)) (c wc)))))
  (b* (((unless (and (natp x) (natp y))) 0)
       ((unless (posp wc)) 0)
       ((if (and (zerop (integer-length x)) (zerop (integer-length y)))) 0)
       (car-chunk-x   (loghead wc x))
       (car-chunk-y   (loghead wc y))
       (car-chunk-or  (orw car-chunk-x car-chunk-y))
       (cdr-chunk-x   (logtail wc x))
       (cdr-chunk-y   (logtail wc y)))
      (logapp wc
              car-chunk-or
              (or-wc cdr-chunk-x cdr-chunk-y wc))))

(gl::def-gl-thm orw-or-wc-equiv-32-gl
 :hyp (and (unsigned-byte-p 32 x)
           (unsigned-byte-p 32 y))
 :concl (equal (or-wc x y 8) (orw x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

(gl::def-gl-thm orw-or-wc-equiv-64-gl
 :hyp (and (unsigned-byte-p 64 x)
           (unsigned-byte-p 64 y))
 :concl (equal (or-wc x y 8) (orw x y))
 :g-bindings (gl::auto-bindings (:mix (:nat x 64) (:nat y 64))))


;(defthm orw-or--wc-equiv
; (implies (and (natp x) (natp y))
;          (equal (or-wc x y 8) (orw x y)))
; :hints (("Goal" :in-theory (enable or-wc orw))))





;; ------------ x
;; ------------ y
;; to indices
;; ---- ---- ---- ---- x
;; ---- ---- ---- ---- y
;;
;; x

