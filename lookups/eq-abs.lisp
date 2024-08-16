(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(include-book "eq")


;; NOT SURE WHAT THIS IS FOR

;;;;;;;;;;;;;;
;;	    ;;
;;    EQ-ABS    ;;
;;	    ;;
;;;;;;;;;;;;;;
(define eq-abs-w ((x :type unsigned-byte) (y :type unsigned-byte) (w posp))
  :returns (eq? bitp)
  (b* (((unless (and (natp x) (natp y) (posp w))) 0)
       (x-abs  (loghead (1- w) x))
       (y-abs  (loghead (1- w) y)))
      (eqw x-abs y-abs))
)

(gl::def-gl-thm logbitp-when-<=-2^32
  :hyp   (and (unsigned-byte-p 32 x))
  :concl (equal (logbitp 31 x)
              (<= (expt 2 31) x))
  :g-bindings (gl::auto-bindings (:nat x 32)))


;;
;; 0b1111 = -1
;; 0b0111 = 7
;;
;(gl::def-gl-thm abs-of-logext
;  :hyp   (and (unsigned-byte-p 32 x))
;  :concl (equal (abs



(gl::def-gl-thm abs-of-logext-32-gl
  :hyp   (and (unsigned-byte-p 32 x)
              (unsigned-byte-p 32 y))
  :concl (equal (eq-abs-w x y 32)
                (if (equal (logext 32 x) (logext 32 y))
                    1
                    0))
  :g-bindings (gl::auto-bindings (:mix (:nat x 32) (:nat y 32))))

