(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
;(include-book "eq")


;;;;;;;;;;;;;;
;;	    ;;
;;    left msb
;;	    ;;
;;;;;;;;;;;;;;
(define left-msb ((x :type unsigned-byte) y)
  :irrelevant-formals-ok t
  :ignore-ok t
  :returns (eq? bitp)
 (logbit 31 x))

(gl::def-gl-thm left-msb-correctness-32
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (left-msb x y)
               (if (<= (expt 2 31) x) 1 0))
 :g-bindings (gl::auto-bindings (:nat x 32)))
