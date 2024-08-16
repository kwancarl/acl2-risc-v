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
;;    right msb
;;	    ;;
;;;;;;;;;;;;;;
(define right-msb (x (y :type unsigned-byte))
  :irrelevant-formals-ok t
  :ignore-ok t
  :returns (msb bitp)
 (logbit 31 y))

(gl::def-gl-thm right-msb-correctness-32
 :hyp (unsigned-byte-p 32 y)
 :concl (equal (right-msb x y)
               (if (<= (expt 2 31) y) 1 0))
 :g-bindings (gl::auto-bindings (:nat y 32)))
