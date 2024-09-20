(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/fast-logext" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(include-book "subtable")


;;;;;;;;;;;;;;
;;	    ;;
;;    right msb
;;	    ;;
;;;;;;;;;;;;;;
(define right-msb-8 (x (y :type unsigned-byte))
  :irrelevant-formals-ok t
  :ignore-ok t
  ;:enabled t
  :returns (msb bitp)
 (logbit 7 y))

(gl::def-gl-thm right-msb-8-correctness
 :hyp (unsigned-byte-p 8 y)
 :concl (equal (right-msb-8 x y)
               (if (<= (expt 2 7) y) 1 0))
 :g-bindings (gl::auto-bindings (:nat y 8)))

;(define right-msb-32 (x (y :type unsigned-byte))
;  :irrelevant-formals-ok t
;  :ignore-ok t
;  :returns (msb bitp)
; (logbit 31 y))
;
;(gl::def-gl-thm right-msb-32-correctness
; :hyp (unsigned-byte-p 32 y)
; :concl (equal (right-msb x y)
;               (if (<= (expt 2 31) y) 1 0))
; :g-bindings (gl::auto-bindings (:nat y 8)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                      ;;
;;    right-msb    ;;
;;                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun materialize-right-msb-8-subtable (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x y)                    idx))
     (cons (cons idx (right-msb-8 x y))
           (materialize-right-msb-8-subtable rst))))

(defthm alistp-of-materialize-right-msb-8-subtable
 (alistp (materialize-right-msb-8-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-right-msb-8-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-right-msb-8-subtable idx-lst))))

(defthm assoc-member-materialize-right-msb-8-subtable
 (implies (assoc (cons x y) (materialize-right-msb-8-subtable idx-lst))
          (member (cons x y) idx-lst)))

(defthm assoc-materialize-right-msb-8-subtable
 (implies (assoc (cons i j) (materialize-right-msb-8-subtable idx-lst))
          (equal (assoc (cons i j) (materialize-right-msb-8-subtable idx-lst))
                 (cons (cons i j) (right-msb-8 i j)))))

(defthm materialize-right-msb-8-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-x-indices x-hi y-hi))
               (subtable (materialize-right-msb-8-subtable indices)))
              (equal (assoc-equal (cons i j) subtable)
                     (cons (cons i j)
                           (right-msb-8 i j))))))

(defthm lookup-materialize-right-msb-8-subtable-correctness
 (implies (and (natp x-hi)
               (natp y-hi)
               (natp i)
               (natp j)
               (<= i x-hi)
               (<= j y-hi))
          (b* ((indices  (create-x-indices x-hi y-hi))
               (subtable (materialize-right-msb-8-subtable indices)))
              (equal (lookup i j subtable)
                     (logbit 7 j))))
 :hints (("Goal" :in-theory (e/d (lookup right-msb-8) ()))))
