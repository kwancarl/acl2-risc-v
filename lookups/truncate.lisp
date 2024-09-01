(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
;(local (include-book "ihs/basic-definitions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;(local (include-book "centaur/bitops/fast-logext" :dir :system))
;(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/logops-lemmas" :dir :system))


;; MATERIALIZE SUBTABLES FOR "AND"

(include-book "subtable")


(define truncate-indices (x-hi mask)
 :enabled t
 :returns (lst alistp)
 :measure (acl2-count x-hi)
 (if (not (natp x-hi))
     nil
     (if (zerop x-hi)
         (cons (cons x-hi mask) nil)
         (cons (cons x-hi mask) 
               (truncate-indices (1- x-hi) mask)))))

(defthm truncate-indices-correctness
 (implies (and (natp x-hi) 
               (natp i) 
               (<= i x-hi))
          (member (cons i mask) (truncate-indices x-hi mask))))

(defun materialize-truncate-subtable (idx-lst)
 (b* (((unless (alistp idx-lst))     nil)
      ((if (atom idx-lst))           nil)
      ((cons idx rst)            idx-lst)
      ((unless (consp idx))          nil)
      ((cons x mask)                 idx))
     (cons (cons idx (logand x mask))
           (materialize-truncate-subtable rst))))

(defthm alistp-of-materialize-truncate-subtable
 (alistp (materialize-truncate-subtable idx-lst)))

(defthm member-idx-lst-assoc-materialize-truncate-subtable
 (implies (and (alistp idx-lst) (member idx idx-lst))
          (assoc idx (materialize-truncate-subtable idx-lst))))

(defthm assoc-member-truncate-subtable
 (implies (assoc (cons i mask) (materialize-truncate-subtable idx-lst))
          (member (cons i mask) idx-lst)))

(defthm assoc-truncate-subtable
 (implies (assoc (cons i mask) (materialize-truncate-subtable idx-lst))
          (equal (assoc (cons i mask) (materialize-truncate-subtable idx-lst))
                 (cons (cons i mask) (logand i mask)))))

(defthm truncate-subtable-correctness
 (implies (and (natp x-hi) 
               (natp i) 
        ;       (natp mask) 
               (<= i x-hi))
          (b* ((indices  (truncate-indices x-hi mask))
               (subtable (materialize-truncate-subtable indices)))
              (equal (assoc-equal (cons i mask) subtable)
                     (cons (cons i mask) (logand i mask))))))
                 
(defthm lookup-truncate-subtable-correctness
 (implies (and (natp x-hi) 
               (natp i) 
               (<= i x-hi))
          (b* ((indices  (truncate-indices x-hi mask))
               (subtable (materialize-truncate-subtable indices)))
              (equal (lookup i mask subtable)
                     (logand i mask))))
 :hints (("Goal" :in-theory (enable lookup))))
                 

      

;;;;;;;;;;;;;;;
;;           ;;
;;    TruncateOverflow    ;;
;;           ;;
;;;;;;;;;;;;;;;

;; EVALUATE MLE and CORRECTNESS OF LOOKUP

(define truncate-overflow ((x :type unsigned-byte) (size natp))
 :verify-guards nil
 :returns (smaller acl2-numberp)
 :measure (acl2-count size)
 (if (not (and (natp x) (posp size)))
     0
     (+ (logcar x)
        (* 2 (truncate-overflow (logcdr x) (1- size))))))
(verify-guards truncate-overflow)
  
;; EQUIVALENCE THEOREMS FOR TRUNCATE-OVERFLOW

;; EQUIVALANCE TO LOGAND
(gl::def-gl-thm truncate-overflow-8-logand-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 8) (logand x #xff))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-8-logand-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 8) (logand x #xff))
 :g-bindings (gl::auto-bindings (:nat x 64)))


(gl::def-gl-thm truncate-overflow-16-logand-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 16) (logand x #xffff))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-16-logand-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 16) (logand x #xffff))
 :g-bindings (gl::auto-bindings (:nat x 64)))

;; EQUIVALANCE TO MOD
(gl::def-gl-thm truncate-overflow-8-mod-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 8) (mod x (expt 2 8)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-8-mod-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 8) (mod x (expt 2 8)))
 :g-bindings (gl::auto-bindings (:nat x 64)))

(gl::def-gl-thm truncate-overflow-16-mod-equiv-32-bit-gl
 :hyp   (and (unsigned-byte-p 32 x))
 :concl (equal (truncate-overflow x 16) (mod x (expt 2 16)))
 :g-bindings (gl::auto-bindings (:nat x 32)))

(gl::def-gl-thm truncate-overflow-16-mod-equiv-64-bit-gl
 :hyp   (and (unsigned-byte-p 64 x))
 :concl (equal (truncate-overflow x 16) (mod x (expt 2 16)))
 :g-bindings (gl::auto-bindings (:nat x 64)))

